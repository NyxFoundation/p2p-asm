"""Independent Python integer/cryptography oracles; all private keys are TEST ONLY."""
import hashlib
import json
import math
import struct
from pathlib import Path
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import rsa, padding, utils
from cryptography.exceptions import InvalidSignature

HERE = Path(__file__).resolve().parent
PREFIX = bytes.fromhex('3031300d060960864801650304020105000420')
# FIPS 180-4 constants, read from the frozen independent specification at test generation.


def sha_table():
    import re
    text = (HERE.parents[1]/'Libp2pAsm/Spec/Crypto/SHA256.lean').read_text()
    values = re.findall(r'0x[0-9a-f]+', text.split('def roundConstants')[1].split('def bigSigma0')[0])
    assert len(values) == 64
    return b''.join(struct.pack('<Q', int(x, 16)) for x in values)


def be(n, width=None):
    return n.to_bytes(width or max(1, (n.bit_length()+7)//8), 'big')


def bound(k, e):
    l = (k+3)//4
    return 64*(l+1)**2*(16*e+4)+4096*l*l+50000*((k+31)//32+2)+1000*k+100000


def guard(data):
    return [0xa5]*8+list(data)+[0x5a]*8


def fixture(label, n, e, digest, sig, status=0, content=True, spec=True, raw_n=None, raw_e=None):
    nb, eb = be(n) if raw_n is None else raw_n, be(e) if raw_e is None else raw_e
    k = len(nb)
    work = 56*((k+3)//4)+896
    data = eb+sig+digest
    fields = [0x200008,k,0x210008,len(eb),0x210008+len(eb),len(sig),
              0x210008+len(eb)+len(sig),len(digest),0x230008,work,0x240008,
              65536,65536,2048,bound(k,len(eb)),288]
    regions = [guard(nb),guard(data),guard(struct.pack('<16Q',*fields)),
               guard(bytes([0xcc])*work),guard(sha_table()),[0x69]*4112]
    return dict(label=label,regions=regions,args=[0x220008],status=status,stack=0x251000,workOffset=8,
                wipeLength=work if content else 0,stackDepth=288 if content else 0,
                checkSpec=spec,n=list(nb),e=list(eb),digest=list(digest),signature=list(sig))


def test_key(bits,e):
    if bits%2 == 0:
        key=rsa.generate_private_key(e,bits).private_numbers()
        p,q=key.p,key.q
    else:
        # Some backends round odd key_size down. Build exact test-only factors.
        p=rsa.generate_private_key(e,bits-1).private_numbers().p
        q=rsa.generate_private_key(e,bits+1).private_numbers().p
    n=p*q
    assert n.bit_length()==bits
    return dict(bits=bits,e=e,n=str(n),d=str(pow(e,-1,(p-1)*(q-1))),p=str(p),q=str(q))


def generated_keys():
    path = HERE/'generated-test-keys.json'
    if path.exists():
        keys=json.loads(path.read_text())
        assert all(int(k['n']).bit_length()==k['bits'] for k in keys)
        return keys
    keys = []
    for bits, e in [(2048,3),(2048,65537),(3072,65537),(4096,65537),
                    (2049,65537),(2055,65537),(2056,65537)]:
        keys.append(test_key(bits,e))
    source = keys[1]
    phi = (int(source['p'])-1)*(int(source['q'])-1)
    e = 2**65+3
    while math.gcd(e,phi) != 1:
        e += 2
    keys.append(dict(source,e=e,d=str(pow(e,-1,phi))))
    path.write_text(json.dumps(keys,indent=2)+'\n')
    return keys


def mgf(seed, length):
    return b''.join(hashlib.sha256(seed+i.to_bytes(4,'big')).digest()
                    for i in range((length+31)//32))[:length]


def pkcs_em(k,digest):
    return b'\x00\x01'+b'\xff'*(k-54)+b'\x00'+PREFIX+digest


def pss_em(n,digest,salt=bytes(range(32)),db_change=None):
    bits = n.bit_length()-1
    length = (bits+7)//8
    h = hashlib.sha256(bytes(8)+digest+salt).digest()
    db = bytes(length-len(salt)-34)+b'\x01'+salt
    if db_change:
        db = db_change(db)
    masked = bytes(a^b for a,b in zip(db,mgf(h,len(db))))
    masked = bytes([masked[0] & (255 >> (8*length-bits))])+masked[1:]
    return masked+h+b'\xbc'


def verify_crypto(n,e,digest,sig,kind):
    try:
        rsa.RSAPublicNumbers(e,n).public_key().verify(sig,digest,
            padding.PKCS1v15() if kind == 'pkcs' else
            padding.PSS(mgf=padding.MGF1(hashes.SHA256()),salt_length=32),
            utils.Prehashed(hashes.SHA256()))
        return True
    except InvalidSignature:
        return False


def signed_case(key, kind, em, label, digest, valid):
    n,e,d = int(key['n']),key['e'],int(key['d'])
    k = (n.bit_length()+7)//8
    assert int.from_bytes(em,'big') < n
    sig = be(pow(int.from_bytes(em,'big'),d,n),k)
    assert pow(int.from_bytes(sig,'big'),e,n) == int.from_bytes(em,'big')
    assert verify_crypto(n,e,digest,sig,kind) == valid, label
    return fixture(label,n,e,digest,sig,0 if valid else 2)


def positives(kind):
    digest = hashlib.sha256(b'RSA public TLS verification test').digest()
    out = []
    for key in generated_keys():
        n = int(key['n'])
        k = (n.bit_length()+7)//8
        em = pkcs_em(k,digest) if kind == 'pkcs' else pss_em(n,digest)
        out.append(signed_case(key,kind,em,f"generated-{key['bits']}-e{key['e']}",digest,True))
    return out


def emsa_negatives(kind):
    key = generated_keys()[0]
    n,k = int(key['n']),256
    digest = hashlib.sha256(b'exact EMSA rejection').digest()
    em = pkcs_em(k,digest) if kind == 'pkcs' else pss_em(n,digest)
    mutations = []
    if kind == 'pkcs':
        for offset,label in [(0,'first'),(1,'block-type'),(2,'ff-first'),(k-53,'ff-last'),
                              (k-52,'delimiter'),(k-51,'sequence'),(k-50,'length'),
                              (k-36,'null-tag'),(k-35,'null-length'),(k-33,'octet-length'),
                              (k-32,'digest-first'),(k-1,'digest-last')]:
            b = bytearray(em)
            b[offset] ^= 1
            mutations.append((label,bytes(b)))
        mutations += [('seven-ff',b'\x00\x01'+b'\xff'*7+b'\x00'+bytes(k-61)+PREFIX+digest),
                      ('missing-null',em[:-51]+PREFIX[:15]+PREFIX[17:]+digest+b'\x00\x00')]
    else:
        for length in [0,20,31,33,40]:
            mutations.append((f'salt-{length}',pss_em(n,digest,bytes(range(length)))))
        mutations += [('delimiter-zero',pss_em(n,digest,db_change=lambda db:db[:-33]+b'\x00'+db[-32:])),
                      ('delimiter-two',pss_em(n,digest,db_change=lambda db:db[:-33]+b'\x02'+db[-32:])),
                      ('ps-nonzero',pss_em(n,digest,db_change=lambda db:db[:1]+b'\x01'+db[2:]))]
        for offset,label in [(k-1,'trailer'),(k-33,'hash-first'),(k-2,'hash-last')]:
            b = bytearray(em); b[offset] ^= 1
            mutations.append((label,bytes(b)))
        b = b'\x80'+bytes(k-2)+b'\xbc'
        assert int.from_bytes(b,'big') < n
        mutations.append(('unused-top-bit',b))
    return [signed_case(key,kind,b,label,digest,False) for label,b in mutations]
