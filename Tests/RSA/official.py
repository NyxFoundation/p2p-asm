"""Pinned, public Wycheproof and NIST records with explicit TLS policy."""
import hashlib
import json
from fixtures import HERE, fixture, verify_crypto


def wycheproof(kind):
    data = json.loads((HERE/f'wycheproof-{kind}.json').read_text())
    out = []
    for group in data['testGroups']:
        n=int(group['publicKey']['modulus'],16)
        e=int(group['publicKey']['publicExponent'],16)
        for t in group['tests']:
            digest=hashlib.sha256(bytes.fromhex(t['msg'])).digest()
            sig=bytes.fromhex(t['sig'])
            valid=t['result']=='valid'
            # The selected acceptable missing-NULL vector is deliberately rejected.
            if t['result'] != 'acceptable':
                assert verify_crypto(n,e,digest,sig,kind)==valid
            out.append(fixture(f"wycheproof-{t['tcId']}",n,e,digest,sig,0 if valid else 2,
                               content=len(sig)==(n.bit_length()+7)//8))
    return out


def nist(kind):
    data=json.loads((HERE/'nist.json').read_text())
    out=[]
    for t in data['records']:
        if t['kind'] != kind: continue
        n,e=int(t['n'],16),int(t['e'],16)
        digest=hashlib.sha256(bytes.fromhex(t['Msg'])).digest()
        sig=bytes.fromhex(t['S'])
        assert verify_crypto(n,e,digest,sig,kind) == t['valid']
        out.append(fixture(t['label'],n,e,digest,sig,0 if t['valid'] else 2))
    return out


def rfc8448(kind):
    from cryptography import x509
    data=json.loads((HERE/'rfc8448.json').read_text())
    parts={k:bytes.fromhex(v) for k,v in data['handshake'].items()}
    cert=x509.load_der_x509_certificate(parts['Certificate'][11:-2])
    key=cert.public_key().public_numbers()
    transcript=hashlib.sha256(b''.join(parts[k] for k in
        ['ClientHello','ServerHello','EncryptedExtensions','Certificate'])).digest()
    assert transcript.hex()==data['transcriptHash']
    digest=(hashlib.sha256(cert.tbs_certificate_bytes).digest() if kind=='pkcs' else
            hashlib.sha256(b' '*64+b'TLS 1.3, server CertificateVerify\x00'+transcript).digest())
    sig=cert.signature if kind=='pkcs' else parts['CertificateVerify'][8:]
    assert verify_crypto(key.n,key.e,digest,sig,kind)
    return [fixture('rfc8448-valid-but-below-profile',key.n,key.e,digest,sig,6)]
