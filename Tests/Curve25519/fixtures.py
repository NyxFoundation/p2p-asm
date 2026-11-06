"""Public RFC vectors and test-only cryptography oracle. No runtime dependency."""
from dataclasses import dataclass, replace
import random
from wycheproof import ED, X
from cryptography.hazmat.primitives.asymmetric import x25519, ed25519

P = 2**255-19
L = 2**252+27742317777372353535851937790883648493


@dataclass(frozen=True)
class Case:
    name: str
    a: bytes
    b: bytes = b''
    status: int = 0
    trace: bool = False
    capacity: int = 896
    output_capacity: int = 32
    declared_a: int | None = None
    declared_b: int | None = None
    bad_range: str = ''
    published: bytes = b''
    signature: bytes = b''


def oracle(kind, c):
    if kind.startswith('ed'):
        if kind == 'edverify':
            ed25519.Ed25519PublicKey.from_public_bytes(c.a).verify(c.signature,c.b)
            return b''
        private = ed25519.Ed25519PrivateKey.from_private_bytes(c.a)
        return private.sign(c.b) if kind == 'edsign' else private.public_key().public_bytes_raw()
    private = x25519.X25519PrivateKey.from_private_bytes(c.a)
    if kind == 'xpublic':
        return private.public_key().public_bytes_raw()
    try:
        return private.exchange(x25519.X25519PublicKey.from_public_bytes(c.b))
    except ValueError:
        if kind == 'xraw':
            return bytes(32)
        raise


def cases(kind):
    if kind.startswith("ed"):
        return ed_cases(kind)
    alice = bytes.fromhex('77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a')
    bob = bytes.fromhex('5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb')
    ap = bytes.fromhex('8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a')
    bp = bytes.fromhex('de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f')
    shared = bytes.fromhex('4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742')
    rng = random.Random(7748)
    if kind == 'xpublic':
        result = [Case('RFC7748-Alice', alice, published=ap, trace=True),
                  Case('RFC7748-Bob', bob, published=bp)]
    else:
        result = [Case('RFC7748-Alice-Bob', alice, bp, published=shared, trace=True),
                  Case('RFC7748-Bob-Alice', bob, ap, published=shared),
                  Case('RFC7748-iteration-1', (9).to_bytes(32,'little'), (9).to_bytes(32,'little'),
                       published=bytes.fromhex('422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079'))]
        result += [Case(f'noncanonical-{n}', alice, n.to_bytes(32,'little'))
                   for n in (9+2**255, P+9, P+18)]
        for n in (0,1,P-1,P,P+1,2**255,2**255+1):
            result.append(Case(f'low-order-{n}', alice, n.to_bytes(32,'little'),
                               status=9 if kind == 'xshared' else 0, trace=n == 0))
    result += [Case(f'random-{i}', rng.randbytes(32), rng.randbytes(32)) for i in range(4)]
    if kind != 'xpublic':
        iteration1=bytes.fromhex('422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079')
        result.append(Case('RFC7748-iteration-2',iteration1,(9).to_bytes(32,'little')))
    sample = Case('sample', alice, bp)
    result += [replace(sample, name='short-key', a=alice[:31], status=8),
               replace(sample, name='long-key', a=alice+b'x', status=8),
               replace(sample, name='work-capacity', capacity=895, status=5),
               replace(sample, name='output-capacity', output_capacity=31, status=5)]
    if kind != 'xpublic':
        result += [replace(sample, name='short-peer', b=bp[:31], status=8),
                   replace(sample, name='long-peer', b=bp+b'x', status=8)]
    for which in ('input', 'output', 'work', 'alignment', 'overlap'):
        result.append(replace(sample, name=which, bad_range=which, status=4))
    if kind != 'xpublic':
        result += [Case(f'Wycheproof-{i}',bytes.fromhex(a),bytes.fromhex(b),
            status=9 if kind=='xshared' and int(r,16)==0 else 0,
            published=bytes.fromhex(r) if int(r,16)!=0 or kind=='xraw' else b'')
            for i,a,b,r in X]
    return [replace(c,trace=True) if c.status else c for c in result]


def ed_cases(kind):
    seeds = ['9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60',
             '4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb',
             'c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7']
    keys = ['d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a',
            '3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c',
            'fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025']
    signatures = [
      'e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b',
      '92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00',
      '6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a']
    result=[]
    for i,(seed,key,sig,msg) in enumerate(zip(seeds,keys,signatures,['','72','af82'])):
        result.append(Case(f'RFC8032-{i+1}',bytes.fromhex(key if kind=='edverify' else seed),
            bytes.fromhex(msg) if kind!='edpublic' else b'',capacity=4160+len(bytes.fromhex(msg)),
            output_capacity=32 if kind=='edpublic' else 64,
            published=bytes.fromhex(sig if kind=='edsign' else key) if kind!='edverify' else b'',
            signature=bytes.fromhex(sig),trace=i==0 and kind!='edverify'))
    rng=random.Random(8032)
    for n in ([0,32] if kind=='edpublic' else [0,1,63,64,111,112,127,128,129,4097]):
        seed=rng.randbytes(32)
        msg=b'' if kind=='edpublic' else rng.randbytes(n)
        private=ed25519.Ed25519PrivateKey.from_private_bytes(seed)
        result.append(Case(f'message-{n}',private.public_key().public_bytes_raw() if kind=='edverify' else seed,
            msg,capacity=4160+len(msg),output_capacity=32 if kind=='edpublic' else 64,
            signature=private.sign(msg),trace=n==112 and kind!='edverify'))
    sample=result[0]
    result += [replace(sample,name='short-key',a=sample.a[:31],status=8,trace=True),
               replace(sample,name='work-capacity',capacity=4159,status=5,trace=True),
               replace(sample,name='length-overflow',declared_b=2**64-4160,status=1,trace=True)]
    if kind=='edpublic': result.pop()  # keygen has no message-length argument
    if kind=='edverify':
        result += [replace(sample,name='short-signature',signature=sample.signature[:-1],status=8),
                   replace(sample,name='long-signature',signature=sample.signature+b'x',status=8),
                   replace(sample,name='malleable-S-plus-L',signature=sample.signature[:32]+(int.from_bytes(sample.signature[32:],'little')+L).to_bytes(32,'little'),status=10),
                   replace(sample,name='noncanonical-key',a=P.to_bytes(32,'little'),status=10),
                   replace(sample,name='negative-zero-key',a=(1+2**255).to_bytes(32,'little'),status=10),
                   replace(sample,name='identity-key',a=(1).to_bytes(32,'little'),status=11),
                   replace(sample,name='order-four-key',a=bytes(32),status=11),
                   replace(sample,name='identity-R',signature=(1).to_bytes(32,'little')+sample.signature[32:],status=11),
                   replace(sample,name='wrong-message',b=b'x',capacity=4161,status=12)]
        def mixed(encoded):
            word=int.from_bytes(encoded,'little')
            return (P-word%(2**255)+((1-(word>>255))<<255)).to_bytes(32,'little')
        result += [replace(sample,name='mixed-order-key',a=mixed(sample.a),status=11),
                   replace(sample,name='mixed-order-R',signature=mixed(sample.signature[:32])+sample.signature[32:],status=11),
                   replace(sample,name='noncanonical-R',signature=P.to_bytes(32,'little')+sample.signature[32:],status=10)]
    else:
        result.append(replace(sample,name='output-capacity' ,output_capacity=(31 if kind=='edpublic' else 63),status=5,trace=True))
    for which in ('input','output','work','alignment'):
        result.append(replace(sample,name=which,bad_range=which,status=4,trace=True))
    if kind=='edverify':
        result += [Case(f'Wycheproof-{i}',bytes.fromhex(key),bytes.fromhex(msg),
            signature=bytes.fromhex(sig),status=status,capacity=4160+len(bytes.fromhex(msg)),
            output_capacity=64) for i,key,msg,sig,status in ED]
    return result
