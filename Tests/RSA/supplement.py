"""Additional edge cases kept separate from long-running fixture groups."""
import hashlib
from fixtures import fixture, be, generated_keys, pss_em, signed_case
from official import rfc8448
from negative_cases import unaligned_valid, mutate


def cases(kind, valid):
    out=rfc8448(kind)+[unaligned_valid(valid)]
    for i,label in [(0,'modulus'),(2,'exponent'),(4,'signature'),(6,'digest')]:
        out.append(mutate(valid,f'reverse-overlap-{label}',i,0x230010,4))
    out.append(mutate(valid,'work-inside-modulus',8,0x200010,4))
    n=2**2048-1
    digest=hashlib.sha256(b'maximum Montgomery carries').digest()
    for s,label in [(0,'zero'),(1,'one'),(n-1,'all-limbs-max')]:
        out.append(fixture(f'carry-boundary-{label}',n,3,digest,be(s,256),2))
    if kind=='pss':
        key=generated_keys()[4]
        n=int(key['n'])
        em=next(em for i in range(256)
                if int.from_bytes(em:=pss_em(n,digest,hashlib.sha256(be(i)).digest()),'big')
                < n-2**2048)
        # A 2049-bit modulus has k=257 but emLen=256. Never truncate this 1.
        out.append(signed_case(key,kind,b'\x01'+em,'short-em-nonzero-leading-byte',digest,False))
        key=generated_keys()[5]
        n=int(key['n'])
        # 2055 bits means two unused high EM bits; set the lower forbidden bit.
        em=b'\x40'+bytes(255)+b'\xbc'
        out.append(signed_case(key,kind,em,'two-unused-bits',digest,False))
    return out
