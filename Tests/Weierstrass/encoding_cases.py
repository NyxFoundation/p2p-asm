"""Length/sign-bit/strict DER boundary cases, no costly curve operation."""
import copy
import hashlib
import hmac
import struct
from cryptography.hazmat.primitives.asymmetric import utils
from check import CURVES, guarded
from sign_cases import fixture, sign_cases, RFC_KEY


def encoding_cases(curve, kind):
    n = CURVES[curve][1]
    if kind == 'signnonce':
        out = []
        for msg in [b'sample', b'test']:
            digest = hashlib.sha256(msg).digest()
            k, v = bytes(32), bytes([1]*32)
            seed = RFC_KEY.to_bytes(32, 'big')+(int.from_bytes(digest, 'big') % n).to_bytes(32, 'big')
            for tag in [0, 1]:
                k = hmac.digest(k, v+bytes([tag])+seed, 'sha256')
                v = hmac.digest(k, v, 'sha256')
            candidate = hmac.digest(k, v, 'sha256')
            out.append(fixture('rfc-nonce-'+msg.decode(), RFC_KEY, b'', digest, b'', bytes([0xcc]*32), candidate, depth=400))
        return out
    pairs = [(1,1), (127,128), (128,127), (n-1,n-1)]
    pairs += [(1 << (8*i), 1 << (8*(31-i)+7)) for i in range(32)]
    out = []
    for i, (r,s) in enumerate(pairs):
        sg = utils.encode_dss_signature(r,s)
        if kind == 'encodeder':
            result = len(sg).to_bytes(8, 'little')+sg+bytes(72-len(sg))
            out.append(dict(label=f'width-{i}', regions=[guarded(r.to_bytes(32, 'big')),
                guarded(s.to_bytes(32, 'big')),guarded(bytes([0xcc]*80)),guarded(bytes([0xcc]*1024)),
                guarded(b''),[0x69]*4112], args=[0x200008,0x210008,0x220008,0x230008],
                expected=list(result),outputRegion=2,outputOffset=8,status=0,wipeRegion=3,
                wipeLength=1024,stackDepth=112,traceGroup='fixed' if i < 3 else ''))
        else:
            out.append(fixture(f'width-{i}',1,b'',bytes(32),sg,bytes([0xcc]*64),
                r.to_bytes(32,'big')+s.to_bytes(32,'big'),depth=112))
    if kind == 'parseder':
        sg = utils.encode_dss_signature(1,1)
        bad = [('trailing', sg+b'\x00'), ('negative',bytes.fromhex('3006020180020101')),
            ('overlong-zero', bytes.fromhex('300702020001020101')),
            ('empty-int',bytes.fromhex('3006020002020001')),
            ('wrong-tag', bytes.fromhex('3006030101020101')),
            ('wrong-length',bytes.fromhex('3007020101020101')),
            ('long-length',bytes.fromhex('308106020101020101')),
            ('zero',utils.encode_dss_signature(0,1)),('order',utils.encode_dss_signature(n,1)),
            ('truncated',sg[:-1])]
        for label, sig in bad:
            status,depth = (1,0) if len(sig)<8 else (6,112)
            out.append(fixture(label,1,b'',bytes(32),sig,bytes([0xcc]*64),bytes([0xcc]*64),status,depth))
    return out
