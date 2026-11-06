"""SEC1 key and ECDH test oracle. No host crypto is used by the runtime."""
import struct
import json
from pathlib import Path
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat
from check import CURVES, guarded


def key_cases(curve, kind):
    p, n = CURVES[curve]
    cv = ec.SECP256R1() if curve == 'p256' else ec.SECP256K1()
    fmt = PublicFormat.UncompressedPoint if curve == 'p256' else PublicFormat.CompressedPoint
    tests = []
    for i, d in enumerate([1, 2, n-1, 0, n]):
        align = 3
        secret = [0xa5]*(8+align)+list(d.to_bytes(32, 'big'))+[0x5a]*8
        peer = ec.derive_private_key(7, cv).public_key()
        peer_bytes = peer.public_bytes(Encoding.X962, fmt)
        size = (65 if curve == 'p256' else 33) if kind == 'public' else 32
        out = bytes([0xcc]*size)
        expected = out
        if 0 < d < n:
            private = ec.derive_private_key(d, cv)
            expected = private.public_key().public_bytes(Encoding.X962, fmt) if kind == 'public' else private.exchange(ec.ECDH(), peer)
        descriptor = struct.pack('<13Q', 0x200008+align, 32, 0x210080, len(peer_bytes), 0, 0, 0, 0,
                                 0x220008+align, size, 0x230008, 2064, 0x240008)
        meta = bytearray([0xa5]*512)
        meta[8:8+104] = descriptor
        meta[128:128+len(peer_bytes)] = peer_bytes
        regions = [secret, list(meta), [0xa5]*(8+align)+list(out)+[0x5a]*8,
                   guarded(bytes([0xcc]*2064)), guarded(b''), [0x69]*4112]
        tests.append(dict(label=f'scalar-{i}', regions=regions, args=[0x210008], expected=list(expected),
            outputRegion=2, outputOffset=8+align, status=0 if 0 < d < n else 8,
            wipeRegion=3, wipeLength=2064, stackDepth=1440, traceGroup='fixed' if i in (0,1,3) else ''))
    if curve == 'p256' and kind == 'ecdh':
        from sign_cases import fixture
        for record in json.loads((Path(__file__).parent/'nist-ecdh.json').read_text())['tests']:
            q = bytes.fromhex('04'+record['QsCAVSx']+record['QsCAVSy'])
            d = int(record['dsIUT'], 16)
            shared = bytes.fromhex(record['Z'])
            private = ec.derive_private_key(d, cv)
            assert private.exchange(ec.ECDH(), ec.EllipticCurvePublicKey.from_encoded_point(cv,q)) == shared
            tests.append(fixture(f'nist-cavs-{record["COUNT"]}',d,q,bytes(32),b'',bytes([0xcc]*32),shared))
        # Reciprocal ECDH agreement, using the opposite caller's private scalar.
        q = ec.derive_private_key(2, cv).public_key().public_bytes(Encoding.X962, fmt)
        private = ec.derive_private_key(7, cv)
        shared = private.exchange(ec.ECDH(),ec.EllipticCurvePublicKey.from_encoded_point(cv,q))
        tests.append(fixture('reciprocal-agreement',7,q,bytes(32),b'',bytes([0xcc]*32),shared))
    return tests
