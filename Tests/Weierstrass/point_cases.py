"""Exceptional point cases, compared with SEC1 affine group arithmetic."""
from cryptography.hazmat.primitives.asymmetric import ec
from check import CURVES, guarded


def point_cases(curve, kind):
    p, n = CURVES[curve]
    cv = ec.SECP256R1() if curve == 'p256' else ec.SECP256K1()
    g = ec.derive_private_key(1, cv).public_key().public_numbers()
    g2 = ec.derive_private_key(2, cv).public_key().public_numbers()
    affine = lambda q: bytes(64) if q is None else q.x.to_bytes(32, 'big')+q.y.to_bytes(32, 'big')
    def projective(q, z=1):
        coords = (0, 1, 0) if q is None else (q.x*z % p, q.y*z % p, z)
        return b''.join((v*2**256 % p).to_bytes(32, 'little') for v in coords)
    minus = ec.EllipticCurvePublicNumbers(g.x, p-g.y, cv)
    if kind == 'pointadd':
        cases = [('inf-inf', None, None, None, 1), ('inf-G', None, g, g, 1),
                 ('G-inf', g, None, g, 1), ('G-plus-G', g, g, g2, 1),
                 ('G-minus-G', g, minus, None, 1), ('scaled-G-plus-G', g, g, g2, 7)]
        inputs = [(label, projective(a, scale), projective(b), affine(result))
                  for label, a, b, result, scale in cases]
    else:
        inputs = [(f'scalar-{d}', d.to_bytes(32, 'big'), projective(g), affine(result))
                  for d, result in [(0, None), (n, None), (n-1, minus)]]
    return [dict(label=label, regions=[guarded(a), guarded(b), guarded(bytes([0xcc]*64)),
                   guarded(bytes([0xcc]*1024)), guarded(b''), [0x69]*4112],
                 args=[0x200008, 0x210008, 0x220008, 0x230008], expected=list(out),
                 outputRegion=2, outputOffset=8, status=0, wipeRegion=3, wipeLength=1024,
                 stackDepth=1008 if kind == 'pointadd' else 1440, traceGroup='')
            for label, a, b, out in inputs]
