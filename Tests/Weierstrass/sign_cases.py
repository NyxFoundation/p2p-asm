"""RFC6979/independent OpenSSL oracle and strict DER negative tests."""
import hashlib
import json
import re
import struct
from pathlib import Path
from cryptography.hazmat.primitives.asymmetric import ec, utils
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.serialization import Encoding, PublicFormat
from check import CURVES, guarded
from native import ROOT

RFC_KEY = int('C9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721', 16)
RFC_SAMPLE = ('efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716',
              'f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8')


def fixture(label, d, peer, digest, signature, output, expected, status=0, depth=1440, unaligned=False):
    align = 3
    secret = [0xa5]*11+list(d.to_bytes(32, 'big'))+[0x5a]*8
    meta = bytearray([0xa5]*512)
    po, do, so = (131,261,327) if unaligned else (128,256,320)
    meta[8:112] = struct.pack('<13Q', 0x20000b, 32, 0x210000+po, len(peer),
        0x210000+do, len(digest), 0x210000+so, len(signature), 0x22000b, len(output), 0x230008, 2064, 0x240008)
    meta[po:po+len(peer)] = peer
    meta[do:do+len(digest)] = digest
    meta[so:so+len(signature)] = signature
    text = (ROOT/'Libp2pAsm/Spec/Crypto/SHA256.lean').read_text().split('def roundConstants')[1]
    constants = [int(s, 16) for s in re.findall(r'0x[0-9a-f]+', text.split('#v[')[1].split(']')[0])]
    table = struct.pack('<64Q', *constants)
    regions = [secret, list(meta), [0xa5]*11+list(output)+[0x5a]*8,
               guarded(bytes([0xcc]*2064)), guarded(table), [0x69]*4112]
    return dict(label=label, regions=regions, args=[0x210008], expected=list(expected),
        outputRegion=2, outputOffset=11, status=status, wipeRegion=3,
        wipeLength=2064 if depth else 0, stackDepth=depth, traceGroup='')


def known(curve, d, digest):
    cv = ec.SECP256R1() if curve == 'p256' else ec.SECP256K1()
    key = ec.derive_private_key(d, cv)
    fmt = PublicFormat.UncompressedPoint if curve == 'p256' else PublicFormat.CompressedPoint
    peer = key.public_key().public_bytes(Encoding.X962, fmt)
    sig = key.sign(digest, ec.ECDSA(utils.Prehashed(hashes.SHA256()), deterministic_signing=True))
    r, s = utils.decode_dss_signature(sig)
    if curve == 'k256':
        s = min(s, CURVES[curve][1]-s)
    return peer, utils.encode_dss_signature(r, s)


def sign_cases(curve, kind):
    cases = []
    values = [('rfc-sample', RFC_KEY, hashlib.sha256(b'sample').digest()),
              ('rfc-test', RFC_KEY, hashlib.sha256(b'test').digest()),
              ('digest-reduction', 2, bytes([255]*32)), ('invalid-d', 0, bytes(32))]
    for label, d, digest in values:
        peer, sig = known(curve, d or 1, digest)
        r, s = utils.decode_dss_signature(sig)
        if curve == 'p256' and label == 'rfc-sample':
            assert (r, s) == tuple(int(x, 16) for x in RFC_SAMPLE)
        if kind == 'signcompact':
            result = r.to_bytes(32, 'big')+s.to_bytes(32, 'big')
        else:
            result = len(sig).to_bytes(8, 'little')+sig+bytes(72-len(sig))
        output = bytes([0xcc]*len(result))
        cases.append(fixture(label, d, peer, digest, b'', output, result if d else output, 0 if d else 8))
    cases[0]['traceGroup'] = 'secret-constant'
    cases[-1]['traceGroup'] = 'secret-constant'
    return cases


def verify_cases(curve, kind):
    if kind == 'verifyzero':
        digest = bytes(32)
        peer, sig = known(curve, 1, digest)
        return [fixture('zero-digest-infinity-term-unaligned',1,peer,digest,sig,b'',b'',unaligned=True)]
    digest = hashlib.sha256(b'sample').digest()
    peer, sig = known(curve, RFC_KEY, digest)
    n = CURVES[curve][1]
    r, s = utils.decode_dss_signature(sig)
    entries = [('known', sig, 0, 1440), ('malleated', utils.encode_dss_signature(r, n-s), 0, 1440),
        ('zero-r', utils.encode_dss_signature(0, s), 6, 112),
        ('order-r', utils.encode_dss_signature(n, s), 6, 112),
        ('zero-s', utils.encode_dss_signature(r, 0), 6, 112),
        ('order-s', utils.encode_dss_signature(r, n), 6, 112)]
    if kind == 'verifylow':
        entries = [(label, sg, 6 if utils.decode_dss_signature(sg)[1] > n//2 else status,
                    112 if utils.decode_dss_signature(sg)[1] > n//2 else depth)
                   for label, sg, status, depth in entries]
    cases = []
    for label, sg, status, depth in entries:
        if kind == 'verifycompact':
            a, b = utils.decode_dss_signature(sg)
            sg = a.to_bytes(32, 'big')+b.to_bytes(32, 'big')
        cases.append(fixture(label, 1, peer, digest, sg, b'', b'', status, depth))
    if kind != 'verify':
        return cases
    data = json.loads((Path(__file__).parent/f'wycheproof-{curve}.json').read_text())
    for t in data['tests']:
        pub = bytes.fromhex(t['publicKey']['uncompressed'])
        if curve == 'k256':
            pub = bytes([2+(pub[-1]&1)])+pub[1:33]
        sg = bytes.fromhex(t['sig'])
        status, depth = 6, 1440
        if not 8 <= len(sg) <= 72:
            status, depth = 1, 0
        else:
            try:
                a, b = utils.decode_dss_signature(sg)
                if not (0 < a < n and 0 < b < n):
                    depth = 112
            except ValueError:
                depth = 112
        cases.append(fixture(f'wycheproof-{t["tcId"]}', 1, pub,
            hashlib.sha256(bytes.fromhex(t['msg'])).digest(), sg, b'', b'', status, depth))
    return cases
