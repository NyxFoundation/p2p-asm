"""Test-only Go crypto.Signer/verification bridge into actual fetched RV64 + QEMU.

The production core never imports or invokes this process. Every request gets
its own artifact directory, model footprint check and both native executions.
"""
import json
from pathlib import Path
import struct
import subprocess
import sys
from cryptography import x509
from cryptography.hazmat.primitives.asymmetric import ed25519, ec, rsa
from build import ROOT
from cases import fixture
from native import prepare, execute
from oracle import OID, parse, test_seed


def describe(raw, seed=None):
    cert = x509.load_der_x509_certificate(raw)
    encoded = cert.extensions.get_extension_for_oid(OID).value.value
    public_node = parse(encoded).children(encoded)[0]
    proto = encoded[public_node.body:public_node.end]
    assert proto[0] == 8 and proto[2] == 18 and proto[3] == len(proto) - 4
    kind = proto[1]
    assert kind in (1, 2) and len(proto) == kind + 35
    public = cert.public_key()
    subject_kind = (1 if isinstance(public, ed25519.Ed25519PublicKey) else
                    2 if isinstance(public, ec.EllipticCurvePublicKey) else 3)
    seed = test_seed('unused-counterpart-seed') if seed is None else seed
    return dict(raw=raw, host_kind=kind, subject_kind=subject_kind, host=proto[4:],
                signature_kind=4 if cert.signature_algorithm_oid.dotted_string ==
                '1.2.840.113549.1.1.10' else subject_kind,
                peer=bytes([0, len(proto)]) + proto, seed=seed,
                host_seed=test_seed('unused-counterpart-host'),
                subject=ed25519.Ed25519PrivateKey.from_private_bytes(seed))


def run_request(request_path):
    request = json.loads(Path(request_path).read_text())
    directory = Path(request_path).resolve().parent / (Path(request_path).stem + '-artifacts')
    directory.mkdir(parents=True, exist_ok=True)
    raw = bytes.fromhex(request['der'])
    value = describe(raw, bytes.fromhex(request['seed']) if 'seed' in request else None)
    kind, role = request['operation'], request['role']
    digest = bytes.fromhex(request.get('digest', '00' * 32))
    signature = bytes.fromhex(request.get('signature', ''))
    expected = bytes.fromhex(request.get('expected', ''))
    f = fixture(kind, request['label'], value, role=role, digest=digest,
                signature=signature, expected=expected,
                utc_ns=request.get('utcNs', 1800000000000000000))
    (directory / 'cases.json').write_text(json.dumps([f], separators=(',', ':')))
    probe = ROOT / 'build/certificate-auth/lake-probe/.lake/build/bin/certificate-auth-probe'
    with (directory / 'model.log').open('w') as log:
        subprocess.run([str(probe), kind, str(directory)], stdout=log, stderr=log, check=True)
    prefix = request['prefix']
    prepare(prefix, directory)
    execute(prefix, request['qemu'], directory, kind, 0, f)
    snapshot = (directory / 'case-0.after.bin').read_bytes()
    start = 256 + len(f['regions'][0]) + len(f['regions'][1]) + 8
    if kind == 'cv-sign':
        return snapshot[start:start+64].hex()
    if kind == 'auth':
        size = struct.unpack_from('<Q', snapshot, start + 16)[0]
        return snapshot[start+136:start+136+size].hex()
    return ''


if __name__ == '__main__':
    print(run_request(sys.argv[1]))
