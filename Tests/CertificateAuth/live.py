"""Issue in ASM, exchange real TLS handshakes, authenticate and verify CV in ASM."""
import argparse
import json
from pathlib import Path
import struct
import subprocess
from build import ROOT
from cases import issue_fixture
from oracle import certificate, test_seed, verify_certificate
from native import prepare, execute


def issue_material(kind, prefix, qemu):
    directory = ROOT / 'build/certificate-auth/live' / f'issue-host{kind}'
    directory.mkdir(parents=True, exist_ok=True)
    cert = certificate(host_kind=kind)
    fixture = issue_fixture(cert, f'live-issued-host{kind}')
    (directory / 'cases.json').write_text(json.dumps([fixture], separators=(',', ':')))
    probe = ROOT / 'build/certificate-auth/lake-probe/.lake/build/bin/certificate-auth-probe'
    subprocess.run([str(probe), 'issue', str(directory)], check=True)
    prepare(prefix, directory)
    execute(prefix, qemu, directory, 'issue', 0, fixture)
    data = (directory / 'case-0.after.bin').read_bytes()
    output = 256 + len(fixture['regions'][0]) + len(fixture['regions'][1])
    length = struct.unpack_from('<Q', data, 11 * 8)[0]
    der = data[output+8:output+8+length]
    seed = data[output+520:output+552]
    peer_length = struct.unpack_from('<Q', data, output+560)[0]
    peer = data[output+568:output+568+peer_length]
    assert der == cert['raw'] and seed == cert['seed'] and peer == cert['peer']
    verify_certificate(dict(cert, raw=der))
    return der, seed, peer


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--qemu', required=True)
    parser.add_argument('--prefix', default='riscv64-unknown-elf-')
    args = parser.parse_args()
    for kind in (1, 2):
        der, seed, peer = issue_material(kind, args.prefix, args.qemu)
        for role in (1, 2):
            directory = ROOT / 'build/certificate-auth/live' / f'host{kind}-role{role}'
            directory.mkdir(parents=True, exist_ok=True)
            request = dict(DER=der.hex(), Seed=seed.hex(), Peer=peer.hex(),
                           HostSeed=test_seed(f'real-go-counterpart-{3-kind}').hex(),
                           HostKind=3-kind, Role=role, Directory=str(directory),
                           Bridge=str(ROOT / 'Tests/CertificateAuth/bridge.py'),
                           Prefix=args.prefix, Qemu=args.qemu)
            path = directory / 'input.json'
            path.write_text(json.dumps(request, indent=2))
            subprocess.run([str(ROOT / 'build/certificate-auth/go-counterpart'), str(path)], check=True)
            print(f'PASS live TLS: ASM host{kind}, role{role}, Go host{3-kind}', flush=True)


if __name__ == '__main__':
    main()
