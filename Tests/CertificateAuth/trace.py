"""Secret-varying finite instruction/address trace pairs; no CT proof claim."""
import argparse
import json
import subprocess
from cryptography.hazmat.primitives.asymmetric import ed25519
from build import ROOT, compile_probe
from cases import fixture
from oracle import certificate, test_seed
from native import prepare, execute


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--qemu', required=True)
    parser.add_argument('--prefix', default='riscv64-unknown-elf-')
    args = parser.parse_args()
    probe = compile_probe()
    for role in (1, 2):
        cert = certificate()
        other_seed = test_seed('second-ephemeral')
        other = dict(cert, seed=other_seed, subject=ed25519.Ed25519PrivateKey.from_private_bytes(other_seed))
        fixtures = [fixture('cv-sign', f'role{role}-seed{i}', value, role=role,
                            signature=b'', expected=b'') for i,value in enumerate([cert,other])]
        assert fixtures[0]['regions'][0] == fixtures[1]['regions'][0]
        assert fixtures[0]['regions'][1][40:] == fixtures[1]['regions'][1][40:]
        directory = ROOT / 'build/certificate-auth/trace' / f'role{role}'
        directory.mkdir(parents=True, exist_ok=True)
        (directory / 'cases.json').write_text(json.dumps(fixtures,separators=(',', ':')))
        subprocess.run([str(probe),'trace','cv-sign',str(directory)],check=True)
        prepare(args.prefix,directory)
        for i,value in enumerate(fixtures):
            execute(args.prefix,args.qemu,directory,'cv-sign',i,value)


if __name__ == '__main__':
    main()
