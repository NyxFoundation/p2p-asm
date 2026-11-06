import argparse
import json
import os
import subprocess
from build import compile_probe, ROOT
from cases import smoke


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--kind', choices=['auth', 'cv-verify', 'cv-sign', 'issue'])
    parser.add_argument('--native', action='store_true')
    parser.add_argument('--no-build', action='store_true')
    parser.add_argument('--matrix', action='store_true')
    parser.add_argument('--prefix', default=os.environ.get('RISCV_PREFIX', 'riscv64-unknown-elf-'))
    parser.add_argument('--qemu', default=os.environ.get('QEMU_RISCV64', 'qemu-riscv64'))
    args = parser.parse_args()
    probe = (ROOT / 'build/certificate-auth/lake-probe/.lake/build/bin/certificate-auth-probe'
             if args.no_build else compile_probe())
    from matrix import suites
    for kind, fixtures in (suites() if args.matrix else smoke()).items():
        if args.kind and args.kind != kind:
            continue
        directory = ROOT / 'build/certificate-auth' / ('matrix' if args.matrix else 'smoke') / kind
        directory.mkdir(parents=True, exist_ok=True)
        (directory / 'cases.json').write_text(json.dumps(fixtures, separators=(',', ':')))
        subprocess.run([str(probe), kind, str(directory)], check=True)
        if args.native:
            from native import prepare, execute
            prepare(args.prefix, directory)
            for idx, fixture in enumerate(fixtures):
                execute(args.prefix, args.qemu, directory, kind, idx, fixture)
            print(f'PASS {kind}: GNU bytes and both QEMU paths ({len(fixtures)} cases)', flush=True)


if __name__ == '__main__':
    main()
