#!/usr/bin/env python3
"""Run with python3 Tests/Aead/check.py; no production crypto dependencies."""

import argparse
import json
import os
import re

import cryptography
from fixtures import aes_cases, gcm_cases
from native import ROOT, execute, prepare, run


def audit_proofs():
    report = run(['lake', 'env', 'lean', 'Tests/Aead/ProofAudit.lean'])
    axioms = re.findall(r'depends on axioms:\s*\[([^]]*)\]', report)
    axioms += [''] * report.count('does not depend on any axioms')
    assert len(axioms) == 10, 'all AEAD lemmas must be audited'
    for names in axioms:
        used = {name.strip() for name in names.split(',') if name.strip()}
        assert used <= {'propext', 'Quot.sound', 'Classical.choice'}, used
    directory = ROOT/'build/aead'
    directory.mkdir(parents=True, exist_ok=True)
    (directory/'proof-audit.txt').write_text(report)
    print('PASS kernel proof dependency audit (10 theorems)', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qemu', default=os.environ.get('QEMU_RISCV64', 'qemu-riscv64'))
    parser.add_argument('--prefix', default='riscv64-unknown-elf-')
    parser.add_argument('--kinds', nargs='+', default=['sbox', 'expand', 'aes', 'hp', 'ghash', 'seal', 'open'])
    parser.add_argument('--native-only', action='store_true', help='reuse already verified model snapshots')
    args = parser.parse_args()
    if cryptography.__version__ != '49.0.0':
        raise RuntimeError('Install the pinned test requirements: Tests/Aead/requirements.txt')
    if not args.native_only:
        print(run(['lake', 'build', 'libp2p-asm-aead-probe', 'Tests.Aead.SpecMain', 'Tests.Aead.ProofAudit'], timeout=1800), end='', flush=True)
        audit_proofs()
        print(run(['lake', 'env', 'lean', '--run', 'Tests/Aead/SpecMain.lean']), end='', flush=True)
    all_cases = aes_cases() | gcm_cases()
    for kind in args.kinds:
        if kind not in all_cases:
            raise ValueError('unknown routine')
        directory = ROOT/'build/aead'/kind
        directory.mkdir(parents=True, exist_ok=True)
        cases = all_cases[kind]
        case_file = directory/'cases.json'
        serialized = json.dumps(cases)
        if args.native_only:
            assert json.loads(case_file.read_text()) == cases, 'fixtures changed; rerun model tests'
        else:
            case_file.write_text(serialized)
            print(run([str(ROOT/'.lake/build/bin/libp2p-asm-aead-probe'), kind, str(directory)],
                      timeout=1800), end='', flush=True)
        prepare(args.prefix, directory)
        for i, fixture in enumerate(cases):
            execute(args.prefix, args.qemu, directory, kind, i, fixture)
        print(f'PASS {kind}: {len(cases)} cases, GNU bytes, QEMU assembly and encoded bytes', flush=True)


if __name__ == '__main__':
    main()
