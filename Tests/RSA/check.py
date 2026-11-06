#!/usr/bin/env python3
"""Execute typed RV64IM, independent specs, GNU byte equality and both QEMU paths."""
import argparse
import json
import os
import re
import subprocess
import cryptography
from build import compile_probe
from fixtures import positives, emsa_negatives
from negative_cases import preflight_cases, content_cases, unaligned_valid
from official import wycheproof, nist
from supplement import cases as supplements
from native import ROOT, prepare, execute


def audit_proofs():
    subprocess.run(['lake','build','+Tests.RSA.ProofAudit:olean'],cwd=ROOT,check=True,
                   stdout=subprocess.DEVNULL)
    result=subprocess.run(['lake','env','lean','Tests/RSA/ProofAudit.lean'],cwd=ROOT,
                          check=True,capture_output=True,text=True)
    axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',result.stdout)
    assert len(axioms)+result.stdout.count('does not depend on any axioms')==24
    assert all(set(a.replace(',',' ').split()) <= {'propext','Quot.sound','Classical.choice'}
               for a in axioms)
    (ROOT/'build/rsa/proof-audit.txt').write_text(result.stdout)
    print('PASS 24 kernel-checked helper lemmas and axiom audit',flush=True)


def run_group(probe,kind,group,fs,args):
    if args.limit:
        fs=fs[:args.limit]
    directory=ROOT/'build/rsa'/f'{kind}-{group}'
    directory.mkdir(parents=True,exist_ok=True)
    (directory/'cases.json').write_text(json.dumps(fs))
    subprocess.run([str(probe),kind,str(directory)],cwd=ROOT,check=True)
    prepare(args.prefix,directory)
    for i,f in enumerate(fs):
        execute(args.prefix,args.qemu,directory,kind,i,f)
    print(f'PASS {kind}/{group}: {len(fs)} cases, GNU bytes and both QEMU paths',flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qemu', default=os.environ.get('QEMU_RISCV64','qemu-riscv64'))
    parser.add_argument('--prefix', default=os.environ.get('RISCV_PREFIX','riscv64-unknown-elf-'))
    parser.add_argument('--kinds', nargs='+', choices=['pkcs','pss'], default=['pkcs','pss'])
    parser.add_argument('--limit', type=int)
    parser.add_argument('--group', choices=['positive','emsa','errors','official','supplement','all'], default='all')
    args = parser.parse_args()
    if args.limit is not None and args.limit < 1:
        parser.error('--limit must be positive')
    assert cryptography.__version__ == '49.0.0'
    probe = compile_probe()
    audit_proofs()
    for kind in args.kinds:
        valid = positives(kind)
        groups = {'positive': lambda: valid+[unaligned_valid(valid[0])],
                  'emsa': lambda: emsa_negatives(kind),
                  'errors': lambda: preflight_cases(valid[1])+content_cases(valid[0]),
                  'official': lambda: wycheproof(kind)+nist(kind),
                  'supplement': lambda: supplements(kind,valid[0])}
        for group in groups if args.group == 'all' else [args.group]:
            run_group(probe,kind,group,groups[group](),args)


if __name__ == '__main__':
    main()
