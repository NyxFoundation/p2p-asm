#!/usr/bin/env python3
"""Additional ABI rejection cases and a canonical but off-curve Ed25519 point."""
import argparse
import json
import os
from dataclasses import replace
from build import OUT,build
from fixtures import cases
from check import suite


def negatives(kind):
    sample=cases(kind)[0]
    result=[replace(sample,name='long-key',a=sample.a+b'x',status=8,trace=True)]
    ranges=['work-input-overlap','stack-work-overlap','stack-underflow','stack-alignment']
    if kind!='edverify': ranges += ['overlap','output-work-overlap']
    if kind in ('xraw','xshared'): ranges += ['second']
    for which in ranges:
        result.append(replace(sample,name=which,bad_range=which,status=4,trace=True))
    if kind in ('edsign','edverify'):
        result.append(replace(sample,name='message-range',b=b'xx',capacity=4162,
                              bad_range='second',status=4,trace=True))
    if kind=='edverify':
        result.append(replace(sample,name='off-curve-y-two',a=(2).to_bytes(32,'little'),
                              status=10,trace=False))
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qemu',default=os.environ.get('QEMU_RISCV64','qemu-riscv64'))
    parser.add_argument('--prefix',default='riscv64-unknown-elf-')
    args=parser.parse_args()
    args.limit=None
    executable,env=build()
    reports=[suite(args,executable,env,k,negatives(k),'adversarial')
             for k in ['xpublic','xraw','xshared','edpublic','edsign','edverify']]
    (OUT/'adversarial-verification.json').write_text(json.dumps(reports,indent=2)+'\n')


if __name__=='__main__': main()
