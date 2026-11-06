#!/usr/bin/env python3
"""Spec, independent Python, lowered RV64, full snapshots, GNU and both QEMU paths."""
import argparse
import os
import sys
import hashlib
import json
from build import ROOT,OUT,run,build
from fixtures import cases
from cases import write_case,changed
from oracle import published
from adversarial import cases as adversarial_cases

sys.path.append(str(ROOT/'Tests/HashCrypto'))
import native

def suite(args,lean,env,kind):
    directory=(OUT/'extra' if args.extra else OUT)/kind
    if args.limit: directory=OUT/'subsets'/('extra' if args.extra else 'base')/f'{kind}-{args.limit}'
    directory.mkdir(parents=True,exist_ok=True)
    fixtures=adversarial_cases(kind) if args.extra else cases(kind)
    if args.limit: fixtures=fixtures[:args.limit]
    for i,c in enumerate(fixtures):
        write_case(directory/f'case-{i}',kind,c,i)
        if c.trace: write_case(directory/'alternate'/f'case-{i}',kind,changed(kind,c),i)
    (directory/'count.txt').write_text(str(len(fixtures)))
    output=run([lean,kind,str(directory)],env=env)
    print(output,end='',flush=True); (directory/'model.txt').write_text(output)
    native.prepare(args.prefix,directory); script=native.linker(directory)
    for i,c in enumerate(fixtures):
        for path in [directory/f'case-{i}']+([directory/'alternate'/f'case-{i}'] if c.trace else []):
            expected=(path/'expected.bin').read_bytes()
            assert (path/'after.bin').read_bytes()==expected,(kind,c.name,'Python snapshot')
            native.execute(args,directory,path,expected,script)
    traces=sum(c.trace for c in fixtures)
    print(f'PASS {kind}: {len(fixtures)} cases, {traces} trace pairs, GNU bytes and QEMU',flush=True)
    return {'kind':kind,'cases':len(fixtures),'trace_pairs':traces,'qemu':2*(len(fixtures)+traces),
            'instructions':len((directory/'encoded.bin').read_bytes())//4,
            'sha256':hashlib.sha256((directory/'encoded.bin').read_bytes()).hexdigest()}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--qemu',default=os.environ.get('QEMU_RISCV64','qemu-riscv64'))
    p.add_argument('--prefix',default='riscv64-unknown-elf-')
    p.add_argument('--only',choices=['initial','keys','update','nonce','number','seal','open','retry','retrycheck'])
    p.add_argument('--limit',type=int,default=0)
    p.add_argument('--extra',action='store_true',help='additional boundary and integration fixtures')
    args=p.parse_args()
    if args.limit<0: p.error('--limit must be nonnegative')
    if args.extra and args.only and args.only not in ('seal','open','retry','retrycheck'):
        p.error('--extra supports seal, open, retry and retrycheck')
    published(); lean,env=build()
    kinds=[args.only] if args.only else (['seal','open','retry','retrycheck'] if args.extra else
        ['initial','keys','update','nonce','number','seal','open','retry','retrycheck'])
    results=[suite(args,lean,env,k) for k in kinds]
    name=('extra-' if args.extra else '')+(f'{args.only}-verification.json' if args.only else 'verification.json')
    if args.limit: name=f'subset-{args.limit}-{name}'
    (OUT/name).write_text(json.dumps(results,indent=2)+'\n')
    if args.only and not args.limit:
        full=OUT/('extra-verification.json' if args.extra else 'verification.json')
        previous=json.loads(full.read_text()) if full.exists() else []
        combined={r['kind']:r for r in previous+results}
        full.write_text(json.dumps(list(combined.values()),indent=2)+'\n')

if __name__=='__main__': main()
