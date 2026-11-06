#!/usr/bin/env python3
"""Independent spec, lowered model, GNU bytes, both QEMU paths and snapshots."""
import argparse
import os
import sys
import json
import hashlib
from concurrent.futures import ThreadPoolExecutor
from build import ROOT, OUT, run, build, audit
from fixtures import cases
from cases import write_case

# Reuse the frozen SHA suite's generic six-region ELF/snapshot driver.
sys.path.append(str(ROOT/'Tests/HashCrypto'))
import native


def suite(args, lean, env, kind, fixtures=None, category=""):
    directory=OUT/category/kind
    directory.mkdir(parents=True,exist_ok=True)
    fixtures=cases(kind) if fixtures is None else fixtures
    if args.limit: fixtures=fixtures[:args.limit]
    for i,c in enumerate(fixtures): write_case(directory/f'case-{i}',kind,c,i)
    (directory/'count.txt').write_text(str(len(fixtures)))
    output=run([lean,kind,str(directory)],env=env)
    print(output,end='',flush=True)
    (directory/'model.txt').write_text(output)
    native.prepare(args.prefix,directory)
    script=native.linker(directory)
    for i,c in enumerate(fixtures):
        path=directory/f'case-{i}'
        expected=(path/'expected.bin').read_bytes()
        assert (path/'after.bin').read_bytes()==expected,(kind,c.name,'oracle mismatch')
        native.execute(args,directory,path,expected,script)
    print(f'PASS {kind}: {len(fixtures)} cases; cryptography, GNU bytes, both QEMU paths',flush=True)
    return {'algorithm':kind,'cases':len(fixtures),'trace_pairs':sum(c.trace for c in fixtures),
            'qemu_executions':2*len(fixtures),
            'code_sha256':hashlib.sha256((directory/'encoded.bin').read_bytes()).hexdigest(),
            'instructions':len((directory/'encoded.bin').read_bytes())//4}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qemu',default=os.environ.get('QEMU_RISCV64','qemu-riscv64'))
    parser.add_argument('--prefix',default='riscv64-unknown-elf-')
    parser.add_argument('--only',choices=('xpublic','xraw','xshared','edpublic','edsign','edverify'))
    parser.add_argument('--limit',type=int)
    parser.add_argument('--jobs',type=int,default=1)
    args=parser.parse_args()
    lean,env=build()
    audit()
    kinds=[args.only] if args.only else ['xpublic','xraw','xshared','edpublic','edsign','edverify']
    with ThreadPoolExecutor(max_workers=max(1,min(6,args.jobs))) as pool:
        reports=list(pool.map(lambda kind:suite(args,lean,env,kind),kinds))
    report_path=OUT/(f'{args.only}-verification.json' if args.only else 'verification.json')
    report_path.write_text(json.dumps(reports,indent=2)+'\n')


if __name__=='__main__': main()
