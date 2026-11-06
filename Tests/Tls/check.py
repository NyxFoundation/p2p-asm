#!/usr/bin/env python3
"""Specs + Python/RFC + actual instruction model + GNU equality + both QEMU paths."""
import argparse
import hashlib
import json
import os
import sys
from dataclasses import replace
from build import ROOT, OUT, build, run
from cases import cases, write_case

sys.path.append(str(ROOT/'Tests/HashCrypto'))
import native


def suite(args, lean, env, kind):
    directory = OUT/(args.label or ('extended-'+kind if args.extended else kind))
    directory.mkdir(parents=True, exist_ok=True)
    if args.extended and kind == 'decode':
        from codec_cases import cases as codec_cases
        fixtures = codec_cases(extended=True)
    else: fixtures = cases(kind)
    if args.match: fixtures = [c for c in fixtures if args.match in c.name]
    if args.limit: fixtures = fixtures[:args.limit]
    for i, case in enumerate(fixtures):
        write_case(directory/f'case-{i}', kind, case, i)
        if args.traces and kind in ('handshake','application','finished','hash','messageHash') and case.status == 0:
            alt = replace(case,a=bytes(v^255 for v in case.a),b=bytes(v^255 for v in case.b))
            write_case(directory/'alternate'/f'case-{i}',kind,alt,i)
    (directory/'count.txt').write_text(str(len(fixtures)))
    output = run([lean, kind, str(directory)], env=env)
    print(output, end='', flush=True)
    (directory/'model.txt').write_text(output)
    native.prepare(args.prefix, directory)
    script = native.linker(directory)
    for i, case in enumerate(fixtures):
        path = directory/f'case-{i}'
        expected = (path/'expected.bin').read_bytes()
        assert (path/'after.bin').read_bytes() == expected, (kind, case.name, 'Python snapshot')
        native.execute(args, directory, path, expected, script)
        alt = directory/'alternate'/f'case-{i}'
        if (alt/'before.bin').exists():
            expected = (alt/'expected.bin').read_bytes()
            assert (alt/'after.bin').read_bytes() == expected
            native.execute(args,directory,alt,expected,script)
    pairs = sum((directory/'alternate'/f'case-{i}'/'before.bin').exists() for i in range(len(fixtures)))
    return {'kind': kind, 'cases': len(fixtures), 'trace_pairs': pairs, 'qemu': 2*(len(fixtures)+pairs),
            'instructions': len((directory/'encoded.bin').read_bytes())//4,
            'sha256': hashlib.sha256((directory/'encoded.bin').read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--qemu', default=os.environ.get('QEMU_RISCV64', 'qemu-riscv64'))
    parser.add_argument('--prefix', default='riscv64-unknown-elf-')
    parser.add_argument('--only', choices=['handshake','application','finished','hash','messageHash','decode','encode','vector','boundary'])
    parser.add_argument('--limit', type=int)
    parser.add_argument('--extended', action='store_true')
    parser.add_argument('--traces', action='store_true')
    parser.add_argument('--match')
    parser.add_argument('--label')
    args = parser.parse_args()
    lean, env = build()
    for kind in [args.only] if args.only else ['handshake','application','finished','hash','messageHash','decode','encode','vector','boundary']:
        summary = suite(args, lean, env, kind)
        (OUT/f'{args.label or (("extended-" if args.extended else "")+kind)}-verification.json').write_text(json.dumps(summary, indent=2)+'\n')
        print(summary, flush=True)


if __name__ == '__main__': main()
