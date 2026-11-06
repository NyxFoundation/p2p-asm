#!/usr/bin/env python3
"""Typed RV64 execution, independent integer oracle, GNU bytes and both QEMU paths."""
import argparse
import json
import os
import random
import re
import cryptography
from native import ROOT, run, prepare, execute

CURVES = {
    'p256': (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff,
             0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551),
    'k256': (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f,
             0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141),
}


def guarded(b):
    return [0xa5]*8+list(b)+[0x5a]*8


def arithmetic(curve, kind):
    p, n = CURVES[curve]
    m = n if kind.startswith('q') else p
    rng = random.Random(0x6979)
    values = [(0, 0), (1, 1), (m-1, m-1), (m-1, 1), (2**128-1, 2**192+1)]
    values += [(rng.randrange(m), rng.randrange(m)) for _ in range(8)]
    fixtures = []
    for i, (a, b) in enumerate(values):
        op = kind.removeprefix('q')
        z = {'mul': lambda: a*b*pow(2**256, -1, m) % m,
             'add': lambda: (a+b) % m, 'sub': lambda: (a-b) % m,
             'inv': lambda: pow(a, m-2, m)*pow(2**256, 2, m) % m}[op]()
        regions = [guarded(a.to_bytes(32, 'big')), guarded(b.to_bytes(32, 'big')),
                   guarded(bytes([0xcc]*32)), guarded(bytes([0xcc]*1024)),
                   guarded(b''), [0x69]*4112]
        fixtures.append(dict(label=f'case-{i}', regions=regions,
            args=[0x200008, 0x210008, 0x220008, 0x230008], expected=list(z.to_bytes(32, 'big')),
            outputRegion=2, outputOffset=8, status=0, wipeRegion=3, wipeLength=1024,
            stackDepth=464 if op == 'inv' else 224, traceGroup='fixed' if i < 3 and op != 'inv' else ''))
    return fixtures


def audit_proofs():
    print(run(['lake', 'build', '+Tests.Weierstrass.ProofAudit:olean']), end='', flush=True)
    report = run(['lake', 'env', 'lean', 'Tests/Weierstrass/ProofAudit.lean'])
    deps = re.findall(r'depends on axioms:\s*\[([^]]*)\]', report)
    assert len(deps)+report.count('does not depend on any axioms') == 18
    assert all(set(d.replace(',', ' ').split()) <= {'propext','Quot.sound','Classical.choice'} for d in deps)
    directory = ROOT/'build/weierstrass'
    directory.mkdir(parents=True, exist_ok=True)
    (directory/'proof-audit.txt').write_text(report)


def options():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qemu', default=os.environ.get('QEMU_RISCV64', 'qemu-riscv64'))
    parser.add_argument('--prefix', default='riscv64-unknown-elf-')
    parser.add_argument('--kinds', nargs='+', default=['mul', 'add', 'sub', 'qmul', 'qadd', 'qsub', 'inv', 'qinv',
        'pointadd', 'pointmul', 'public', 'ecdh', 'encodeder', 'parseder', 'signnonce',
        'signfailure', 'sign', 'signcompact', 'verify', 'verifycompact', 'verifylow', 'verifyzero'])
    parser.add_argument('--curves', nargs='+', choices=['p256','k256'], default=['p256', 'k256'])
    parser.add_argument('--limit', type=int)
    parser.add_argument('--public-errors', action='store_true')
    parser.add_argument('--artifact-tag', default='', help='optional safe directory suffix for isolated extra runs')
    args = parser.parse_args()
    if not re.fullmatch(r'[a-zA-Z0-9_-]*', args.artifact_tag):
        parser.error('artifact tag must contain only ASCII letters, digits, underscores or hyphens')
    valid = {'mul','add','sub','qmul','qadd','qsub','inv','qinv','pointadd','pointmul',
        'public','ecdh','encodeder','parseder','signnonce','signfailure','sign','signcompact',
        'verify','verifycompact','verifylow','verifyzero'}
    if not set(args.kinds) <= valid or (args.limit is not None and args.limit < 1):
        parser.error('unknown routine or invalid case limit')
    return args


def main():
    args = options()
    if cryptography.__version__ != '49.0.0':
        raise RuntimeError('Tests require cryptography==49.0.0')
    from build import compile_probe
    probe = compile_probe()
    audit_proofs()
    for curve in args.curves:
        for kind in args.kinds:
            directory = ROOT/'build/weierstrass'/curve/(kind+args.artifact_tag)
            directory.mkdir(parents=True, exist_ok=True)
            from key_cases import key_cases
            from point_cases import point_cases
            from sign_cases import sign_cases, verify_cases
            from encoding_cases import encoding_cases
            from negative_cases import public_errors, peer_errors, failure_cases
            fixtures = (failure_cases(curve) if kind == 'signfailure' else
                        encoding_cases(curve, kind) if kind in ('parseder', 'encodeder', 'signnonce') else
                        key_cases(curve, kind) if kind in ('public', 'ecdh') else
                        point_cases(curve, kind) if kind in ('pointadd', 'pointmul') else
                        sign_cases(curve, kind) if kind.startswith('sign') else
                        verify_cases(curve, kind) if kind.startswith('verify') else arithmetic(curve, kind))
            if kind in ('public','ecdh','sign','signcompact','verify','verifycompact','verifylow'):
                errors = public_errors(curve,kind,fixtures[0])
                if kind == 'ecdh':
                    errors += peer_errors(curve,fixtures[0])
                fixtures = errors if args.public_errors else fixtures+errors
            if args.limit:
                fixtures = fixtures[:args.limit]
            for f in fixtures:
                f.setdefault('stack', 0x251000)
            (directory/'cases.json').write_text(json.dumps(fixtures))
            print(run([probe, curve, kind, str(directory)], timeout=1800), end='', flush=True)
            prepare(args.prefix, directory)
            for i, fixture in enumerate(fixtures):
                execute(args.prefix, args.qemu, directory, kind, i, fixture)
            print(f'PASS {curve}/{kind}: GNU bytes, both QEMU paths ({len(fixtures)} cases)', flush=True)


if __name__ == '__main__':
    main()
