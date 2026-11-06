#!/usr/bin/env python3
"""Audit saved execution artifacts and emit a machine-readable integration report."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
KINDS = ('mul add sub qmul qadd qsub inv qinv pointadd pointmul public ecdh '
         'encodeder parseder signnonce signfailure sign signcompact verify verifycompact verifylow').split()


def audit(directory):
    cases = json.loads((directory/'cases.json').read_text())
    encoded = (directory/'encoded.bin').read_bytes()
    assert (directory/'protocol.bin').read_bytes() == encoded
    measurements = (directory/'measurements.txt').read_text().splitlines()
    assert len(measurements) == len(cases)+1
    for i, case in enumerate(cases):
        assert measurements[i+1].startswith(f'{i} {case["label"]} ')
        expected = (directory/f'case-{i}.expected.bin').read_bytes()
        for variant in ('after', 'protocol.native', 'encoded.native'):
            assert (directory/f'case-{i}.{variant}.bin').read_bytes() == expected, (directory,i,variant)
    return dict(cases=len(cases), qemu_executions=2*len(cases),
        trace_pairs=sum('tracePair=true' in line for line in measurements),
        instruction_bytes=len(encoded), encoded_sha256=hashlib.sha256(encoded).hexdigest(),
        fixture_sha256=hashlib.sha256((directory/'cases.json').read_bytes()).hexdigest())


def main():
    results = {}
    for curve in ('p256','k256'):
        for kind in KINDS+['verifyzero-unaligned','public-trace','ecdh-trace','public-strict-rejects','ecdh-strict-rejects',
                           'sign-strict-rejects','verify-strict-rejects']:
            directory = ROOT/'build/weierstrass'/curve/kind
            results[f'{curve}/{kind}'] = audit(directory)
    totals = {key:sum(row[key] for row in results.values()) for key in ('cases','qemu_executions','trace_pairs')}
    result = dict(totals=totals,routines=results,proof_lemmas=18,
                  proof_boundary='Primitive identities and spec encoding contracts; no whole-function formal verification.')
    (ROOT/'build/weierstrass/result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(totals))


if __name__ == '__main__':
    main()
