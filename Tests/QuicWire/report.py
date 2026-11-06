#!/usr/bin/env python3
"""Recheck saved complete snapshots and produce a machine-readable result."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]


def main():
    results={}
    for kind in ['packet','frame','tp','packet-encode','frame-encode','tp-encode',
                 'permission','packet-batch','frame-batch']:
        folder=ROOT/'build/quic-wire'/kind
        cases=json.loads((folder/'cases.json').read_text())
        measurements=(folder/'measurements.txt').read_text().splitlines()
        assert len(measurements)==len(cases)+1,kind
        static=int(measurements[0].split('=')[1])
        steps=[]
        for i,f in enumerate(cases):
            want=(folder/f'case-{i}.expected.bin').read_bytes()
            for suffix in ('after.bin','protocol.native.bin','encoded.native.bin'):
                assert (folder/f'case-{i}.{suffix}').read_bytes()==want,(kind,f['label'],suffix)
            words=measurements[i+1].split()
            used,bound=int(words[-2]),int(words[-1].split('=')[1])
            assert used<bound
            steps.append(used)
        code=(folder/'encoded.bin').read_bytes()
        for variant in ('protocol','encoded'):
            assert (folder/f'{variant}.bin').read_bytes()==code
        results[kind]={'cases':len(cases),'qemu_executions':2*len(cases),
            'static_instructions':static,'min_steps':min(steps),'max_steps':max(steps),
            'code_sha256':hashlib.sha256(code).hexdigest()}
    report={'routines':results,'cases':sum(r['cases'] for r in results.values()),
            'qemu_executions':sum(r['qemu_executions'] for r in results.values()),
            'scope':'finite wire codec differential execution; no source-coverage percentage'}
    (ROOT/'build/quic-wire/result.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__': main()
