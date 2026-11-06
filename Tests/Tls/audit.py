#!/usr/bin/env python3
"""Audit artifacts and kernel axioms; optional explicit worktree ownership baseline."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import struct
from build import ROOT, OUT, run


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def proof_audit():
    log = run(['lake','env','lean','Tests/Tls/ProofAudit.lean'])
    (OUT/'proof-audit-final.log').write_text(log)
    lines = [line for line in log.splitlines() if 'axioms' in line]
    assert len(lines) == (ROOT/'Tests/Tls/ProofAudit.lean').read_text().count('#print axioms')
    for line in lines:
        if 'does not depend on any axioms' in line: continue
        names = line.split('[',1)[1].split(']',1)[0].split(', ')
        assert set(names) <= {'propext','Quot.sound','Classical.choice'}, line
    for directory in ['Spec','Asm','Refinement']:
        for path in (ROOT/f'Libp2pAsm/{directory}/Tls').glob('*.lean'):
            assert not re.search(r'\b(sorry|native_decide|axiom|unsafe)\b',path.read_text()), path
            assert len(path.read_text().splitlines()) < 800, path
    return len(lines)


def frozen_audit(baseline):
    if baseline is None:
        return None
    frozen = json.loads(baseline.read_text())
    if not isinstance(frozen, dict):
        raise ValueError("Invalid source baseline")
    for name, expected in frozen.items():
        if not isinstance(name, str) or not isinstance(expected, str):
            raise ValueError("Invalid baseline entry")
        target = (ROOT/name).resolve()
        if not target.is_relative_to(ROOT) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError("Invalid baseline path or digest")
        assert sha(target) == expected, name
    return len(frozen)


def artifacts(summary_path):
    summary = json.loads(summary_path.read_text())
    directory = OUT/summary_path.name.removesuffix('-verification.json')
    encoded = (directory/'encoded.bin').read_bytes()
    assert hashlib.sha256(encoded).hexdigest() == summary['sha256']
    assert (directory/'gnu.bin').read_bytes() == encoded
    count = int((directory/'count.txt').read_text())
    assert count == summary['cases']
    pairs = 0
    max_steps = 0
    for i in range(count):
        primary = directory/f'case-{i}'
        paths = [primary]
        alt = directory/'alternate'/f'case-{i}'
        if (alt/'before.bin').exists(): paths.append(alt); pairs += 1
        max_steps = max(max_steps,int((primary/'steps.txt').read_text()))
        for path in paths:
            expected = (path/'expected.bin').read_bytes()
            for name in ('after.bin','protocol.native.bin','encoded.native.bin'):
                assert (path/name).read_bytes() == expected, (path,name)
            for name in ('protocol.program.bin','encoded.program.bin'):
                assert (path/name).read_bytes() == encoded, (path,name)
    assert summary['qemu'] == 2*(count+pairs)
    return dict(summary,artifact_directory=str(directory.relative_to(ROOT)),trace_pairs=pairs,max_steps=max_steps)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frozen-baseline", type=Path,
                        help="explicit source-ownership inventory for THIS worktree")
    args = parser.parse_args()
    assert OUT.exists()
    proofs, frozen = proof_audit(), frozen_audit(args.frozen_baseline)
    names = ['handshake','application','finished','hash','messageHash','final-decode','final-encode','vector','boundary','edge-decode','edge-encode']
    suites = [artifacts(OUT/f'{name}-verification.json') for name in names]
    result = {'proofs':proofs,'unchanged_frozen_files':frozen,'suites':suites,
              'cases':sum(s['cases'] for s in suites),'trace_pairs':sum(s['trace_pairs'] for s in suites),
              'qemu_runs':sum(s['qemu'] for s in suites)}
    (OUT/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__': main()
