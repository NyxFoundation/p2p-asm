#!/usr/bin/env python3
"""Audit saved executions; never infer a pass from a stale log message."""
from pathlib import Path
import hashlib
import json
import re

ROOT=Path(__file__).resolve().parents[2]
BUILD=ROOT/'build/rsa'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_run(directory):
    cases=json.loads((directory/'cases.json').read_text())
    lines=(directory/'measurements.txt').read_text().splitlines()
    assert len(lines)==len(cases)+1,directory
    encoded=(directory/'encoded.bin').read_bytes()
    assert encoded==(directory/'protocol.bin').read_bytes()
    rows=[]
    for i,f in enumerate(cases):
        idx,label,steps,budget=lines[i+1].split()
        assert int(idx)==i and label==f['label']
        assert int(steps)<int(budget.split('=')[1])
        expected=(directory/f'case-{i}.expected.bin').read_bytes()
        for suffix in ['after','protocol.native','encoded.native']:
            assert (directory/f'case-{i}.{suffix}.bin').read_bytes()==expected,(directory,i,suffix)
        n=int.from_bytes(bytes(f['n']),'big')
        rows.append(dict(label=label,status=f['status'],steps=int(steps),
                         modulusBits=n.bit_length(),exponentBits=int.from_bytes(bytes(f['e']),'big').bit_length(),
                         bound=int(budget.split('=')[1]),snapshotSHA256=hashlib.sha256(expected).hexdigest()))
    return dict(directory=str(directory.relative_to(ROOT)),cases=rows,
                encodedSHA256=hashlib.sha256(encoded).hexdigest(),
                staticInstructions=int(lines[0].split('=')[1]))


def main():
    audit=(BUILD/'proof-audit.txt').read_text()
    axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',audit)
    assert len(axioms)+audit.count('does not depend on any axioms')==24
    assert all(set(a.replace(',',' ').split())<={'propext','Quot.sound','Classical.choice'} for a in axioms)
    runs=[audit_run(BUILD/f'{kind}-{group}') for kind in ['pkcs','pss']
          for group in ['positive','emsa','errors','official','supplement']]
    for kind in ['pkcs','pss']:
        positives=next(r['cases'] for r in runs if r['directory'].endswith(f'{kind}-positive'))
        assert {2048,2049,2055,2056,3072,4096}<={r['modulusBits'] for r in positives if r['status']==0}
        assert {2,17,66}<={r['exponentBits'] for r in positives if r['status']==0}
    paths=[p for root in ['Spec','Asm','Refinement'] for p in (ROOT/f'Libp2pAsm/{root}/Crypto/RSA').glob('*.lean')]
    for p in paths:
        assert not re.search(r'\b(sorry|native_decide|unsafe|axiom)\b',p.read_text()),p
    total=sum(len(r['cases']) for r in runs)
    report=dict(caseExecutions=total,qemuExecutions=2*total,kernelCheckedLemmas=24,runs=runs,
                implementationSHA256={str(p.relative_to(ROOT)):digest(p) for p in sorted(paths)},
                proofGaps=['whole-function refinement','fetch correspondence',
                           'whole-function resource/cleanup safety','assembly termination/instruction bound'])
    (BUILD/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS {total} complete model/oracle snapshots, {2*total} QEMU executions, 24 kernel lemmas')


if __name__=='__main__':
    main()
