#!/usr/bin/env python3
"""Kernel-check and automatically enumerate every owned refinement theorem."""
import re
import subprocess
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]


def main():
    subprocess.run(['lake','build','Tests.QuicWire.ProofAudit','Tests.QuicWire.SpecTests'],cwd=ROOT,check=True)
    result=subprocess.run(['lake','env','lean','Tests/QuicWire/ProofAudit.lean'],cwd=ROOT,
        check=True,capture_output=True,text=True)
    sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',result.stdout)
    closed=result.stdout.count('does not depend on any axioms')
    count=int(re.search(r'WIRE_THEOREMS=(\d+)',result.stdout)[1])
    assert count>0 and len(sets)+closed==count
    assert all(set(s.replace(',',' ').split()) <= {'propext','Quot.sound','Classical.choice'} for s in sets)
    for root in ('Spec','Asm','Refinement'):
        directory=ROOT/f'Libp2pAsm/{root}/Quic'
        paths=list(directory.glob('Wire*.lean'))+list((directory/'Wire').rglob('*.lean'))
        for path in paths:
            assert not re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',path.read_text()),path
    out=ROOT/'build/quic-wire/proof-audit.txt'
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(result.stdout)
    print(f'PASS {count} automatically discovered kernel-checked theorems; axiom whitelist',flush=True)


if __name__=='__main__': main()
