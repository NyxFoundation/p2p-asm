"""Kernel check, automatic transitive axiom audit, and forbidden escape-hatch scan."""
from pathlib import Path
import re
import subprocess
from build import build,PACKAGE,ROOT


def main():
    build('Tests.Kernel.ProofAudit')
    r=subprocess.run(['lake','env','lean','Tests/Kernel/ProofAudit.lean'],cwd=PACKAGE,
        check=True,capture_output=True,text=True)
    sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',r.stdout)
    closed=r.stdout.count('does not depend on any axioms')
    count=int(re.search(r'KERNEL_THEOREMS=(\d+)',r.stdout)[1])
    assert count and len(sets)+closed==count
    assert all(set(s.replace(',',' ').split()) <= {'propext','Quot.sound','Classical.choice'} for s in sets)
    for part in ('Spec','Asm','Refinement'):
        for p in (ROOT/f'Libp2pAsm/{part}/Kernel').glob('*.lean'):
            assert not re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',p.read_text()),p
    (ROOT/'build/kernel/proof-audit.txt').write_text(r.stdout)
    print(f'PASS {count} automatically enumerated kernel-checked declarations; transitive axiom whitelist')

if __name__=='__main__':main()
