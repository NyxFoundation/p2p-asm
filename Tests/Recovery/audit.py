"""Kernel elaboration and automatically enumerated transitive axiom audit."""
import re
from pathlib import Path
from build import ROOT, run


def audit():
    roots = [ROOT/'Libp2pAsm'/part/'Quic/Recovery' for part in ('Spec','Asm','Refinement')]
    declarations = []
    for root in roots:
        for path in sorted(root.glob('*.lean')):
            text = path.read_text()
            assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b|^\s*axiom\s',text,re.M), path
            if '/Refinement/' not in str(path):
                continue
            namespace = re.search(r'^namespace (\S+)',text,re.M).group(1)
            declarations.extend(namespace+'.'+name for name in re.findall(r'^theorem (\w+)',text,re.M))
    path = ROOT/'Tests/Recovery/ProofAudit.lean'
    path.write_text('import Libp2pAsm.Refinement.Quic.Recovery.Instructions\n\n'+
                    '\n'.join('#print axioms '+name for name in declarations)+'\n')
    print(run(['lake','build','Libp2pAsm.Refinement.Quic.Recovery.Instructions']),end='')
    output = run(['lake','env','lean',str(path)])
    allowed = {'propext','Quot.sound','Classical.choice'}
    for body in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',output,re.S):
        assert set(re.findall(r'[\w.]+',body)) <= allowed, body
    for name in declarations:
        assert name in output, name
    (ROOT/'Tests/Recovery/.build/axioms.txt').write_text(output)
    print(f'PASS {len(declarations)} declarations: kernel checked, transitive axioms audited')


if __name__ == '__main__':
    audit()
