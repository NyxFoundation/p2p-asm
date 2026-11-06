"""Check recorded complete-suite artifacts and kernel theorem axiom reports."""
import hashlib
import json
import re
import struct
from pathlib import Path
from build import ROOT,OUT,run
from fixtures import cases
from adversarial import cases as extra_cases
from cases import write_case,changed

def proofs():
    print(run(['lake','--no-cache','build','+Tests.QuicCrypto.ProofAudit:olean']),end='')
    report=run(['lake','env','lean','Tests/QuicCrypto/ProofAudit.lean'])
    groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',report)
    assert len(groups)+report.count('does not depend on any axioms')==24
    for group in groups:
        assert {x.strip() for x in group.split(',')} <= {'propext','Classical.choice','Quot.sound'}
    (OUT/'proof-audit.txt').write_text(report)
    print('PASS 24 kernel theorem axiom audits')

def artifacts(category,records):
    for r in records:
        directory=OUT/category/r['kind']
        fixtures=extra_cases(r['kind']) if category else cases(r['kind'])
        assert len(fixtures)==r['cases']
        assert hashlib.sha256((directory/'encoded.bin').read_bytes()).hexdigest()==r['sha256']
        assert (directory/'gnu.bin').read_bytes()==(directory/'encoded.bin').read_bytes()
        counts=[]
        traces=0
        for i in range(r['cases']):
            p=directory/f'case-{i}'
            fresh=OUT/'audit-fixtures'/category/r['kind']/f'case-{i}'
            write_case(fresh,r['kind'],fixtures[i],i)
            assert (fresh/'before.bin').read_bytes()==(p/'before.bin').read_bytes()
            expected=(p/'expected.bin').read_bytes()
            assert (fresh/'expected.bin').read_bytes()==expected
            assert all((p/name).read_bytes()==expected for name in
                       ['after.bin','protocol.native.bin','encoded.native.bin'])
            counts.append(int((p/'steps.txt').read_text()))
            if struct.unpack('<10Q',(p/'meta.bin').read_bytes())[4]:
                traces+=1
                alt=directory/'alternate'/f'case-{i}'
                other=(alt/'expected.bin').read_bytes()
                write_case(fresh,r['kind'],changed(r['kind'],fixtures[i]),i)
                assert (fresh/'before.bin').read_bytes()==(alt/'before.bin').read_bytes()
                assert (fresh/'expected.bin').read_bytes()==other
                assert all((alt/name).read_bytes()==other for name in
                           ['after.bin','protocol.native.bin','encoded.native.bin'])
        assert traces==r['trace_pairs']
        (directory/'measurements.json').write_text(json.dumps({**r,'minimum_steps':min(counts),
            'maximum_steps':max(counts),'per_case_steps':counts},indent=2)+'\n')

def main():
    proofs()
    base=json.loads((OUT/'verification.json').read_text())
    extra=json.loads((OUT/'extra-verification.json').read_text())
    assert {r['kind'] for r in base}=={'initial','keys','update','nonce','number','seal','open','retry','retrycheck'}
    assert {r['kind'] for r in extra}=={'seal','open','retry','retrycheck'}
    artifacts('',base); artifacts('extra',extra)
    records=base+extra
    totals={key:sum(r[key] for r in records) for key in ('cases','trace_pairs','qemu')}
    dependencies=json.loads((ROOT/'Tests/QuicCrypto/provenance.json').read_text())['frozen_dependencies']
    for path,digest in dependencies.items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    (OUT/'summary.json').write_text(json.dumps(totals,indent=2)+'\n')
    print('PASS snapshots/GNU/QEMU/frozen dependencies:',totals)

if __name__=='__main__': main()
