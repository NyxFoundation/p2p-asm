"""Fail closed on missing/mismatched artifacts; inventory only owned source trees."""
from pathlib import Path
import argparse,hashlib,json,re
ROOT=Path(__file__).resolve().parents[2]
OWNED=['Libp2pAsm/Spec/Stream','Libp2pAsm/Asm/Stream','Libp2pAsm/Refinement/Stream',
       'Libp2pAsm/Spec/Multistream','Libp2pAsm/Asm/Multistream',
       'Libp2pAsm/Spec/Ping','Libp2pAsm/Asm/Ping','Tests/Streams']
LEAVES=['receive','consume','peek','append','reserve','settle','ack','stop','id','ordinal',
        'negotiate','neg-emit','neg-timer','ping-begin','ping-feed','ping-release',
        'ping-finish','ping-cancel','ping-timer','ping-quota']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def artifacts():
    results={}
    for kind in LEAVES:
        p=ROOT/'build/streams'/kind
        fs=json.loads((p/'cases.json').read_text())
        code=(p/'encoded.bin').read_bytes()
        for variant in ('protocol','encoded'):
            assert (p/f'{variant}.linked.bin').read_bytes()==code,(kind,variant,'code')
        for i,f in enumerate(fs):
            want=(p/f'case-{i}.expected.bin').read_bytes()
            for variant in ('after','protocol.native','encoded.native'):
                assert (p/f'case-{i}.{variant}.bin').read_bytes()==want,(kind,i,variant)
            trace=(p/f'case-{i}.accesses.bin').read_bytes()
            assert len(trace)%32==0
        measurements=(p/'measurements.txt').read_text().splitlines()
        assert len(measurements)==len(fs)+1
        results[kind]={'cases':len(fs),'qemu_runs':2*len(fs),'code_sha256':digest(p/'encoded.bin'),
                       'instructions':int(measurements[0].split('=')[1]),
                       'max_steps':max(int(line.split(': ')[1].split('/')[0]) for line in measurements[1:])}
    return results


def sources():
    files=[p for name in OWNED for p in (ROOT/name).rglob('*') if p.is_file() and '__pycache__' not in p.parts]
    for p in files:
        if p.suffix=='.lean':
            assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b',p.read_text()),p
            assert not re.search(r'^\s*(?:private\s+)?axiom\s',p.read_text(),re.M),p
        assert len(p.read_bytes().splitlines())<=800,p
    return {str(p.relative_to(ROOT)):digest(p) for p in sorted(files)}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--baseline',type=Path)
    args=parser.parse_args()
    if args.baseline:
        frozen=json.loads(args.baseline.read_text())
        for name,sha in frozen.items():
            p=(ROOT/name).resolve()
            assert p.is_relative_to(ROOT) and p.is_file() and digest(p)==sha,name
    report={'source_hashes':sources(),'results':artifacts(),
            'limits':'Tests/Streams/README.md','proof_audit':'Tests/Streams/ProofAudit.lean',
            'proof_scope':'Arithmetic/invariants and exact ordinal leaf; whole-engine refinement/resource/CT proofs not claimed.'}
    (ROOT/'build/streams/report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f"PASS {sum(r['cases'] for r in report['results'].values())} cases, "
          f"{sum(r['qemu_runs'] for r in report['results'].values())} QEMU runs, "
          f"{len(report['source_hashes'])} source files; all hashes/snapshots match")

if __name__=='__main__':main()
