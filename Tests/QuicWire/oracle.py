"""Pinned quic-go codec oracle; all generated Go state is under build/quic-wire."""
import json
import os
from pathlib import Path
import subprocess
from reference import frame, packet, parameters, WireError
from cases import frame_cases, packet_cases
from encoding import tp_encodings

ROOT=Path(__file__).resolve().parents[2]


def run():
    directory=ROOT/'build/quic-wire/go-oracle'
    directory.mkdir(parents=True,exist_ok=True)
    (directory/'go.mod').write_text('module github.com/quic-go/quic-go/wire-oracle\n\ngo 1.24\n\nrequire github.com/quic-go/quic-go v0.59.0\n')
    (directory/'go.sum').write_bytes((ROOT/'Tests/QuicWire/go.sum').read_bytes())
    (directory/'main.go').write_bytes((ROOT/'Tests/QuicWire/oracle.go').read_bytes())
    requests=[]
    for kind,fs in [('frame',frame_cases()),('packet',packet_cases())]:
        for f in fs:
            if not f['checkSpec'] or f['status']==5: continue
            data=bytes(f['regions'][0][9:9+f['args'][1]])
            if kind=='packet':
                # quic-go ParsePacket is specifically its supported long-header codec.
                if len(data)<5 or data[0]&128==0 or data[1:5]!=b'\0\0\0\1': continue
                if f['label']=='zero-length': continue # quic-go accepts envelope length zero.
            requests.append((dict(Kind=kind,Hex=data.hex()),f))
    for f in tp_encodings():
        if f['status']==0:
            requests.append((dict(Kind='tp',Hex=bytes(f['output']).hex(),Server=bool(f['args'][6])),f))
    env=os.environ|{'GOCACHE':str(ROOT/'build/quic-wire/go-cache'),'GOTOOLCHAIN':'local','GOSUMDB':'off','GOPROXY':'off'}
    result=subprocess.run([os.environ.get('GO','go'),'run','-mod=mod','.'],cwd=directory,env=env,
        input=''.join(json.dumps(r)+'\n' for r,_ in requests),capture_output=True,text=True,check=False)
    if result.returncode: raise RuntimeError(result.stderr)
    for (r,f),line in zip(requests,result.stdout.splitlines(),strict=True):
        got=json.loads(line)
        want = True if f['label']=='crypto-overflow' else f['status']==0
        assert got['OK']==want,(f['label'],r,got,f['status'])
        if got['OK'] and f['status']==0 and r['Kind']!='tp':
            assert got['Consumed']==f['consumed'],(f['label'],got)
    (directory/'results.jsonl').write_text(result.stdout)
    print(f'PASS quic-go v0.59.0: {len(requests)} overlapping codec cases',flush=True)


if __name__=='__main__': run()
