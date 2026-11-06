from pathlib import Path
import argparse,json,subprocess,os
from native import prepare,execute
from build import compile_probe,ROOT
from extra_cases import emit_cases,timer_cases,quota_cases,metadata_cases,large_receive_cases,overlap_cases
from id_cases import cases as id_cases,ordinal_cases
from ping_cases import suites as ping_suites
from send_cases import suites,permutation_suites
from multistream_cases import cases as negotiation_cases
from cases import receive_cases,consume_cases,peek_cases

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--leaf',choices=['receive','consume','peek','append','reserve','settle','ack','stop','negotiate','ping-begin','ping-feed','ping-release','ping-finish','ping-cancel','ping-timer','id','neg-emit','neg-timer','ping-quota','ordinal'])
    parser.add_argument('--native',action='store_true')
    parser.add_argument('--qemu',default=os.environ.get('QEMU_RISCV64','qemu-riscv64'))
    parser.add_argument('--prefix',default=os.environ.get('RISCV_PREFIX','riscv64-unknown-elf-'))
    args=parser.parse_args()
    from multistream_oracle import frame,HEADER,PING,NA
    pins=json.loads((ROOT/'Tests/Streams/fixtures.json').read_text())['frames']
    assert [frame(HEADER).hex(),frame(PING).hex(),frame(NA).hex()]==[pins[k] for k in ('header','ping','na')]
    probe=compile_probe()
    subprocess.run([str(probe),"spec"],check=True)
    all_suites={'ordinal':ordinal_cases,'neg-emit':emit_cases,'neg-timer':timer_cases,'ping-quota':quota_cases,'id':id_cases,'negotiate':negotiation_cases,'receive':receive_cases,'consume':consume_cases,'peek':peek_cases}
    all_suites.update({k:lambda fs=fs:fs for k,fs in suites().items()})
    all_suites.update({k:lambda fs=fs:fs for k,fs in ping_suites().items()})
    for kind,make in all_suites.items():
        if args.leaf and args.leaf!=kind:
            continue
        p=ROOT/'build/streams'/kind
        p.mkdir(parents=True,exist_ok=True)
        fs=make()+metadata_cases().get(kind,[])
        if kind=="receive":fs+=large_receive_cases()+overlap_cases()
        fs+=permutation_suites().get(kind,[])
        for f in fs:
            cap=max(0,len(f['regions'][1])-17)
            length=max(0,len(f['regions'][3])-17)
            f['budget']=5000+300*length if kind=='negotiate' else (
                5000+200*(length+cap) if kind in ('receive','consume','peek','append','reserve','settle','ack','stop') else 5000)
        (p/'cases.json').write_text(json.dumps(fs,separators=(',',':')))
        subprocess.run([str(probe),kind,str(p)],check=True)
        if args.native:
            prepare(args.prefix,p)
            for i,f in enumerate(fs):
                execute(args.prefix,args.qemu,p,kind,i,f)
            print(f"PASS {kind}: GNU byte equality and {2*len(fs)} QEMU executions",flush=True)
if __name__=='__main__':
    main()
