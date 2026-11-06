#!/usr/bin/env python3
"""Spec vs RV64, complete footprints, GNU bytes, and both QEMU paths."""
import argparse
import json
import os
import subprocess
from build import compile_probe
from native import ROOT, prepare, execute
from cases import packet_cases, frame_cases, tp_cases
from encoding import packet_encodings, frame_encodings, tp_encodings
from extra import public_packets, public_frames, permissions
from batch import packet_batches, frame_batches
from fuzz import cases as fuzz_cases


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qemu',default=os.environ.get('QEMU_RISCV64','qemu-riscv64'))
    parser.add_argument('--prefix',default=os.environ.get('RISCV_PREFIX','riscv64-unknown-elf-'))
    parser.add_argument('--kinds',nargs='+',default=['packet','frame','tp','packet-encode',
        'frame-encode','tp-encode','permission','packet-batch','frame-batch'])
    args=parser.parse_args()
    probe=compile_probe()
    for kind in args.kinds:
        fs={'packet':lambda:packet_cases()+public_packets()+fuzz_cases('packet'),
            'frame':lambda:frame_cases()+public_frames()+fuzz_cases('frame'),
            'tp':lambda:tp_cases()+fuzz_cases('tp'),
            'packet-encode':packet_encodings,'frame-encode':frame_encodings,
            'tp-encode':tp_encodings,'permission':permissions,
            'packet-batch':packet_batches,'frame-batch':frame_batches}[kind]()
        directory=ROOT/'build/quic-wire'/kind
        directory.mkdir(parents=True,exist_ok=True)
        (directory/'cases.json').write_text(json.dumps(fs))
        subprocess.run([str(probe),kind,str(directory)],cwd=ROOT,check=True)
        prepare(args.prefix,directory)
        for i,f in enumerate(fs):
            execute(args.prefix,args.qemu,directory,kind,i,f)
        print(f'PASS {kind}: {len(fs)} cases, GNU byte equality, both QEMU paths',flush=True)


if __name__=='__main__':
    main()
