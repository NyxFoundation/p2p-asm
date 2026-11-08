"""Independent Spec, actual instruction snapshots, GNU and two QEMU executions."""
import argparse
import json
import os
import subprocess
from build import build,ROOT
from native import prepare,execute
from cases import limits_cases
from registry import cases as registry_cases
from queue import cases as queue_cases
from requests import cases as request_cases
from layout import cases as layout_cases
from admission import cases as admission_cases
from connections import cases as connection_cases
from integration import cases as integration_cases
from copying import cases as copy_cases
from abi import cases as abi_cases


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--qemu',default=os.environ.get('QEMU_RISCV64','qemu-riscv64'))
    p.add_argument('--prefix',default=os.environ.get('RISCV_PREFIX','riscv64-unknown-elf-'))
    p.add_argument('--kinds',nargs='+',default=['limits','limits-export','abi']+[f'registry-{i}' for i in range(10)]+[f'queue-{i}' for i in range(5)]+[f'request-{i}' for i in range(8)]+[f'connection-{i}' for i in range(4)]+['resolve','copy','owned-issue','owned-reap','init-begin','init-resume','admit','charge','quantum','kernel-quantum'])
    a=p.parse_args();probe=build('kernel-probe')
    for kind in a.kinds:
        fs=(abi_cases() if kind == 'abi' else copy_cases() if kind == 'copy' else integration_cases()[kind] if kind in ('resolve','owned-issue','owned-reap','kernel-quantum') else
            connection_cases()[kind] if kind.startswith('connection-') else admission_cases()[kind] if kind in ('admit','charge','quantum') else layout_cases()[kind] if kind.startswith('init-') else registry_cases()[kind] if kind.startswith('registry-') else
            queue_cases()[kind] if kind.startswith('queue-') else
            request_cases()[kind] if kind.startswith('request-') else limits_cases(kind=='limits-export'))
        d=ROOT/'build/kernel'/kind;d.mkdir(parents=True,exist_ok=True)
        (d/'cases.json').write_text(json.dumps(fs))
        subprocess.run([str(probe),kind,str(d)],check=True)
        prepare(a.prefix,d)
        for i,f in enumerate(fs): execute(a.prefix,a.qemu,d,kind,i,f)
        print(f'PASS {kind}: {len(fs)} GNU/BOTH QEMU complete snapshots',flush=True)

if __name__=='__main__':main()
