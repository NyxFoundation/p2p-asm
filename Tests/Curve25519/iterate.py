#!/usr/bin/env python3
"""RFC 7748 1000 iterations: independent Spec, cryptography and both QEMU paths.
The lowered interpreter tests the first two recurrence steps in check.py; this
additional long recurrence is native only, not a 1.5-billion-step model run.
"""
import argparse
import os
import sys
from pathlib import Path
from cryptography.hazmat.primitives.asymmetric import x25519
from build import ROOT,OUT,run,native_config
sys.path.append(str(ROOT/'Tests/HashCrypto'))
import native

EXPECTED=bytes.fromhex('684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51')


def driver():
    return '''.option norvc
.option norelax
.section .text.start,"ax",@progbits
.global _start
_start:
  la sp, stack_end
  li s11, 1000
again:
  la a0, secret
  li a1, 32
  la a2, peer
  li a3, 32
  la a4, result
  li a5, 32
  la a6, work
  li a7, 896
  la ra, returned
  jal x0, protocol_entry
.section .text.return,"ax",@progbits
returned:
  bnez a0, failure
  addi s11,s11,-1
  beqz s11, done
  la t0, secret
  la t1, peer
  la t2, result
  li t3, 32
copy:
  lbu t4,0(t0)
  sb t4,0(t1)
  lbu t4,0(t2)
  sb t4,0(t0)
  addi t0,t0,1
  addi t1,t1,1
  addi t2,t2,1
  addi t3,t3,-1
  bnez t3,copy
  j again
done:
  li a0,1
  la a1, result_guard
  li a2,1240
  li a7,64
  ecall
  li a0,0
  j exit
failure:
  li a0,1
exit:
  li a7,93
  ecall
.section .data,"aw",@progbits
.balign 16
secret: .byte 9
.zero 31
peer: .byte 9
.zero 31
result_guard: .fill 8,1,165
result: .fill 32,1,204
.fill 8,1,90
work: .fill 896,1,204
.fill 8,1,90
stack: .fill 8,1,105
.fill 272,1,105
stack_end: .fill 8,1,105
'''


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qemu',default=os.environ.get('QEMU_RISCV64','qemu-riscv64'))
    parser.add_argument('--prefix',default='riscv64-unknown-elf-')
    args=parser.parse_args()
    run(['lake','-d',str(native_config()),'--no-cache','build','curve25519IterateSpec'])
    directory=OUT/'iterations-1000'
    directory.mkdir(parents=True,exist_ok=True)
    run([str(OUT/'lake/bin/curve25519IterateSpec'),'1000',str(directory/'spec.bin')])
    assert (directory/'spec.bin').read_bytes()==EXPECTED
    k=u=(9).to_bytes(32,'little')
    for _ in range(1000):
        k,u=x25519.X25519PrivateKey.from_private_bytes(k).exchange(
            x25519.X25519PublicKey.from_public_bytes(u)),k
    assert k==EXPECTED
    (directory/'driver.S').write_text(driver())
    (directory/'link.ld').write_text('ENTRY(_start)\nSECTIONS {\n'
        '. = 0x10000; .text.protocol : { *(.text.protocol) }\n'
        '. = 0x80000; .text : { *(.text.return) *(.text.start) }\n'
        '. = 0x100000; .data : { *(.data) }\n}\n')
    native.assemble(args.prefix,directory/'driver.S',directory/'driver.o')
    expected=b'\xa5'*8+EXPECTED+b'\x5a'*8+bytes(896)+b'\x5a'*8+b'\x69'*8+bytes(272)+b'\x69'*8
    assert len(expected)==1240
    for mode in ('protocol','encoded'):
        elf=directory/f'{mode}.elf'
        run([args.prefix+'ld','--no-relax','-T',str(directory/'link.ld'),'-o',str(elf),
             str(OUT/f'xraw/{mode}.o'),str(directory/'driver.o')])
        actual=run([args.qemu,str(elf)],binary=True)
        (directory/f'{mode}.bin').write_bytes(actual)
        assert actual==expected,mode
    print('PASS RFC 7748 1000 iterations: Spec, cryptography, both QEMU paths, guards/work/stack wipes')


if __name__=='__main__': main()
