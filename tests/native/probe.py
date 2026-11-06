"""Shared Linux RV64 test driver; protocol code always comes from the Lean generator."""

DRIVER = """
.option norvc
.option norelax
.section .text.start, "ax", @progbits
.global _start
_start:
{arguments}
  jal ra, protocol_entry
  la t0, output
  sd a0, 0(t0)
  sd a1, 8(t0)
  sd a2, 16(t0)
  la t1, payload
  addi t2, t0, 24
  li t3, {length}
copy:
  beq t3, zero, copied
  lbu t4, 0(t1)
  sb t4, 0(t2)
  addi t1, t1, 1
  addi t2, t2, 1
  addi t3, t3, -1
  jal zero, copy
copied:
  li a0, 1
  mv a1, t0
  li a2, {output_length}
  li a7, 64
  ecall
  li a0, 0
  li a7, 93
  ecall
.section .data, "aw", @progbits
payload:
  .byte {bytes}
.section .bss, "aw", @nobits
.balign 8
output:
  .skip {output_length}
"""


def source(arguments, data):
    return DRIVER.format(
        arguments=arguments, length=len(data), output_length=24 + len(data),
        bytes=", ".join(str(b) for b in data) if data else "0",
    )

