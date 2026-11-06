import Libp2pAsm.Asm.Crypto.Weierstrass.Point

namespace Libp2pAsm.Asm.Crypto.Weierstrass
open Rv64 Util Link
open Spec.Crypto.Weierstrass (Curve)

def workBytes : Nat := 2064
def stackBytes : Nat := 1440

/-- Descriptor (104 bytes, 8-aligned): secret ptr/len at0/8, peer ptr/len16/24,
digest ptr/len32/40, signature ptr/len48/56, output ptr/cap64/72,
work ptr/cap80/88, SHA table96. Unused input fields are never read.
All pointer/length metadata, keys for verification, digests, signatures are public.
Key/scalar bytes are secret. Valid mappings and mutually disjoint ranges are
caller ownership preconditions. Inputs/output may be unaligned. -/
def descriptorCheck : SAsm.Stmt := sequence [
  block [.ANDI .x5 .x10 7], reject (.ne .x5 .x0) 4,
  block [.ADDI .x7 .x0 104], range .x10 .x7,
  block [.ANDI .x5 .x2 15], reject (.ne .x5 .x0) 4,
  block (load .x7 stackBytes), reject (.ltu .x2 .x7) 4]

def inputCheck (offset size : Nat) : SAsm.Stmt := sequence [
  block [.LD .x11 .x10 (imm offset), .LD .x12 .x10 (imm (offset+8))],
  block (load .x7 size), reject (.ne .x12 .x7) 1, range .x11 .x12]

def signatureCheck (compact : Bool) : SAsm.Stmt :=
  if compact then inputCheck 48 64 else sequence [
    block [.LD .x11 .x10 48, .LD .x12 .x10 56, .ADDI .x7 .x0 8],
    reject (.ltu .x12 .x7) 1, block [.ADDI .x7 .x0 73],
    reject (.geu .x12 .x7) 1, range .x11 .x12]

def buffersCheck (outputBytes : Nat) (hash : Bool := false) : SAsm.Stmt := sequence [
  block [.LD .x11 .x10 64, .LD .x12 .x10 72], capacity .x12 outputBytes,
  block (load .x7 outputBytes), range .x11 .x7,
  block [.LD .x11 .x10 80, .LD .x12 .x10 88], capacity .x12 workBytes,
  block (load .x7 workBytes), range .x11 .x7,
  block [.ANDI .x5 .x11 7], reject (.ne .x5 .x0) 4,
  if hash then sequence [block [.LD .x11 .x10 96, .ADDI .x7 .x0 512],
    range .x11 .x7, block [.ANDI .x5 .x11 7], reject (.ne .x5 .x0) 4] else empty]

/-- s0=work,s1=descriptor,s2=valid secret mask bit,s3=status,s4=output.
Only writes begin after all public bounds/length/alignment checks. -/
def beginWork : SAsm.Stmt := sequence [enter,
  block [.ADDI .x9 .x10 0, .LD .x8 .x9 80, .LD .x20 .x9 64,
    .ADDI .x18 .x0 1, .ADDI .x19 .x0 0],
  block (load .x21 workBytes), wipe .x8 .x21]

def endWork : SAsm.Stmt := sequence [wipe .x8 .x21,
  block [.ADDI .x10 .x19 0], leave]

/-- Failure after public parsing: work and save frame are wiped, no output. -/
def failWork (condition : SAsm.Cond) (status : Nat) : Part :=
  .ite condition (.asm (sequence [block [.ADDI .x19 .x0 (imm status)], endWork])) (.asm empty)

def setupConstants (c : Curve) : Part := .asm (sequence [
  constant .x8 544 1, constant .x8 576 (2^512 % c.prime),
  constant .x8 608 (2^512 % c.order)])

def basePoint (c : Curve) (offset : Nat) : Part := .asm (sequence [
  constant .x8 offset (c.generator.x*2^256 % c.prime),
  constant .x8 (offset+32) (c.generator.y*2^256 % c.prime),
  constant .x8 (offset+64) (2^256 % c.prime)])

/-- Invalid private scalar is replaced with 1 in constant time; status records
the validation result. Computation and address traces still run identically.
No branch on private validation, no output change on invalid input. -/
def secretScalar (c : Curve) : Part := .seq [
  .asm (block [.LD .x11 .x9 0]), .asm (decode .x8 .x11 0 0),
  .asm (canonical .x8 0 c.order .x18 true),
  .asm (block [.XORI .x19 .x18 1, .SLLI .x19 .x19 3,
    .SUB .x22 .x0 .x18, .ADDI .x10 .x8 0, .ADDI .x11 .x8 0, .ADDI .x12 .x8 544]),
  .asm (maskSelect .x10 .x11 .x12 .x22)]

/-- Constant-time error-atomic commit. Destination must be readable+writable.
Both success/failure touch exactly the designated output extent; failures store
each preexisting byte back unchanged. s3=public result status. -/
def commit (offset size : Nat) : Part := .asm (sequence [
  block [.SLTU .x22 .x0 .x19, .ADDI .x22 .x22 (-1),
    .ADDI .x5 .x8 (imm offset), .ADDI .x6 .x20 0, .ADDI .x7 .x0 (imm size)],
  .loop (.ne .x7 .x0) (block [.LBU .x28 .x5 0, .LBU .x29 .x6 0,
    .XOR .x28 .x28 .x29, .AND .x28 .x28 .x22, .XOR .x28 .x28 .x29,
    .SB .x6 .x28 0, .ADDI .x5 .x5 1, .ADDI .x6 .x6 1, .ADDI .x7 .x7 (-1)])])

end Libp2pAsm.Asm.Crypto.Weierstrass
