import Libp2pAsm.Asm.Tls.Codec

namespace Libp2pAsm.Asm.Tls.Encode
open Rv64 Crypto.Util Crypto.Link

/-- align8(body+4) plus a 512-byte view, 16896 decoder scratch, descriptor64. -/
def required (n : Nat) : Nat := (n+11)/8*8+17472

def validate : SAsm.Stmt := sequence [descriptor 72,
  block [.LD .x11 .x10 8, .SRLI .x5 .x11 24], reject (.ne .x5 .x0) 2,
  block [.LD .x12 .x10 16, .ADDI .x7 .x0 255], reject (.ltu .x7 .x12) 2,
  block [.LD .x7 .x10 56], reject (.ltu .x7 .x11) 9,
  block [.LD .x12 .x10 64, .ADDI .x7 .x0 1], reject (.ltu .x7 .x12) 2,
  block [.ADDI .x15 .x11 4, .LD .x12 .x10 32], reject (.ltu .x12 .x15) 5,
  block (load .x7 17472 ++ [.ADDI .x16 .x11 11, .ANDI .x16 .x16 (-8),
    .ADD .x17 .x16 .x7, .LD .x12 .x10 48]), reject (.ltu .x12 .x17) 5,
  alignedField 40,
  spans 72 352 [variableSpan 0 8, ⟨field 24,register .x15⟩, ⟨field 40,register .x17⟩]]

def setup : SAsm.Stmt := sequence [enter, block [
  .LD .x8 .x10 0, .LD .x9 .x10 8, .LD .x18 .x10 24, .LD .x19 .x10 40,
  .ADDI .x20 .x16 0, .ADDI .x21 .x17 0, .LD .x22 .x10 16,
  .LD .x23 .x10 56, .LD .x24 .x10 64], wipe .x19 .x21,
  block ([.SB .x19 .x22 0] ++ storeBE .x19 .x9 1 3 ++ [.ADDI .x12 .x19 4]),
  copy .x12 .x8 .x9]

def arguments : SAsm.Stmt := block <|
  load .x7 17408 ++ [.ADD .x10 .x19 .x20, .ADD .x10 .x10 .x7,
    .SD .x10 .x19 0, .ADDI .x11 .x9 4, .SD .x10 .x11 8,
    .ADD .x11 .x19 .x20, .SD .x10 .x11 16, .ADDI .x12 .x0 512, .SD .x10 .x12 24,
    .ADDI .x11 .x11 512, .SD .x10 .x11 32] ++ load .x12 16896 ++
    [.SD .x10 .x12 40, .SD .x10 .x23 48, .SD .x10 .x24 56]

def cleanup : SAsm.Stmt := sequence [wipe .x19 .x21, leave]

/-- Descriptor body,len,type,out,outCap,work,workCap,maxBody,profile. Encodes the
uint24 header into private staging, invokes the ACTUAL typed decoder to validate
all vectors, rejects SNI on ClientHello emission, then commits bytes atomically.
Caller constructs bodies with the checked vector helper or typed Spec encoders.
Workspace uses the full uint24 length domain and is wiped on every processed exit. -/
def encode : Except String SAsm.Stmt := do
  program (.seq [.asm validate, .asm setup, .asm arguments, .call 0,
    .ite (.ne .x10 .x0) (.asm cleanup) (.asm empty),
    .asm (block [.ADD .x12 .x19 .x20, .LD .x11 .x12 440]),
    .ite (.ne .x11 .x0) (.asm (sequence [block [.ADDI .x10 .x0 7], cleanup])) (.asm empty),
    .asm (block [.ADDI .x11 .x9 4]), .asm (copy .x18 .x19 .x11),
    .asm (block [.ADDI .x10 .x0 0]), .asm cleanup]) [.asm (← Codec.decode)]

/-- a0 points to immutable 56 bytes: input,len,width(1/2/3),minimum,out,
outputCapacity,callerLimit. A single checked length vector, no stack/scratch.
No partial prefix on error, lengths validated BEFORE narrowing to bytes. -/
def vector : SAsm.Stmt := sequence [descriptor 56,
  block [.LD .x11 .x10 8, .LD .x12 .x10 16, .ADDI .x7 .x0 1], reject (.ltu .x12 .x7) 2,
  block [.ADDI .x7 .x0 3], reject (.ltu .x7 .x12) 2,
  block [.SLLI .x5 .x12 3, .ADDI .x7 .x0 1, .SLL .x7 .x7 .x5], reject (.geu .x11 .x7) 2,
  block [.LD .x7 .x10 24], reject (.ltu .x11 .x7) 2,
  block [.LD .x7 .x10 48], reject (.ltu .x7 .x11) 9,
  block [.ADD .x15 .x11 .x12, .LD .x7 .x10 40], reject (.ltu .x7 .x15) 5,
  spans 56 0 [variableSpan 0 8, ⟨field 32,register .x15⟩],
  block [.LD .x13 .x10 32, .LD .x14 .x10 0, .ADDI .x15 .x12 0],
  .loop (.ne .x15 .x0) (block [.ADDI .x15 .x15 (-1), .SLLI .x6 .x15 3,
    .SRL .x7 .x11 .x6, .SB .x13 .x7 0, .ADDI .x13 .x13 1]),
  copy .x13 .x14 .x11, finish 0]

end Libp2pAsm.Asm.Tls.Encode
