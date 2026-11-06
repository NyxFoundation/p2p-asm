import Libp2pAsm.Asm.Tls.Common
import Libp2pAsm.Asm.Crypto.HKDF

namespace Libp2pAsm.Asm.Tls.Schedule
open Rv64 Crypto.Util Crypto.Link

inductive Mode where | handshake | application | finished | hash | messageHash deriving BEq
def outputBytes : Mode → Nat
  | .handshake => 224 | .application | .finished => 64 | .hash => 32 | .messageHash => 36
def workspaceBytes : Nat := 1536
def stackBytes : Nat := 528
def transcript (mode : Mode) : Bool := mode == .hash || mode == .messageHash

def validate (mode : Mode) : SAsm.Stmt := sequence [descriptor 80,
  block [.LD .x11 .x10 8, .LD .x12 .x10 24],
  (if transcript mode then sequence [
    reject (.ne .x12 .x0) 2, block [.SRLI .x5 .x11 61], reject (.ne .x5 .x0) 2,
    block [.LD .x7 .x10 72], reject (.ltu .x7 .x11) 9]
  else sequence [block [.ADDI .x7 .x0 32],
    reject (.ne .x11 .x7) 2, reject (.ne .x12 .x7) 2]),
  block [.LD .x12 .x10 40], capacity .x12 (outputBytes mode),
  block [.LD .x12 .x10 56], capacity .x12 workspaceBytes,
  alignedField 48, alignedField 64,
  spans 80 stackBytes [variableSpan 0 8, variableSpan 16 24,
    fixed 32 (outputBytes mode), fixed 48 workspaceBytes, fixed 64 512]]

def setup : SAsm.Stmt := sequence [enter, block [
  .LD .x8 .x10 0, .LD .x9 .x10 8, .LD .x18 .x10 16,
  .LD .x19 .x10 48, .LD .x20 .x10 64, .LD .x21 .x10 32,
  .ADDI .x2 .x2 (-16), .SD .x2 .x20 0, .SD .x2 .x0 8]]

def cleanup : SAsm.Stmt := sequence [
  block [.ADDI .x11 .x0 (imm workspaceBytes)], wipe .x19 .x11,
  block [.SD .x2 .x0 0, .SD .x2 .x0 8, .ADDI .x2 .x2 16], leave]

def checkedCall (target : Nat) : Part := .seq [.call target,
  .ite (.ne .x10 .x0) (.seq [.asm (block [.ADDI .x10 .x0 8]), .asm cleanup]) (.asm empty)]

def workAt (offset : Nat) : Expr := fun r => [.ADDI r .x19 (imm offset)]
def labelPrefix (label : String) (contextLength : Nat) : List Nat :=
  [0,32,6+label.toUTF8.size,116,108,115,49,51,32] ++
  label.toUTF8.data.toList.map UInt8.toNat ++ [contextLength]

def expand (source : Expr) (label : String) (context : Option Expr) (offset : Nat) : Part :=
  let head := labelPrefix label (if context.isSome then 32 else 0)
  .seq ([.asm (writeBytes .x19 256 head)] ++
    (match context with
    | none => []
    | some src => [.asm (block (src .x12 ++ [.ADDI .x13 .x19 (imm (256+head.length)),
        .ADDI .x14 .x0 32])), .asm (copy .x13 .x12 .x14)]) ++
    [.asm (block (source .x10 ++ [.ADDI .x11 .x0 32, .ADDI .x12 .x19 256,
      .ADDI .x13 .x0 (imm (head.length + if context.isSome then 32 else 0)),
      .ADDI .x14 .x19 (imm offset), .ADDI .x15 .x0 32,
      .ADDI .x16 .x19 512, .ADDI .x17 .x0 1024])), checkedCall 1])

def extract (salt ikm : Expr) (offset : Nat) : Part := .seq [
  .asm (block (salt .x10 ++ ikm .x12 ++ [.ADDI .x11 .x0 32, .ADDI .x13 .x0 32,
    .ADDI .x14 .x19 (imm offset), .ADDI .x15 .x19 512,
    .ADDI .x16 .x0 1024, .ADDI .x17 .x20 0])), checkedCall 0]

def digest (input length : Expr) (offset : Nat) : Part := .seq [
  .asm (block (input .x10 ++ length .x11 ++ [.ADDI .x12 .x19 (imm offset),
    .ADDI .x13 .x19 512, .ADDI .x14 .x0 1024, .ADDI .x15 .x20 0])), checkedCall 2]

def handshake : Part := .seq [
  .asm (block [.ADDI .x12 .x19 384, .ADDI .x13 .x0 32]), .asm (wipe .x12 .x13),
  digest (literal 0) (literal 0) 416,
  extract (workAt 384) (workAt 384) 0,
  expand (workAt 0) "derived" (some (workAt 416)) 32,
  extract (workAt 32) (register .x8) 64,
  expand (workAt 64) "c hs traffic" (some (register .x18)) 96,
  expand (workAt 64) "s hs traffic" (some (register .x18)) 128,
  expand (workAt 64) "derived" (some (workAt 416)) 160,
  extract (workAt 160) (workAt 384) 192]

def work (mode : Mode) : Part := match mode with
  | .handshake => handshake
  | .application => .seq [
    expand (register .x8) "c ap traffic" (some (register .x18)) 0,
    expand (register .x8) "s ap traffic" (some (register .x18)) 32]
  | .finished => .seq [expand (register .x8) "finished" none 0,
    extract (workAt 0) (register .x18) 32]
  | .hash => digest (register .x8) (register .x9) 0
  | .messageHash => .seq [.asm (writeBytes .x19 0 [254,0,0,32]),
    digest (register .x8) (register .x9) 4]

/-- a0 points to 80 immutable bytes: inputA,lenA,inputB,lenB,out,outCap,
work,workCap,SHA256table,transcriptLimit. Stage privately, then publish.
Success clears all 1536 work bytes and 528 stack bytes (maximum depth;
shallower paths only touch/wipe their actual frames). Preflight errors write
nothing. No crypto secret is read before complete metadata validation. -/
def derive (mode : Mode) : Except String SAsm.Stmt := do
  program (.seq [.asm (validate mode), .asm setup, work mode,
    .asm (block [.ADDI .x11 .x0 (imm (outputBytes mode))]), .asm (copy .x21 .x19 .x11),
    .asm (block [.ADDI .x10 .x0 0]), .asm cleanup])
    [ .asm (← Crypto.HMAC.sha256), .asm (← Crypto.HKDF.expand), .asm (Crypto.Whole.body .sha256)]

end Libp2pAsm.Asm.Tls.Schedule
