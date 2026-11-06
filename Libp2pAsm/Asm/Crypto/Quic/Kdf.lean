import Libp2pAsm.Asm.Crypto.Quic.Common
import Libp2pAsm.Asm.Crypto.HKDF

namespace Libp2pAsm.Asm.Crypto.Quic.Kdf
open Rv64 Util Link

inductive Mode where | initial | keys | update deriving BEq
def outputBytes : Mode → Nat | .initial => 184 | .keys => 44 | .update => 60
def workspaceBytes : Nat := 1280
def stackBytes : Nat := 528

/-- Static empty-context TLS HkdfLabel, independently encoded at generation time.
Bytes are stored by ordinary RV64 instructions before the real HKDF ASM call. -/
def labelBytes (label : String) (n : Nat) : List Nat :=
  [n/256,n%256,6+label.toUTF8.size] ++ [116,108,115,49,51,32] ++
    (label.toUTF8.data.toList.map UInt8.toNat) ++ [0]

def validate (mode : Mode) : SAsm.Stmt := sequence [descriptor 56,
  block [.LD .x11 .x10 8, .ADDI .x7 .x0 (if mode == .initial then 20 else 32)],
  (if mode == .initial then reject (.ltu .x7 .x11) 1 else reject (.ne .x7 .x11) 1),
  block [.LD .x12 .x10 24], capacity .x12 (outputBytes mode),
  block [.LD .x12 .x10 40], capacity .x12 workspaceBytes,
  alignedField 32, alignedField 48,
  spans 56 stackBytes [variableSpan 0 8, fixed 16 (outputBytes mode), fixed 32 workspaceBytes, fixed 48 512]]

def setup : SAsm.Stmt := sequence [enter, block [
  .LD .x8 .x10 0, .LD .x9 .x10 8, .LD .x18 .x10 16, .LD .x19 .x10 32,
  .LD .x20 .x10 48, .ADDI .x2 .x2 (-16), .SD .x2 .x20 0, .SD .x2 .x0 8]]

/-- source is independent of all caller-saved temporaries. -/
def expand (source : Expr) (label : String) (n offset : Nat) : Part := .seq [
  .asm (writeBytes .x19 224 (labelBytes label n)),
  .asm (block (source .x10 ++ [.ADDI .x11 .x0 32, .ADDI .x12 .x19 224,
    .ADDI .x13 .x0 (imm (labelBytes label n).length), .ADDI .x14 .x19 (imm offset),
    .ADDI .x15 .x0 (imm n), .ADDI .x16 .x19 256, .ADDI .x17 .x0 1024])), .call 1]

def workAt (offset : Nat) : Expr := fun r => [.ADDI r .x19 (imm offset)]
def keys (source : Expr) (offset : Nat) (hp : Bool) : List Part :=
  [expand source "quic key" 16 offset, expand source "quic iv" 12 (offset+16)] ++
    if hp then [expand source "quic hp" 16 (offset+28)] else []

def initial : Part := .seq ([
  .asm (writeBytes .x19 192 [0x38,0x76,0x2c,0xf7,0xf5,0x59,0x34,0xb3,0x4d,0x17,
    0x9a,0xe6,0xa4,0xc8,0x0c,0xad,0xcc,0xbb,0x7f,0x0a]),
  .asm (block [.ADDI .x10 .x19 192, .ADDI .x11 .x0 20, .ADDI .x12 .x8 0,
    .ADDI .x13 .x9 0, .ADDI .x14 .x19 0, .ADDI .x15 .x19 256,
    .ADDI .x16 .x0 1024, .ADDI .x17 .x20 0]), .call 0,
  expand (workAt 0) "client in" 32 32, expand (workAt 0) "server in" 32 64] ++
  keys (workAt 32) 96 true ++ keys (workAt 64) 140 true)

def finishKdf (n : Nat) : SAsm.Stmt := sequence [
  block [.ADDI .x11 .x0 (imm n)], copy .x18 .x19 .x11,
  block [.ADDI .x11 .x0 (imm workspaceBytes)], wipe .x19 .x11,
  block [.SD .x2 .x0 0, .SD .x2 .x0 8, .ADDI .x2 .x2 16, .ADDI .x10 .x0 0], leave]

/-- Immutable 56-byte descriptor: input, input length, output, output capacity,
work, work capacity, SHA-256 table. All external accessed spans must be disjoint.
Output: initial=secret32/client32/server32/client44/server44, keys=44, update=60.
All metadata checked before key reads; owns/wipes 1280 workspace and 528 stack.
Real frozen HKDF/HMAC/SHA RV64 code, using checked PIC local calls. -/
def derive (mode : Mode) : Except String SAsm.Stmt := do
  let body := match mode with
    | .initial => initial
    | .keys => .seq (keys (register .x8) 0 true)
    | .update => .seq ([expand (register .x8) "quic ku" 32 0] ++ keys (workAt 0) 32 false)
  program (.seq [.asm (validate mode), .asm setup, body, .asm (finishKdf (outputBytes mode))])
    [.asm (← HKDF.extract), .asm (← HKDF.expand)]

end Libp2pAsm.Asm.Crypto.Quic.Kdf
