import Libp2pAsm.Asm.Crypto.Quic.Common
import Libp2pAsm.Asm.Crypto.GCM.Api

namespace Libp2pAsm.Asm.Crypto.Quic.Retry
open Rv64 Util Link

def workspaceBytes (cid retry : Nat) : Nat := 1441+cid+retry
def stackBytes : Nat := 240

def validate (checking : Bool) : SAsm.Stmt := sequence [descriptor 72,
  block [.LD .x11 .x10 8, .ADDI .x7 .x0 20], reject (.ltu .x7 .x11) 1,
  block (load .x7 (2^61-22) ++ [.LD .x12 .x10 24, .LD .x13 .x10 64]),
  reject (.ltu .x7 .x13) 1, reject (.ltu .x13 .x12) 1,
  (if checking then sequence [block [.ADDI .x7 .x0 16], reject (.ltu .x12 .x7) 1,
    block [.ADDI .x12 .x12 (-16)]] else sequence [
    block [.LD .x13 .x10 40], capacity .x13 16]),
  block [.ADD .x17 .x11 .x12, .ADDI .x17 .x17 1441, .LD .x13 .x10 56],
  reject (.ltu .x13 .x17) 5, alignedField 48,
  spans 72 stackBytes ([variableSpan 0 8, variableSpan 16 24, ⟨field 48, register .x17⟩] ++
    if checking then [] else [fixed 32 16])]

def setup : SAsm.Stmt := sequence [enter, block [
  .LD .x8 .x10 0, .LD .x9 .x10 8, .LD .x18 .x10 16, .ADDI .x19 .x12 0,
  .LD .x20 .x10 32, .LD .x22 .x10 48, .ADDI .x23 .x17 0]]

def pseudo : SAsm.Stmt := sequence [
  writeBytes .x22 0 [0xbe,0x0c,0x69,0x0b,0x9f,0x66,0x57,0x5a,0x1d,0x76,0x6b,0x54,0xe3,0x68,0xc8,0x4e],
  writeBytes .x22 16 [0x46,0x15,0x99,0xd3,0x5d,0x63,0x2b,0xf2,0x23,0x98,0x25,0xbb],
  block [.SB .x22 .x9 1440, .ADDI .x11 .x22 1441], copy .x11 .x8 .x9,
  block [.ADD .x11 .x11 .x9], copy .x11 .x18 .x19]

def gcmArgs : SAsm.Stmt := block [
  .SD .x22 .x22 48, .ADDI .x5 .x0 16, .SD .x22 .x5 56,
  .ADDI .x5 .x22 16, .SD .x22 .x5 64, .ADDI .x5 .x0 12, .SD .x22 .x5 72,
  .ADDI .x5 .x22 1440, .SD .x22 .x5 80, .ADD .x5 .x9 .x19, .ADDI .x5 .x5 1,
  .SD .x22 .x5 88, .SD .x22 .x0 96, .SD .x22 .x0 104,
  .ADDI .x5 .x22 32, .SD .x22 .x5 112, .ADDI .x5 .x0 16, .SD .x22 .x5 120,
  .ADDI .x5 .x22 160, .SD .x22 .x5 128, .ADDI .x5 .x0 1280, .SD .x22 .x5 136,
  .ADDI .x10 .x22 48]

def compareTag : SAsm.Stmt := sequence [
  block [.ADDI .x11 .x22 32, .ADD .x12 .x18 .x19, .ADDI .x13 .x0 16, .ADDI .x14 .x0 0],
  .loop (.ne .x13 .x0) (block [.LBU .x5 .x11 0, .LBU .x6 .x12 0,
    .XOR .x5 .x5 .x6, .OR .x14 .x14 .x5, .ADDI .x11 .x11 1,
    .ADDI .x12 .x12 1, .ADDI .x13 .x13 (-1)]),
  block [.SLTU .x27 .x0 .x14, .ADDI .x5 .x0 6, .MUL .x27 .x27 .x5]]

def cleanup : SAsm.Stmt := sequence [wipe .x22 .x23,
  block [.ADDI .x11 .x2 (-128), .ADDI .x12 .x0 128], wipe .x11 .x12,
  block [.ADDI .x10 .x27 0], leave]

/-- LE64 descriptor: ODCID pointer/length, Retry pointer/length, output/capacity,
workspace/capacity, configured packet limit. Generate consumes Retry WITHOUT
tag and outputs 16 tag bytes. Check consumes Retry WITH tag and does not access
the output buffer; capacity is ignored. Header/Retry parsing remains caller-owned.
Checks all public metadata/spans before payload reads; exact workspace requirement
1441+ODCIDlen+RetryWithoutTagLen. Owns/wipes exactly 240 stack bytes and workspace.
Status 0 success, 1 length/limit, 4 span, 5 capacity, 6 authentication failure.
All tag bytes are compared without data-dependent branches/addresses. -/
def retry (checking : Bool) : Except String SAsm.Stmt := program (.seq [
  .asm (validate checking), .asm setup, .asm pseudo, .asm gcmArgs, .call 0,
  .asm (if checking then compareTag else sequence [
    block [.ADDI .x11 .x22 32, .ADDI .x12 .x0 16], copy .x20 .x11 .x12,
    block [.ADDI .x27 .x0 0]]), .asm cleanup]) [.asm GCM.seal]

def generate := retry false
def check := retry true

end Libp2pAsm.Asm.Crypto.Quic.Retry
