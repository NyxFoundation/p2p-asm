import Libp2pAsm.Asm.Crypto.Quic.Number
import Libp2pAsm.Asm.Crypto.AES.Api
import Libp2pAsm.Asm.Crypto.GCM.Api

namespace Libp2pAsm.Asm.Crypto.Quic.Packet
open Rv64 Util Link

def workspaceBytes (n : Nat) : Nat := 1616+n
def stackBytes : Nat := 240

def lengths (opening : Bool) : SAsm.Stmt := sequence [descriptor 88,
  block (load .x7 (2^62) ++ [.LD .x13 .x10 32]),
  (if opening then reject (.ltu .x7 .x13) 2 else reject (.geu .x13 .x7) 2),
  block (load .x7 (2^36-32) ++ [.LD .x11 .x10 16, .LD .x12 .x10 24, .LD .x15 .x10 72]),
  reject (.ltu .x7 .x15) 1, reject (.ltu .x15 .x11) 1,
  reject (.eq .x12 .x0) 3, reject (.geu .x12 .x11) 3,
  block [.ADDI .x14 .x11 (if opening then 0 else 16), .ADDI .x5 .x12 20],
  reject (.ltu .x14 .x5) 7,
  block [.LD .x5 .x10 48], reject (.ltu .x5 .x14) 5,
  block [.ADDI .x17 .x11 1616, .LD .x5 .x10 64], reject (.ltu .x5 .x17) 5,
  alignedField 56,
  spans 88 stackBytes [fixed 0 44, variableSpan 8 16,
    ⟨field 40, register .x14⟩, ⟨field 56, register .x17⟩]]

/-- All addresses/capacities are checked before this public header read. -/
def sealHeader : SAsm.Stmt := sequence [
  block [.LD .x15 .x10 8, .LBU .x5 .x15 0, .ANDI .x5 .x5 3,
    .ADDI .x5 .x5 1, .ADD .x5 .x5 .x12, .LD .x16 .x10 80],
  reject (.ne .x5 .x16) 3, reject (.ltu .x11 .x16) 3]

def setup : SAsm.Stmt := sequence [enter, block [
  .LD .x8 .x10 0, .LD .x9 .x10 8, .LD .x18 .x10 16, .LD .x19 .x10 24,
  .LD .x20 .x10 32, .LD .x21 .x10 40, .LD .x22 .x10 56, .ADDI .x23 .x17 0,
  .ADDI .x24 .x22 1600, .LD .x25 .x10 80, .ADDI .x27 .x0 0]]

def cleanup : SAsm.Stmt := sequence [wipe .x22 .x23,
  block [.ADDI .x11 .x2 (-128), .ADDI .x12 .x0 128], wipe .x11 .x12,
  block [.ADDI .x10 .x27 0], leave]

/-- Calls preserve saved registers; schedule and mask have separate scratch spans. -/
def hp (opening : Bool) : Part := .seq [
  .asm (block [.ADDI .x10 .x8 28, .ADDI .x11 .x0 16, .ADDI .x12 .x22 112,
    .ADDI .x13 .x0 176, .ADDI .x14 .x22 320, .ADDI .x15 .x0 1024]), .call 0,
  .asm (block [.ADDI .x10 .x22 112,
    .ADD .x11 (if opening then .x9 else .x24) .x19, .ADDI .x11 .x11 4,
    .ADDI .x12 .x0 16, .ADDI .x13 .x22 288, .ADDI .x14 .x0 5,
    .ADDI .x15 .x22 320, .ADDI .x16 .x0 1024]), .call 1]

def firstByte : SAsm.Stmt := sequence [
  block [.LBU .x5 .x24 0, .LBU .x6 .x22 288, .ANDI .x7 .x5 128],
  .ite (.eq .x7 .x0) (block [.ANDI .x6 .x6 31]) (block [.ANDI .x6 .x6 15]),
  block [.XOR .x5 .x5 .x6, .SB .x24 .x5 0]]

def maskNumber : SAsm.Stmt := sequence [
  block [.ADD .x11 .x24 .x19, .ADDI .x12 .x22 289, .ADDI .x13 .x26 0],
  .loop (.ne .x13 .x0) (block [.LBU .x5 .x11 0, .LBU .x6 .x12 0,
    .XOR .x5 .x5 .x6, .SB .x11 .x5 0, .ADDI .x11 .x11 1,
    .ADDI .x12 .x12 1, .ADDI .x13 .x13 (-1)])]

def sealStage : SAsm.Stmt := sequence [copy .x24 .x9 .x25,
  block [.SUB .x26 .x25 .x19, .ADDI .x13 .x20 0, .ADD .x11 .x24 .x25,
    .ADDI .x12 .x26 0],
  .loop (.ne .x12 .x0) (block [.ADDI .x11 .x11 (-1), .SB .x11 .x13 0,
    .SRLI .x13 .x13 8, .ADDI .x12 .x12 (-1)])]

def openStage : SAsm.Stmt := sequence [copy .x24 .x9 .x18, firstByte,
  block [.LBU .x26 .x24 0, .ANDI .x26 .x26 3, .ADDI .x26 .x26 1,
    .ADD .x25 .x19 .x26], maskNumber,
  block [.ADD .x15 .x24 .x19, .ADDI .x16 .x26 0, .ADDI .x12 .x0 0],
  .loop (.ne .x16 .x0) (block [.LBU .x5 .x15 0, .SLLI .x12 .x12 8,
    .OR .x12 .x12 .x5, .ADDI .x15 .x15 1, .ADDI .x16 .x16 (-1)]),
  block [.ADDI .x11 .x20 0, .ADDI .x13 .x26 0], reconstructBody,
  block [.SRLI .x5 .x14 62],
  .ite (.ne .x5 .x0) (sequence [block [.ADDI .x27 .x0 2], cleanup]) empty,
  block [.ADDI .x20 .x14 0]]

/-- Exact frozen GCM descriptor at work+16; key and nonce lengths fixed,
AAD is staged unprotected header; input is immutable caller payload. -/
def gcmArgs (opening : Bool) : SAsm.Stmt := sequence [
  block [.ADDI .x11 .x8 16, .ADDI .x12 .x20 0, .ADDI .x13 .x22 0], nonceBody,
  block [.SD .x22 .x8 16, .ADDI .x5 .x0 16, .SD .x22 .x5 24,
    .SD .x22 .x22 32, .ADDI .x5 .x0 12, .SD .x22 .x5 40,
    .SD .x22 .x24 48, .SD .x22 .x25 56, .ADD .x5 .x9 .x25, .SD .x22 .x5 64,
    .SUB .x5 .x18 .x25, .SD .x22 .x5 72, .ADD .x5 .x24 .x25, .SD .x22 .x5 80,
    .SUB .x5 .x18 .x25, .ADDI .x5 .x5 (if opening then -16 else 16), .SD .x22 .x5 88,
    .ADDI .x5 .x22 320, .SD .x22 .x5 96, .ADDI .x5 .x0 1280, .SD .x22 .x5 104,
    .ADDI .x10 .x22 16]]

/-- Masked whole-output commit includes authenticated PN/header metadata.
Valid and invalid GCM tags run the same commit addresses/instructions. -/
def commit (opening : Bool) : SAsm.Stmt := sequence [
  (if opening then sequence [block [.ADDI .x11 .x24 (-16)],
    storeLE .x11 .x20 0, storeLE .x11 .x25 8] else block [.ADDI .x11 .x24 0]),
  block [.ADDI .x12 .x21 0, .ADDI .x13 .x18 (if opening then 0 else 16),
    .SLTU .x30 .x0 .x27, .ADDI .x30 .x30 (-1), .XORI .x31 .x30 (-1)],
  .loop (.ne .x13 .x0) (block [.LBU .x5 .x11 0, .LBU .x6 .x12 0,
    .AND .x5 .x5 .x30, .AND .x6 .x6 .x31, .OR .x5 .x5 .x6, .SB .x12 .x5 0,
    .ADDI .x11 .x11 1, .ADDI .x12 .x12 1, .ADDI .x13 .x13 (-1)])]

/-- Immutable LE64 descriptor (88 bytes): packed key44 pointer, input pointer,
input length, PN offset, full PN(seal)/expected PN(open), output pointer/capacity,
workspace pointer/capacity, configured packet limit, unprotected header length.
Open requires header length slot=0, returns LE64 PN || LE64 header length ||
unprotected header || plaintext (input length bytes total). Seal returns the
protected packet (input length+16). No output is published on any failure.
HP sample starts at PN offset+4, checked before any sample or secret read.
Metadata failures touch no output/work/stack. All processed calls wipe work
[0,1616+inputLength) and exactly 240 owned stack bytes. Code must be disjoint.
Statuses: 1 length/limit, 2 PN, 3 header, 4 span, 5 capacity, 6 tag, 7 sample.
Public parsing of v1 Initial/Handshake/short headers and PN spaces is caller-owned. -/
def packet (opening : Bool) : Except String SAsm.Stmt :=
  program (.seq ([.asm (lengths opening), .asm (if opening then sequence [
    block [.LD .x5 .x10 80], reject (.ne .x5 .x0) 3] else sealHeader), .asm setup] ++
    (if opening then [hp true, .asm openStage] else [.asm sealStage]) ++
    [.asm (gcmArgs opening), .call 2, .asm (block [.ADDI .x27 .x10 0])] ++
    (if opening then [] else [hp false, .asm firstByte, .asm maskNumber]) ++
    [.asm (commit opening), .asm cleanup]))
    [.asm AES.expand, .asm AES.headerProtection, .asm (GCM.aead opening)]

def protect := packet false
def unprotect := packet true

end Libp2pAsm.Asm.Crypto.Quic.Packet
