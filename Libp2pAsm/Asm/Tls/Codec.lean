import Libp2pAsm.Asm.Tls.Profile

namespace Libp2pAsm.Asm.Tls.Codec
open Rv64 Crypto.Util Crypto.Link Cursor

/-- Descriptor: input,len,out,outCap,work,workCap,maxBody,libp2pProfile.
All buffer capacity and separation checks precede input reads. Metadata errors
leave output, scratch and stack unchanged. Mapping is a caller obligation. -/
def validate : SAsm.Stmt := sequence [descriptor 64,
  block [.LD .x11 .x10 24], capacity .x11 outputBytes,
  block [.LD .x11 .x10 40], capacity .x11 workspaceBytes,
  alignedField 32, alignedField 16,
  block [.LD .x11 .x10 56, .ADDI .x7 .x0 1], reject (.ltu .x7 .x11) 2,
  spans 64 stackBytes [variableSpan 0 8, fixed 16 outputBytes, fixed 32 workspaceBytes]]

/-- Outer header reads occur before entering/clearing the workspace. -/
def header : SAsm.Stmt := sequence [
  block [.LD .x11 .x10 8, .ADDI .x7 .x0 4], reject (.ltu .x11 .x7) 1,
  block [.LD .x12 .x10 0, .LBU .x13 .x12 0, .LBU .x14 .x12 1,
    .SLLI .x14 .x14 8, .LBU .x6 .x12 2, .OR .x14 .x14 .x6,
    .SLLI .x14 .x14 8, .LBU .x6 .x12 3, .OR .x14 .x14 .x6,
    .LD .x7 .x10 48], reject (.ltu .x7 .x14) 9,
  block [.ADDI .x11 .x11 (-4)], reject (.ltu .x11 .x14) 1]

def setup : SAsm.Stmt := sequence [enter, block [
  .ADDI .x27 .x2 0, .LD .x8 .x10 0, .ADDI .x9 .x0 4, .ADDI .x18 .x14 4,
  .ADDI .x21 .x18 0, .LD .x19 .x10 32, .LD .x20 .x10 16, .LD .x26 .x10 56],
  block (load .x11 workspaceBytes), wipe .x19 .x11,
  block [.ADDI .x12 .x27 (-128), .ADDI .x11 .x0 128], wipe .x12 .x11,
  put 0 .x13, put 1 .x21]

def dispatch : Part := .seq [
  slotEq 0 1 (.seq [.asm (set 3 8), invoke 0]),
  slotEq 0 2 (.seq [.asm (set 3 3), invoke 0]),
  slotEq 0 8 (.seq [.asm (set 3 9), invoke 1]),
  slotEq 0 13 (.seq [.asm (set 3 1), invoke 2]),
  slotEq 0 11 (.seq [.asm (set 3 5), invoke 3]),
  slotEq 0 15 (.seq [.asm (set 3 5), invoke 4]),
  slotEq 0 20 (invoke 5), slotEq 0 4 (.seq [.asm (set 3 1), invoke 6]),
  .asm (get 0 .x14), .asm (block [.ADDI .x15 .x0 0]),
  .seq ([1,2,8,13,11,15,20,4].map fun n => eqConst .x14 n (.asm (block [.ADDI .x15 .x0 1]))),
  .asm (guard (.eq .x15 .x0) 3)]

def decode : Except String SAsm.Stmt := program (.seq [
  .asm validate, .asm header, .asm setup, dispatch,
  when (.ne .x26 .x0) (invoke 17),
  .asm (block [.ADDI .x11 .x0 512]), .asm (copy .x20 .x19 .x11),
  .asm (block [.ADDI .x10 .x0 0]), .asm cleanup])
  [Messages.hello, Messages.encryptedExtensions, Messages.certificateRequest,
   Messages.certificate, Messages.certificateVerify, Messages.finished, Messages.ticket,
   Extensions.scan, Extensions.entry, Extensions.versions, Extensions.offerWords,
   Extensions.shares, Extensions.alpn, Extensions.cookie, Messages.certificateEntry,
   Extensions.shareEntry, Extensions.nameEntry, Profile.validate]

/-- a0=isRecord (0 or 1), a1=handshakeType. No memory or stack access.
The transport MUST call this with the actual envelope classification. -/
def admitQuic : SAsm.Stmt := sequence [
  reject (.ne .x10 .x0) 3, block [.ADDI .x7 .x0 24], reject (.eq .x11 .x7) 3, finish 0]

end Libp2pAsm.Asm.Tls.Codec
