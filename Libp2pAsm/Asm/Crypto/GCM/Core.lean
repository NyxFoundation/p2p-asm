import Libp2pAsm.Asm.Crypto.GCM.GHash

namespace Libp2pAsm.Asm.Crypto.GCM
open Rv64
open AES (imm)

/-- Fixed workspace: AES core [0,1024), schedule [1024,1200), H,
J0 mask, accumulator, padded block; remaining 16 bytes are also wiped. -/
def workspaceBytes : Nat := 1280
def keyOffset : Nat := 1024
def hOffset : Nat := 1200
def maskOffset : Nat := 1216
def accOffset : Nat := 1232
def blockOffset : Nat := 1248

/-- All metadata resides in the caller's owned 128-byte stack frame. No
callee-saved registers hold temporary state, and no calls change ra. -/
def aesPointers : SAsm.Stmt := .block [
  .LD .x12 .x2 8, .ADDI .x10 .x12 (imm keyOffset),
  .ADDI .x11 .x12 (imm AES.stateOffset)]

def hashPointers : SAsm.Stmt := .block [
  .LD .x12 .x2 8, .ADDI .x10 .x12 (imm accOffset),
  .ADDI .x11 .x12 (imm hOffset), .ADDI .x12 .x12 (imm blockOffset)]

/-- Copy the 96-bit nonce; counter is a public LE64 metadata integer, emitted
as exactly four big-endian bytes. It is never used as an address. -/
def counterBlock : SAsm.Stmt := sequence [
  aesPointers, .block [.LD .x13 .x2 56], AES.copy .x11 .x13 12,
  .block ([.LD .x5 .x2 112] ++ (List.range 4).flatMap fun i =>
    [.SRLI .x6 .x5 (BitVec.ofNat 6 (8*(3-i))), .SB .x11 .x6 (imm (12+i))])]

def derive : SAsm.Stmt := sequence [
  .block [.LD .x10 .x2 0, .LD .x10 .x10 0, .LD .x12 .x2 8,
    .ADDI .x15 .x12 (imm keyOffset)], AES.expandCore,
  aesPointers, AES.wipe .x11 16, AES.encryptCore,
  .block [.ADDI .x13 .x12 (imm hOffset)], AES.copy .x13 .x11 16,
  .block [.ADDI .x5 .x0 1, .SD .x2 .x5 112], counterBlock, AES.encryptCore,
  .block [.ADDI .x13 .x12 (imm maskOffset)], AES.copy .x13 .x11 16,
  .block [.ADDI .x13 .x12 (imm accOffset)], AES.wipe .x13 16]

/-- Private mask is all ones on success, zero on authentication failure.
Both paths read every caller output byte and execute the same stores. No
unauthenticated plaintext is ever stored in caller output or private memory. -/
def xorCommit : SAsm.Stmt := sequence [
  .block [.LD .x28 .x2 16, .LD .x29 .x2 32, .LD .x14 .x2 24,
    .ADDI .x31 .x0 16, .LD .x13 .x2 40, .XORI .x7 .x13 (-1)],
  .ite (.ltu .x14 .x31) (.block [.ADDI .x31 .x14 0]) (.block []),
  .block [.ADDI .x14 .x31 0],
  .loop (.ne .x31 .x0) (.block [
    .LBU .x5 .x28 0, .LBU .x6 .x11 0, .XOR .x5 .x5 .x6,
    .AND .x5 .x5 .x13, .LBU .x6 .x29 0, .AND .x6 .x6 .x7,
    .OR .x5 .x5 .x6, .SB .x29 .x5 0,
    .ADDI .x28 .x28 1, .ADDI .x29 .x29 1, .ADDI .x11 .x11 1,
    .ADDI .x31 .x31 (-1)]),
  .block [.SD .x2 .x28 16, .SD .x2 .x29 32, .LD .x17 .x2 24,
    .SUB .x17 .x17 .x14, .SD .x2 .x17 24, .LD .x5 .x2 112,
    .ADDI .x5 .x5 1, .SD .x2 .x5 112]]

def ctr : SAsm.Stmt := sequence [
  .block [.ADDI .x5 .x0 2, .SD .x2 .x5 112, .LD .x17 .x2 88, .SD .x2 .x17 24,
    .LD .x5 .x2 64, .SD .x2 .x5 16, .LD .x5 .x2 72, .SD .x2 .x5 32],
  .loop (.ne .x17 .x0) (sequence [counterBlock, AES.encryptCore, xorCommit])]

/-- Copy only valid input bytes into a zero-filled 16-byte private block.
No read across the public input length, including partial final blocks. -/
def paddedBlock : SAsm.Stmt := sequence [
  hashPointers, AES.wipe .x12 16,
  .block [.LD .x28 .x2 96, .ADDI .x29 .x12 0, .LD .x14 .x2 104, .ADDI .x31 .x0 16],
  .ite (.ltu .x14 .x31) (.block [.ADDI .x31 .x14 0]) (.block []),
  .block [.SUB .x14 .x14 .x31, .SD .x2 .x14 104],
  .loop (.ne .x31 .x0) (.block [
    .LBU .x5 .x28 0, .SB .x29 .x5 0, .ADDI .x28 .x28 1,
    .ADDI .x29 .x29 1, .ADDI .x31 .x31 (-1)]),
  .block [.SD .x2 .x28 96]]

def hashBytes : SAsm.Stmt := sequence [
  .block [.LD .x17 .x2 104],
  .loop (.ne .x17 .x0) (sequence [paddedBlock, updateCore, .block [.LD .x17 .x2 104]])]

def authenticate (opening : Bool) : SAsm.Stmt := sequence [
  .block [.LD .x5 .x2 0, .LD .x6 .x5 32, .SD .x2 .x6 96,
    .LD .x6 .x2 80, .SD .x2 .x6 104], hashBytes,
  .block [.LD .x5 .x2 (if opening then 64 else 72), .SD .x2 .x5 96,
    .LD .x5 .x2 88, .SD .x2 .x5 104], hashBytes,
  hashPointers,
  .block ([.LD .x5 .x2 80, .SLLI .x5 .x5 3] ++ storeBE .x5 .x12 .x6 0 ++
    [.LD .x5 .x2 88, .SLLI .x5 .x5 3] ++ storeBE .x5 .x12 .x6 8),
  updateCore]

/-- Consume all sixteen tag bytes; status=6 and success mask=0 on mismatch.
SLTU and arithmetic declassify the return status without altering the trace. -/
def compareTag : SAsm.Stmt := sequence [
  .block [.LD .x12 .x2 8, .ADDI .x28 .x12 (imm accOffset),
    .ADDI .x29 .x12 (imm maskOffset), .LD .x30 .x2 64, .LD .x5 .x2 88,
    .ADD .x30 .x30 .x5, .ADDI .x31 .x0 16, .ADDI .x7 .x0 0],
  .loop (.ne .x31 .x0) (.block [
    .LBU .x5 .x28 0, .LBU .x6 .x29 0, .XOR .x5 .x5 .x6,
    .LBU .x6 .x30 0, .XOR .x5 .x5 .x6, .OR .x7 .x7 .x5,
    .ADDI .x28 .x28 1, .ADDI .x29 .x29 1, .ADDI .x30 .x30 1, .ADDI .x31 .x31 (-1)]),
  .block [.SLTU .x7 .x0 .x7, .ADDI .x5 .x7 (-1), .SD .x2 .x5 40,
    .SLLI .x5 .x7 1, .SLLI .x6 .x7 2, .ADD .x5 .x5 .x6, .SD .x2 .x5 120]]

def writeTag : SAsm.Stmt := sequence [
  .block [.LD .x12 .x2 8, .ADDI .x28 .x12 (imm accOffset),
    .ADDI .x29 .x12 (imm maskOffset), .LD .x30 .x2 72, .LD .x5 .x2 88,
    .ADD .x30 .x30 .x5, .ADDI .x31 .x0 16],
  .loop (.ne .x31 .x0) (.block [
    .LBU .x5 .x28 0, .LBU .x6 .x29 0, .XOR .x5 .x5 .x6, .SB .x30 .x5 0,
    .ADDI .x28 .x28 1, .ADDI .x29 .x29 1, .ADDI .x30 .x30 1, .ADDI .x31 .x31 (-1)])]

end Libp2pAsm.Asm.Crypto.GCM
