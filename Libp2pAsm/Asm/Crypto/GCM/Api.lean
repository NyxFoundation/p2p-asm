import Libp2pAsm.Asm.Crypto.GCM.Core

namespace Libp2pAsm.Asm.Crypto.GCM
open Rv64
open AES (imm)

/-- Status: 0 success; 1 key length; 2 nonce length; 3 short ciphertext;
4 plaintext/counter bound; 5 AAD bound; 6 authentication; 7 output capacity;
8 workspace capacity. Malformed crypto and resource errors are distinct. -/
def validate (opening : Bool) : SAsm.Stmt := sequence [
  .block [.LD .x5 .x10 8, .ADDI .x6 .x0 16], AES.reject (.ne .x5 .x6) 1,
  .block [.LD .x5 .x10 24, .ADDI .x6 .x0 12], AES.reject (.ne .x5 .x6) 2,
  .block [.LD .x6 .x10 56],
  (if opening then sequence [
    .block [.ADDI .x5 .x0 16], AES.reject (.ltu .x6 .x5) 3,
    .block [.ADDI .x6 .x6 (-16)]] else .block []),
  .block [.ADDI .x7 .x0 1, .SLLI .x7 .x7 36, .ADDI .x7 .x7 (-32)],
  AES.reject (.ltu .x7 .x6) 4,
  .block [.LD .x5 .x10 40, .ADDI .x7 .x0 (-1), .SRLI .x7 .x7 3],
  AES.reject (.ltu .x7 .x5) 5,
  .block [.LD .x7 .x10 72, .ADDI .x5 .x6 (if opening then 0 else 16)],
  AES.reject (.ltu .x7 .x5) 7,
  .block [.LD .x7 .x10 88, .ADDI .x5 .x0 (imm workspaceBytes)],
  AES.reject (.ltu .x7 .x5) 8]

/-- Validation leaves the checked message length in x6. Initialize every
owned frame slot; save descriptor/public pointers and lengths only. -/
def enter : SAsm.Stmt := .block <|
  [.ADDI .x2 .x2 (-128)] ++ (List.range 16).map (fun i => LeanAsm.Rv64.Instr.SD .x2 .x0 (imm (8*i))) ++
  [.SD .x2 .x10 0, .SD .x2 .x6 88, .LD .x5 .x10 80, .SD .x2 .x5 8,
   .LD .x5 .x10 16, .SD .x2 .x5 56, .LD .x5 .x10 48, .SD .x2 .x5 64,
   .LD .x5 .x10 64, .SD .x2 .x5 72, .LD .x5 .x10 40, .SD .x2 .x5 80,
   .ADDI .x5 .x0 (-1), .SD .x2 .x5 40]

def leave : SAsm.Stmt := sequence [
  .block [.LD .x12 .x2 8], AES.wipe .x12 workspaceBytes,
  .block ([.LD .x10 .x2 120] ++
    (List.range 16).map (fun i => LeanAsm.Rv64.Instr.SD .x2 .x0 (imm (8*i))) ++
    [.ADDI .x2 .x2 128] ++ AES.clearRegs.map (fun r => LeanAsm.Rv64.Instr.ADDI r .x0 0)), .ret]

/-- AES-128-GCM leaf ABI: a0 points to an 8-aligned immutable 96-byte descriptor:
LE64 slots key pointer, key length, nonce pointer, nonce length, AAD pointer,
AAD length, input pointer, input length, output pointer, output capacity,
workspace pointer, workspace capacity. Open input is ciphertext || 16-byte tag.
Seal output has inputLength+16 bytes; open output has inputLength-16 bytes.
Internal pointers are RV64 addresses, not network integers.

Preconditions: descriptor, key, nonce, AAD, input, output, 8-aligned workspace,
128 owned bytes below 16-aligned sp, and code are valid nonwrapping disjoint
ranges. Zero-length payload pointers need not be dereferenceable. Output and
workspace/frame are writable; output is also readable for masked commit.
Only the used output prefix, first 1280 workspace bytes and frame are accessed.
No heap allocation, protocol-sized hidden limit, or external calls. All input
length/capacity checks precede payload reads, subtraction (except checked open
length), shifts, output writes and frame acquisition. Error validation writes
no memory. GCM's normative limits ensure counter and bit-length fields fit.

ra/sp/gp/tp and s0..s11 preserved. All other caller-saved registers cleared,
except a0=status. Workspace (including expanded key) and frame are zeroized on
success and authentication failure. Open authenticates first, compares every
tag byte, then performs CTR with branchless masked output commit: a failed tag
leaves every caller output byte unchanged. Plaintext exists transiently only in
registers until masked. Trace noninterference is tested, not universally proved.
Nonce uniqueness across seals is the caller's protocol-level obligation.
-/
def aead (opening : Bool) : SAsm.Stmt := sequence [
  validate opening, enter, derive,
  (if opening then sequence [authenticate true, compareTag, ctr]
   else sequence [ctr, authenticate false, writeTag]), leave]

def «seal» : SAsm.Stmt := aead false
def «open» : SAsm.Stmt := aead true

end Libp2pAsm.Asm.Crypto.GCM
