import Libp2pAsm.Asm.Identity.Certificate.IssueCommon

namespace Libp2pAsm.Asm.Identity.Certificate.Issue
open Rv64 Crypto.Util Crypto.Link
open Crypto.Curve25519 (ptr)

/-- Construction cursor s10; length s9; source s8. All DER lengths/public
signatures here are explicitly declassified outputs of the signing primitives. -/
def startBody : Part := .asm (block (ptr .x26 .x9 2560))

def literal (bytes : List UInt8) : Part := .asm (sequence [
  Crypto.Quic.writeBytes .x26 0 (bytes.map UInt8.toNat),
  block [.ADDI .x26 .x26 (imm bytes.length)]])

def append (source : Nat) (length : List Instr) : Part := .asm (sequence [
  block (ptr .x24 .x9 source ++ length), copy .x26 .x24 .x25,
  block [.ADD .x26 .x26 .x25]])

def header (tag : Nat) (length : List Instr) : Part := .seq [
  .asm (block (length ++ [.ADDI .x10 .x0 (imm tag), .ADDI .x11 .x25 0,
    .ADDI .x12 .x26 0, .ADDI .x13 .x0 10])), checked 7 30,
  .asm (block [.ADD .x26 .x26 .x11])]

def sized (n : Nat) : List Instr := [.ADDI .x25 .x0 (imm n)]
def slot (n : Nat) : List Instr := [.LD .x25 .x9 (imm n)]

/-- Distinct source/destination regions. The actual shared DER encoder chooses
minimal short/long length headers; no host ASN.1 runtime or reserved gaps. -/
def wrap (tag source output resultSlot : Nat) (length : List Instr) : Part := .seq [
  .asm (block (length ++ ptr .x24 .x9 source ++ ptr .x22 .x9 output ++
    [.ADDI .x10 .x0 (imm tag), .ADDI .x11 .x25 0,
      .ADDI .x12 .x22 0, .ADDI .x13 .x0 10])), checked 7 30,
  .asm (sequence [block [.ADD .x5 .x11 .x25, .SD .x9 .x5 (imm resultSlot),
    .ADD .x22 .x22 .x11], copy .x22 .x24 .x25])]

def wrapBody (tag output resultSlot : Nat) : Part :=
  wrap tag 2560 output resultSlot (ptr .x7 .x9 2560 ++ [.SUB .x25 .x26 .x7])

private def validityDer : Part := .seq [startBody,
  append 0 (slot 1160), append 32 (slot 1168), wrapBody 48 80 1264]

private def signedKey : Part := .seq [startBody,
  header 4 (slot 1200 ++ [.ADDI .x25 .x25 (-2)]),
  append 1210 (slot 1200 ++ [.ADDI .x25 .x25 (-2)]),
  header 4 (slot 1184), append 408 (slot 1184), wrapBody 48 2816 1272]

private def extensions : Part := .seq [signedKey, startBody,
  literal Spec.Identity.Certificate.identityOid, literal [1,1,255],
  header 4 (slot 1272), append 2816 (slot 1272), wrapBody 48 2944 1272,
  startBody, append 2944 (slot 1272), literal Spec.Identity.Certificate.usageExtensions,
  wrapBody 48 2816 1272, wrap 163 2816 3072 1272 (slot 1272)]

def tbs : Part := .seq [validityDer, extensions, startBody,
  literal [160,3,2,1,2,2,1,1], literal Spec.Identity.Certificate.edAlgorithm,
  literal Spec.Identity.Certificate.issuerName, append 80 (slot 1264),
  literal Spec.Identity.Certificate.issuerName, append 1280 (sized 44),
  append 3072 (slot 1272), wrapBody 48 1536 1192]

def completeDer : Part := .seq [startBody, append 1536 (slot 1192),
  literal Spec.Identity.Certificate.edAlgorithm, literal [3,65,0], append 480 (sized 64),
  wrapBody 48 2048 1256]

end Libp2pAsm.Asm.Identity.Certificate.Issue
