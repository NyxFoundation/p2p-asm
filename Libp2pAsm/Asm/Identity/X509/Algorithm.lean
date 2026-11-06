import Libp2pAsm.Asm.Crypto.Util

namespace Libp2pAsm.Asm.Identity.X509.Algorithm
open Rv64 Crypto.Util

/-! Generation-time constants for the supported AlgorithmIdentifier grammar.
Only ordinary LBU/XORI/OR instructions compare these public bytes at runtime.
RFC4055 §3.1 requires recognizing explicit trailerField1; §5 accepts absent NULL. -/
private def tlv (tag : Nat) (body : List Nat) : List Nat := [tag, body.length] ++ body
private def oid (bytes : List Nat) : List Nat := tlv 6 bytes
private def seq (body : List Nat) : List Nat := tlv 48 body

private def sha (withNull : Bool) : List Nat :=
  seq (oid [96, 134, 72, 1, 101, 3, 4, 2, 1] ++ if withNull then [5, 0] else [])

private def pss (hashNull maskNull trailer : Bool) : List Nat :=
  seq (oid [42, 134, 72, 134, 247, 13, 1, 1, 10] ++ seq (
    tlv 160 (sha hashNull) ++
    tlv 161 (seq (oid [42, 134, 72, 134, 247, 13, 1, 1, 8] ++ sha maskNull)) ++
    [162, 3, 2, 1, 32] ++ if trailer then [163, 3, 2, 1, 1] else []))

private def signaturePatterns : List (Nat × List Nat) :=
  [(1, seq (oid [43, 101, 112])),
   (2, seq (oid [42, 134, 72, 206, 61, 4, 3, 2])),
   (3, seq (oid [42, 134, 72, 134, 247, 13, 1, 1, 11])),
   (3, seq (oid [42, 134, 72, 134, 247, 13, 1, 1, 11] ++ [5, 0]))] ++
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].map fun c => (4, pss a b c)

private def publicPatterns : List (Nat × List Nat) := [
  (1, seq (oid [43, 101, 112])),
  (2, seq (oid [42, 134, 72, 206, 61, 2, 1] ++ oid [42, 134, 72, 206, 61, 3, 1, 7])),
  (3, seq (oid [42, 134, 72, 134, 247, 13, 1, 1, 1])),
  (3, seq (oid [42, 134, 72, 134, 247, 13, 1, 1, 1] ++ [5, 0]))]

private def accepted (kind : Nat) : SAsm.Stmt := sequence [
  block ([.ADDI .x11 .x0 (imm kind)] ++
    ((Crypto.Sha2.cleared.filter (· != .x11)).map fun r => .ADDI r .x0 0)), .ret]

private def candidate (kind : Nat) (bytes : List Nat) : SAsm.Stmt := sequence [
  block [.ADDI .x7 .x0 (imm bytes.length)],
  .ite (.eq .x11 .x7) (sequence [
    block ([.ADDI .x13 .x0 0] ++ bytes.zipIdx.flatMap (fun (b, i) =>
      [.LBU .x12 .x10 (imm i), .XORI .x12 .x12 (imm b), .OR .x13 .x13 .x12])),
    .ite (.eq .x13 .x0) (accepted kind) empty]) empty]

private def recognize (patterns : List (Nat × List Nat)) : SAsm.Stmt :=
  sequence ([range .x10 .x11] ++
    patterns.map (fun (kind, bytes) => candidate kind bytes) ++ [finish 8])

/-- a0=complete AlgorithmIdentifier DER,a1=length -> a0=status,a1=kind.
Signature kinds: Ed25519=1,ECDSA/P256/SHA256=2,PKCS1/SHA256=3,PSS/SHA256=4.
Status8 merges unsupported and malformed algorithms; status4 is pointer range.
No stack/writes; preserve ra/sp/gp/tp/s registers, clear other caller temps.
Valid readonly mapping/code separation is caller-owned. No signature is verified. -/
def signature : SAsm.Stmt := recognize signaturePatterns

/-- Same ABI; public-key kinds: Ed25519=1,P256=2,rsaEncryption=3.
This is not key-point/strength validation or authorization. -/
def publicKey : SAsm.Stmt := recognize publicPatterns

end Libp2pAsm.Asm.Identity.X509.Algorithm
