import Libp2pAsm.Asm.Identity.Certificate.Der

namespace Libp2pAsm.Asm.Identity.Certificate.Issue
open Rv64 Crypto.Util Crypto.Link
open Crypto.Curve25519 (ptr)

private def publish : SAsm.Stmt := sequence [
  block [.LD .x12 .x9 1256, .LD .x5 .x8 72], require (.geu .x5 .x12) 5,
  block ([.LD .x10 .x8 64] ++ ptr .x11 .x9 2048), copy .x10 .x11 .x12,
  block [.LD .x10 .x8 80, .LD .x11 .x8 48, .ADDI .x12 .x0 32], copy .x10 .x11 .x12,
  block [.LD .x10 .x8 128, .ADDI .x11 .x9 1200, .ADDI .x12 .x0 48], copy .x10 .x11 .x12,
  block [.LD .x22 .x9 1256, .ADDI .x11 .x2 (-1440), .ADDI .x12 .x0 1440], wipe .x11 .x12,
  block (load .x12 workSize), wipe .x9 .x12,
  block ([.ADDI .x11 .x22 0, .ADDI .x10 .x0 0] ++
    saved.zipIdx.flatMap (fun (r,i) => [.LD r .x2 (imm (8*i)), .SD .x2 .x0 (imm (8*i))]) ++
    [.SD .x2 .x0 104, .ADDI .x2 .x2 112] ++
    (Crypto.Sha2.cleared.filter (fun r => r != .x10 && r != .x11)).map (fun r => .ADDI r .x0 0)),
  .ret]

/-- Descriptor192: host secret0/len8,kind16,NotBefore32/NotAfter40 signed seconds,
fresh entropy48/len56,DER out64/cap72,owned seed out80/cap88,work96/cap104,
operation budget112,stack capacity120,Peer-ID record out128/cap136.
Caller provides cryptographically fresh completion-reserved entropy for EACH
connection. No RNG/fallback/reuse is supplied here. Caller wipes both entropy
and returned owned seed on abort/Finished. Returns status a0,DER length a1.
Work16384,stack1552; all outputs commit together, exact used buffers wiped. -/
def issue : Except String SAsm.Stmt := do
  program (.seq [.asm preflight, .asm setup, times,
    edPublic [.LD .x10 .x8 48] 360, hostPublic, .asm spki, hostSign, tbs,
    edSign [.LD .x10 .x8 48] [.ADDI .x12 .x9 1536] [.LD .x13 .x9 1192] 480,
    completeDer, .asm publish]) (← callees)

end Libp2pAsm.Asm.Identity.Certificate.Issue
