import Libp2pAsm.Asm.Quic.Recovery.Path
import Libp2pAsm.Asm.Quic.Recovery.Audit

namespace Libp2pAsm.Asm.Quic.Recovery
open Rv64 Crypto.Util

/-- 64-byte descriptor: context ptr/bytes, event ptr/bytes, output ptr/capacity,
work ptr/capacity. Input words are aligned LE64. All mapped ranges and executable
code must be separately owned; runtime checks reject wrap and writable aliasing.
The stack is unused. Failure leaves context and output unchanged; validated work
is wiped. Memory failures before work validation perform no writes. -/
def boundary : SAsm.Stmt := sequence [Tls.descriptor 64,
  sequence ([0,16,32,48].map Tls.alignedField),
  block [.LD .x15 .x10 8, .ANDI .x5 .x15 7], reject (.ne .x5 .x0) 4,
  capacity .x15 512, block (load .x7 (2^64-65)), reject (.ltu .x7 .x15) 4,
  block [.LD .x15 .x10 24], capacity .x15 128,
  block [.LD .x15 .x10 40], capacity .x15 64,
  block [.LD .x15 .x10 56, .LD .x7 .x10 8, .ADDI .x7 .x7 64], reject (.ltu .x15 .x7) 5,
  Tls.spans 64 0 [Tls.variableSpan 0 8, Tls.variableSpan 16 24,
    Tls.fixed 32 64, Tls.variableSpan 48 56],
  block [.LD .x14 .x10 48, .LD .x15 .x10 0, .LD .x16 .x10 8], copyWords,
  block [.LD .x11 .x10 48, .LD .x12 .x10 16, .LD .x13 .x10 8, .ADD .x13 .x13 .x11],
  sequence ((List.range 8).map fun w => O w (n 0))]

def operation : String → Option SAsm.Stmt
  | "keys" => some installKeys | "init" => some init | "reserve" => some reserve | "result" => some result
  | "retry" => some retry | "expire" => some expire | "receive" => some receiveBytes
  | "validate" => some validatePath | "challenge" => some challenge | "response" => some response
  | "handshake" => some handshake | "ack" => some beginAck | "resume" => some resume
  | "timer" => some timer | "pto" => some firePto | "discard" => some beginDiscard
  | "loss" => some beginLoss | "newpath" => some newPath | "activate" => some activatePath
  | "persistent" => some collapse | _ => none

def program (kind : String) : Except String SAsm.Stmt := do
  let some op := operation kind | throw "unknown recovery operation"
  let body := sequence [boundary,
    if kind == "init" then empty else sequence [headerCheck, spaceCheck, recordCheck,
      evidenceCheck, pathTotals, connectionTotals, spaceTotals, batchCheck, generation],
    op, if kind == "expire" then ne (h 23) (n 0) clearBatch else empty, commit]
  match body.validate with
  | .ok () => pure body
  | .error err => throw s!"recovery lowering: {repr err}"

end Libp2pAsm.Asm.Quic.Recovery
