import Libp2pAsm.Asm.Stream.Common

namespace Libp2pAsm.Asm.Multistream
open Rv64 Crypto.Util Libp2pAsm.Asm.Stream

/-- Constants expanded at code generation, never dispatched by a host oracle. -/
def header : List Nat := "/multistream/1.0.0\n".toUTF8.data.toList.map UInt8.toNat
def ping : List Nat := "/ipfs/ping/1.0.0\n".toUTF8.data.toList.map UInt8.toNat
def na : List Nat := [110,97,10]

private def frame (xs : List Nat) : List Nat := xs.length :: xs

private def emitBytes (xs : List Nat) : SAsm.Stmt := seq [
  b [.ADDI .x5 .x0 (imm xs.length)], guard (.ltu .x11 .x5) 6 false,
  span .x10 .x11 false,
  b (xs.zipIdx.flatMap fun (v,i) => [.ADDI .x5 .x0 (imm v), .SB .x10 .x5 (imm i)]),
  b [.ADDI .x10 .x0 0, .ADDI .x11 .x0 (imm xs.length), .ADDI .x12 .x0 0,
    .ADDI .x13 .x0 0, .ADDI .x14 .x0 0], exit false]

/-- a0=owned output, a1=capacity, a2=0 listener start / 1 dialer start / 2 ping / 3 na.
Dialer start coalesces both protocol frames. Caller starts exactly once. -/
def emit : SAsm.Stmt := seq [
  b [.ADDI .x5 .x0 3], guard (.ltu .x5 .x12) 1 false,
  .ite (.eq .x12 .x0) (emitBytes (frame header)) nil,
  b [.ADDI .x5 .x0 1], .ite (.eq .x12 .x5) (emitBytes (frame header ++ frame ping)) nil,
  b [.ADDI .x5 .x0 2], .ite (.eq .x12 .x5) (emitBytes (frame ping)) (emitBytes (frame na))]

/-- Incremental strict UTF-8: bounds on the first continuation exclude overlong,
surrogate and >U+10FFFF encodings. Protocol text is public/released for matching. -/
def utf8 : SAsm.Stmt := .ite (.ne .x26 .x0) (seq [
  guard (.ltu .x15 .x27) 13, guard (.ltu .x17 .x15) 13,
  b [.ADDI .x26 .x26 (-1), .ADDI .x27 .x0 128, .ADDI .x17 .x0 191]])
  (seq [b [.ADDI .x5 .x0 128], .ite (.geu .x15 .x5) (seq [
    b [.ADDI .x5 .x0 194], guard (.ltu .x15 .x5) 13,
    b [.ADDI .x5 .x0 224], .ite (.ltu .x15 .x5) (b [.ADDI .x26 .x0 1])
    (seq [b [.ADDI .x5 .x0 240], .ite (.ltu .x15 .x5)
      (seq [b [.ADDI .x26 .x0 2, .ADDI .x5 .x0 224],
        .ite (.eq .x15 .x5) (b [.ADDI .x27 .x0 160]) nil,
        b [.ADDI .x5 .x0 237], .ite (.eq .x15 .x5) (b [.ADDI .x17 .x0 159]) nil])
      (seq [b [.ADDI .x5 .x0 245], guard (.geu .x15 .x5) 13,
        b [.ADDI .x26 .x0 3, .ADDI .x5 .x0 240],
        .ite (.eq .x15 .x5) (b [.ADDI .x27 .x0 144]) nil,
        b [.ADDI .x5 .x0 244], .ite (.eq .x15 .x5) (b [.ADDI .x17 .x0 143]) nil])])]) nil])

private def packed (xs : List Nat) : Nat :=
  (xs.zipIdx.map fun (v,i) => v*2^(8*i)).sum

private def selectWord (xs : List Nat) (chunk : Nat) : SAsm.Stmt :=
  if h : xs.length ≤ 8 then b (load .x6 (packed xs)) else
      seq [b [.ADDI .x5 .x0 (imm (8*(chunk+1)))],
        .ite (.ltu .x25 .x5) (b (load .x6 (packed (xs.take 8))))
          (selectWord (xs.drop 8) (chunk+1))]
termination_by xs.length
decreasing_by simp only [List.length_drop]; omega

def matchText (xs : List Nat) (bit : Nat) : SAsm.Stmt := seq [
  b [.ANDI .x5 .x16 (imm bit)], .ite (.ne .x5 .x0) (seq [selectWord xs 0,
    b [.ANDI .x5 .x25 7, .SLLI .x5 .x5 3, .SRL .x6 .x6 .x5, .ANDI .x6 .x6 255],
    .ite (.ne .x15 .x6) (b [.ANDI .x16 .x16 (BitVec.ofInt 12 (-1-Int.ofNat bit))]) nil]) nil]

end Libp2pAsm.Asm.Multistream
