import Libp2pAsm.Asm.Crypto.Link

namespace Libp2pAsm.Asm.Tls
open Rv64 Crypto.Util

abbrev Expr := Reg → List Instr
def field (offset : Nat) : Expr := fun r => [.LD r .x10 (imm offset)]
def literal (n : Nat) : Expr := fun r => load r n
def register (r : Reg) : Expr := fun d => [.ADDI d r 0]
structure Span where
  ptr : Expr
  len : Expr
def fixed (offset size : Nat) : Span := ⟨field offset, literal size⟩
def variableSpan (ptr len : Nat) : Span := ⟨field ptr, field len⟩

def descriptor (bytes : Nat) : SAsm.Stmt := sequence [
  block [.ANDI .x5 .x10 7], reject (.ne .x5 .x0) 4,
  block (load .x7 bytes), range .x10 .x7]

def apart (a b : Span) : SAsm.Stmt := sequence [
  block (a.ptr .x28 ++ a.len .x29 ++ b.ptr .x30 ++ b.len .x31),
  .ite (.ne .x29 .x0) (.ite (.ne .x31 .x0) (
    .ite (.ltu .x28 .x30)
      (sequence [block [.SUB .x5 .x30 .x28], reject (.ltu .x5 .x29) 4])
      (sequence [block [.SUB .x5 .x28 .x30], reject (.ltu .x5 .x31) 4])) empty) empty]

/-- Actual checked ranges; mapping, permissions, immutable inputs/table, and
disjoint executable code are caller obligations. Stack depth is at most 2048. -/
def spans (descBytes depth : Nat) (items : List Span) : SAsm.Stmt :=
  let all := (⟨register .x10, literal descBytes⟩ : Span) ::
    (if depth == 0 then [] else [⟨fun r => [.ADDI r .x2 (imm (4096-depth))], literal depth⟩]) ++ items
  sequence ([block (load .x7 depth), reject (.ltu .x2 .x7) 4,
    block [.ANDI .x5 .x2 15], reject (.ne .x5 .x0) 4] ++
    all.map (fun s => sequence [block (s.ptr .x28 ++ s.len .x29), range .x28 .x29]) ++
    (all.zipIdx.flatMap fun (a,i) => (all.drop (i+1)).map (apart a)))

def alignedField (offset : Nat) : SAsm.Stmt := sequence [
  block [.LD .x5 .x10 (imm offset), .ANDI .x5 .x5 7], reject (.ne .x5 .x0) 4]

def writeBytes (dst : Reg) (offset : Nat) (bytes : List Nat) : SAsm.Stmt := block <|
  bytes.zipIdx.flatMap fun (b,i) => [.ADDI .x7 .x0 (imm b), .SB dst .x7 (imm (offset+i))]

end Libp2pAsm.Asm.Tls
