import Libp2pAsm.Rv64.Basic

/-!
The structured layouts and offset formulas adapt evm-asm SAsm/Ast.lean and
SAsm/Flatten.lean at 7e65e4d024718f704226cd795f3d03d4e9aafe13.
See LICENSES/evm-asm.txt. This smaller front end has no zkVM dependencies.
-/

namespace Libp2pAsm.Rv64.SAsm

inductive Cond where
  | eq (a b : Reg) | ne (a b : Reg)
  | ltu (a b : Reg) | geu (a b : Reg)
  deriving DecidableEq, Repr

def Cond.neg : Cond → Cond
  | .eq a b => .ne a b | .ne a b => .eq a b
  | .ltu a b => .geu a b | .geu a b => .ltu a b

def Cond.instr : Cond → BitVec 13 → Instr
  | .eq a b, off => .BEQ a b off | .ne a b, off => .BNE a b off
  | .ltu a b, off => .BLTU a b off | .geu a b, off => .BGEU a b off

theorem Cond.neg_neg (c : Cond) : c.neg.neg = c := by cases c <;> rfl

inductive Stmt where
  | block (code : List Instr)
  | seq (first second : Stmt)
  | ite (guard : Cond) (yes no : Stmt)
  | loop (guard : Cond) (body : Stmt)
  | ret
  deriving Repr

def Stmt.size : Stmt → Nat
  | .block code => code.length
  | .seq a b => a.size + b.size
  | .ite _ yes no => yes.size + no.size + 2
  | .loop _ body => body.size + 2
  | .ret => 1

private def brOfs (instructions : Nat) : BitVec 13 := BitVec.ofNat 13 (4 * instructions)
private def jFwd (instructions : Nat) : BitVec 21 := BitVec.ofNat 21 (4 * instructions)
private def jBack (instructions : Nat) : BitVec 21 :=
  BitVec.ofInt 21 (-Int.ofNat (4 * instructions))

def Stmt.flatten : Stmt → List Instr
  | .block code => code
  | .seq a b => a.flatten ++ b.flatten
  | .ite guard yes no =>
    guard.neg.instr (brOfs (yes.size + 2)) ::
      (yes.flatten ++ [.JAL .x0 (jFwd (no.size + 1))] ++ no.flatten)
  | .loop guard body =>
    guard.neg.instr (brOfs (body.size + 2)) ::
      (body.flatten ++ [.JAL .x0 (jBack (body.size + 1))])
  | .ret => [.JALR .x0 .x1 0]

private def straightLine : Instr → Bool
  | .BEQ .. | .BNE .. | .BLTU .. | .BGEU .. | .JAL .. | .JALR .. => false
  | _ => true

inductive LowerError where
  | controlInBlock | branchOutOfRange | jumpOutOfRange
  deriving DecidableEq, BEq, Repr

def Stmt.validate : Stmt → Except LowerError Unit
  | .block code =>
    if code.all straightLine then .ok () else .error .controlInBlock
  | .seq a b => do a.validate; b.validate
  | .ite _ yes no => do
    yes.validate
    no.validate
    unless 4 * (yes.size + 2) < 2 ^ 12 do throw .branchOutOfRange
    unless 4 * (no.size + 1) < 2 ^ 20 do throw .jumpOutOfRange
  | .loop _ body => do
    body.validate
    unless 4 * (body.size + 2) < 2 ^ 12 do throw .branchOutOfRange
    unless 4 * (body.size + 1) ≤ 2 ^ 20 do throw .jumpOutOfRange
  | .ret => .ok ()

def Stmt.lower (s : Stmt) : Except LowerError (Array Instr) := do
  s.validate
  return s.flatten.toArray

theorem Stmt.flatten_length (s : Stmt) : s.flatten.length = s.size := by
  induction s with
  | block code => rfl
  | seq a b ha hb => simp [flatten, size, ha, hb]
  | ite c yes no hy hn => simp [flatten, size, hy, hn]; omega
  | loop c body hb => simp [flatten, size, hb]
  | ret => rfl

end Libp2pAsm.Rv64.SAsm
