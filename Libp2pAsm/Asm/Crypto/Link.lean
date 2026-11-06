import Libp2pAsm.Asm.Crypto.Util

/-! Local, position-independent internal calls using existing typed SAsm only.
A call sets t6 to its continuation, sets ra to the callee, then uses SAsm.ret
(JALR x0, ra, 0) as the transfer. A callee first adopts t6 as ra. Every routine
saves ra before nested calls and restores it on exit. No common lowering changes.
The five-instruction call has no branch-range dependency. Relocations are checked
BEFORE converting to immediates; final SAsm validation is still mandatory. -/
namespace Libp2pAsm.Asm.Crypto.Link
open Rv64

inductive Part where
  | asm (s : SAsm.Stmt)
  | call (target : Nat)
  | seq (parts : List Part)
  | ite (c : SAsm.Cond) (yes no : Part)
  | loop (c : SAsm.Cond) (body : Part)

open Part

def Part.size : Part → Nat
  | .asm s => s.size | .call _ => 5
  | .seq ps => (ps.map Part.size).sum
  | .ite _ a b => a.size + b.size + 2
  | .loop _ b => b.size + 2

def transfer (pc target : Nat) : Except String SAsm.Stmt := do
  let delta : Int := Int.ofNat target - Int.ofNat (pc + 8)
  let hi := (delta + 2048) / 4096
  let lo := delta - hi * 4096
  unless -(2^19) ≤ hi && hi < 2^19 && -2048 ≤ lo && lo < 2048 do
    throw "crypto call relocation out of range"
  return sequence [.block [.AUIPC .x31 0, .ADDI .x31 .x31 20,
    .AUIPC .x1 (BitVec.ofInt 20 hi), .ADDI .x1 .x1 (BitVec.ofInt 12 lo)], .ret]

def Part.resolve (targets : Array Nat) (pc : Nat) : Part → Except String SAsm.Stmt
  | .asm s => pure s
  | .call n => match targets[n]? with
    | none => .error "missing crypto callee"
    | some target => transfer pc target
  | .seq ps => do
    let (_, out) ← ps.foldlM (fun (pos, out) p => do
      let s ← p.resolve targets pos
      pure (pos + p.size*4, out ++ [s])) (pc, [])
    pure (sequence out)
  | .ite c a b => do
    pure (.ite c (← a.resolve targets (pc+4)) (← b.resolve targets (pc+4*(a.size+2))))
  | .loop c b => do pure (.loop c (← b.resolve targets (pc+4)))

/-- Root routine has a standard leaf entry; appended callees use the t6 ABI. -/
def program (root : Part) (callees : List Part) : Except String SAsm.Stmt := do
  let (_, targets) := callees.foldl (fun (pc, acc) p =>
    (pc + 4*(p.size+1), acc.push pc)) (4*root.size, #[])
  let root ← root.resolve targets 0
  let linked ← callees.zipIdx.mapM fun (p, i) => do
    let pc := targets[i]!
    pure (sequence [.block [.ADDI .x1 .x31 0], ← p.resolve targets (pc+4)])
  let result := sequence (root :: linked)
  match result.validate with
  | .error e => throw s!"crypto SAsm validation: {repr e}"
  | .ok () => pure result

end Libp2pAsm.Asm.Crypto.Link
