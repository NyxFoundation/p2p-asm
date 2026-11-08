import Libp2pAsm.Asm.Kernel.Generation
import Libp2pAsm.Rv64.Execution
import Libp2pAsm.Refinement.Registers

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Libp2pAsm.Refinement.Kernel
open Rv64

private def increment (n : Word) : Word := if n < (-1 : Word) then 1 else 0

def generationPost (s : State) : State :=
  let s₁ := (s.setReg .x5 (-1)).advance
  let s₂ := (s₁.setReg .x6 (increment (s.getReg .x10))).advance
  let s₃ := (s₂.setReg .x10 (s.getReg .x10 + increment (s.getReg .x10))).advance
  (s₃.setReg .x11 (increment (s.getReg .x10) ^^^ 1)).advance

/-- Generic exact four-instruction correspondence, including every temporary and PC.
Fetch/return and the entire registry operation are separate obligations. -/
theorem generation_sequence (s : State) :
    execSequence Asm.Kernel.generationCode s = .ok (generationPost s) := by
  simp [Asm.Kernel.generationCode,execSequence,execInstr,writeReg,Bind.bind,Except.bind,generationPost,increment,
    State.getReg,State.setReg,State.advance,Reg.toNat]
  rfl

theorem increment_has_no_wrap (g : Word) :
    (g + increment g).toNat = min (2^64-1) (g.toNat+1) := by
  unfold increment
  split
  · rename_i h
    have hlt : g.toNat < 2^64-1 := by simpa [BitVec.lt_def] using h
    change (g.toNat+1) % 2^64 = min (2^64-1) (g.toNat+1)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i h
    have hg := g.isLt
    have he : g.toNat = 2^64-1 := by
      have : ¬g.toNat < 2^64-1 := by simpa [BitVec.lt_def] using h
      omega
    simp [he]

private def boundaryState (g : Nat) : State :=
  {pc := 0x10000,regs := (Vector.replicate 32 0).set 10 (BitVec.ofNat 64 g) (by decide)}
private def generationProgram : Program := ⟨0x10000,Asm.Kernel.nextGeneration.flatten.toArray⟩

private def observes (input output retired : Nat) : Bool :=
  match runUntil generationProgram 0 32 (boundaryState input) with
  | .error _ => false
  | .ok d => d.state.getReg .x10 == BitVec.ofNat 64 output &&
      d.state.getReg .x11 == BitVec.ofNat 64 retired

theorem generation_zero_fetched : observes 0 1 0 = true := by cbv

theorem generation_max_fetched : observes (2^64-1) (2^64-1) 1 = true := by cbv

end Libp2pAsm.Refinement.Kernel
