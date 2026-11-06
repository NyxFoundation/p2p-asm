import Libp2pAsm.Rv64.Logic.RelocationInstr
import Libp2pAsm.Rv64.Logic.Embedding

namespace Libp2pAsm.Rv64.Logic

/-- Source stop zero maps to the caller's return address; every other PC translates. -/
def relocatePC (delta ra pc : Word) : Word := if pc = 0 then ra else pc + delta

@[simp] theorem relocatePC_zero (delta ra : Word) : relocatePC delta ra 0 = ra := by
  simp [relocatePC]

theorem add_mod_four (pc delta : Word) (hd : delta.toNat % 4 = 0) :
    (pc + delta).toNat % 4 = pc.toNat % 4 := by
  simp only [BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2^64), Nat.add_mod, hd, Nat.add_zero,
    Nat.mod_mod]

theorem sub_aligned (a b : Word) (ha : a.toNat % 4 = 0) (hb : b.toNat % 4 = 0) :
    (a-b).toNat % 4 = 0 := by
  simp only [BitVec.toNat_sub]
  rw [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2^64)]
  have := a.isLt
  have := b.isLt
  omega

theorem relocatePC_offset (delta ra pc off : Word) (hp : pc ≠ 0) (ht : pc+off ≠ 0)
    (hd : delta.toNat % 4 = 0) : MapsOffset (relocatePC delta ra) pc off := by
  simp only [MapsOffset, relocatePC, hp, ht, ↓reduceIte]
  constructor
  · rw [BitVec.add_assoc, BitVec.add_comm off delta, ← BitVec.add_assoc]
  · rw [add_mod_four _ _ hd]

/-- A static check excluding accidental branches to the fixed proof's sentinel.
It need not exclude unreachable jumps past the end of a lowered conditional. -/
def AvoidsZero (pc : Word) : Instr → Prop
  | .BEQ _ _ off | .BNE _ _ off | .BLTU _ _ off | .BGEU _ _ off =>
      pc + 4 ≠ 0 ∧ pc + off.signExtend 64 ≠ 0
  | .JAL _ off => pc + off.signExtend 64 ≠ 0
  | .JALR .. => True
  | _ => pc + 4 ≠ 0

instance (pc : Word) (i : Instr) : Decidable (AvoidsZero pc i) := by
  cases i <;> unfold AvoidsZero <;> infer_instance

theorem relocatePC_instr (delta ra pc : Word) (i : Instr) (hp : pc ≠ 0)
    (hd : delta.toNat % 4 = 0) (hi : AvoidsZero pc i) :
    MapsInstr (relocatePC delta ra) pc i := by
  cases i <;> simp only [AvoidsZero] at hi <;> simp only [MapsInstr]
  all_goals first
    | trivial
    | exact (relocatePC_offset delta ra pc 4 hp hi hd).1
    | exact relocatePC_offset delta ra pc _ hp hi hd
    | exact ⟨(relocatePC_offset delta ra pc 4 hp hi.1 hd).1,
        relocatePC_offset delta ra pc _ hp hi.2 hd⟩

theorem codeAddress_add (p : Program) (j : Nat) :
    codeAddress p j = p.base + BitVec.ofNat 64 (4*j) := by
  simp [codeAddress, BitVec.ofNat_add]

theorem codeAddress_relocate (p : Program) (base : Word) (j : Nat) :
    codeAddress p j + (base-p.base) = codeAddress { p with base := base } j := by
  simp only [codeAddress_add]
  rw [BitVec.add_comm p.base _, BitVec.add_assoc, BitVec.add_comm p.base _,
    BitVec.sub_add_cancel, BitVec.add_comm]

theorem codeAddress_nonzero {p : Program} (hpos : 0 < p.base.toNat)
    (hb : p.base.toNat + 4*p.code.size ≤ 2^64) {j : Nat} (hj : j < p.code.size) :
    codeAddress p j ≠ 0 := by
  intro hz
  have hlt : p.base.toNat + 4*j < 2^64 := by omega
  have := congrArg BitVec.toNat hz
  simp [codeAddress, Nat.mod_eq_of_lt hlt] at this
  omega

end Libp2pAsm.Rv64.Logic
