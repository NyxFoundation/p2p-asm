import Libp2pAsm.Rv64.Logic.ParserMemory

namespace Libp2pAsm.Rv64.Logic.Parser

theorem sub_toNat_of_le (a b : Word) (h : b≤a) : (a-b).toNat=a.toNat-b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.le_def] at h
  rw [BitVec.toNat_sub]
  omega

theorem difference_fits (a b n : Word) (h : a≤b) :
    n≤b-a ↔ a.toNat+n.toNat≤b.toNat := by
  rw [BitVec.le_def,sub_toNat_of_le b a h]
  have hnat : a.toNat≤b.toNat := h
  omega

def DisjointSpans (a : Word) (n : Nat) (b : Word) (m : Nat) : Prop :=
  a.toNat+n≤b.toNat ∨ b.toNat+m≤a.toNat

instance (a : Word) (n : Nat) (b : Word) (m : Nat) : Decidable (DisjointSpans a n b m) :=
  inferInstanceAs (Decidable (a.toNat+n≤b.toNat ∨ b.toNat+m≤a.toNat))

end Libp2pAsm.Rv64.Logic.Parser
