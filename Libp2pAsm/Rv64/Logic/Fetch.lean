import Libp2pAsm.Rv64.Logic.Trace

namespace Libp2pAsm.Rv64.Logic

/-- An instruction address in the non-wrapping, aligned program image. -/
def codeAddress (p : Program) (i : Nat) : Word := BitVec.ofNat 64 (p.base.toNat + 4 * i)

theorem fetch_codeAddress (p : Program) (i : Nat) (hi : i < p.code.size)
    (ha : p.base.toNat % 4 = 0) (hb : p.base.toNat + 4 * p.code.size ≤ 2^64) :
    p.fetch (codeAddress p i) = .ok p.code[i] := by
  have hp : p.base.toNat + 4 * i < 2^64 := by omega
  have hn : (codeAddress p i).toNat = p.base.toNat + 4 * i := by
    simp [codeAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  have hm : (p.base.toNat + 4 * i) % 4 = 0 := by omega
  simp [LeanAsm.Rv64.Image.fetch, hn, hm, Nat.add_sub_cancel_left, hi, pure, Except.pure]

theorem fetch_mem {p : Program} {pc : Word} {i : Instr} (h : p.fetch pc = .ok i) :
    i ∈ p.code := by
  simp only [LeanAsm.Rv64.Image.fetch, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat split at h
  all_goals simp_all
  subst i
  exact Array.getElem_mem _

end Libp2pAsm.Rv64.Logic
