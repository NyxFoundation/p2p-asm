import Libp2pAsm.Refinement.Clock.Memory

namespace Libp2pAsm.Refinement.Clock

open Rv64

set_option maxRecDepth 65536

theorem signed_difference (a b : Word) (h : b.toInt ≤ a.toInt) :
    ((a-b).toNat : Int) = a.toInt-b.toInt := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.toNat_sub, BitVec.toInt_eq_toNat_cond] at h ⊢
  omega

def secondsPart (old : RawState) (sample : RawSample) : Word :=
  if sample.nanos < old.nanos then sample.seconds-old.seconds+18446744073709551615
  else sample.seconds-old.seconds

def nanosPart (old : RawState) (sample : RawSample) : Word :=
  if sample.nanos < old.nanos then sample.nanos+1000000000-old.nanos
  else sample.nanos-old.nanos

def wallElapsed (old : RawState) (sample : RawSample) : Int :=
  (sample.seconds.toInt-old.seconds.toInt)*1000000000+
    (sample.nanos.toNat : Int)-(old.nanos.toNat : Int)

theorem nanos_borrow (a b : Word) (ha : a < 1000000000) (hb : b < 1000000000) :
    (a+1000000000-b).toNat = a.toNat+1000000000-b.toNat := by
  have ha' : a.toNat < 1000000000 := ha
  have hb' : b.toNat < 1000000000 := hb
  have hsum : (a+1000000000).toNat = a.toNat+1000000000 := by
    apply BitVec.toNat_add_of_lt (by change a.toNat+1000000000 < 18446744073709551616; omega)
  have hle : b ≤ a+1000000000 := by change b.toNat ≤ _; rw [hsum]; omega
  rw [BitVec.toNat_sub_of_le hle, hsum]

theorem decrement_nat (a : Word) (ha : 0 < a.toNat) :
    (a+18446744073709551615).toNat = a.toNat-1 := by
  have hb := a.isLt
  rw [BitVec.toNat_add]
  change (a.toNat+18446744073709551615)%18446744073709551616 = _
  omega

theorem elapsed_parts (old : RawState) (sample : RawSample)
    (ho : old.nanos < 1000000000) (hn : sample.nanos < 1000000000)
    (hs : old.seconds.toInt ≤ sample.seconds.toInt)
    (he : sample.seconds = old.seconds → old.nanos ≤ sample.nanos) :
    ((secondsPart old sample).toNat : Int)*1000000000+(nanosPart old sample).toNat =
      wallElapsed old sample := by
  have hd := signed_difference sample.seconds old.seconds hs
  have hb := (sample.seconds-old.seconds).isLt
  have ho' : old.nanos.toNat < 1000000000 := ho
  have hn' : sample.nanos.toNat < 1000000000 := hn
  have he' : sample.seconds.toInt = old.seconds.toInt → old.nanos.toNat ≤ sample.nanos.toNat :=
    fun h => he (BitVec.toInt_inj.mp h)
  by_cases hlt : sample.nanos < old.nanos
  · have hlt' : sample.nanos.toNat < old.nanos.toNat := hlt
    have hdpos : 0 < (sample.seconds-old.seconds).toNat := by omega
    simp only [secondsPart, nanosPart, hlt, if_true, wallElapsed]
    rw [decrement_nat _ hdpos, nanos_borrow _ _ hn ho]
    omega
  · have hle : old.nanos ≤ sample.nanos := BitVec.not_lt.mp hlt
    simp only [secondsPart, nanosPart, hlt, if_false, wallElapsed,
      BitVec.toNat_sub_of_le hle]
    have hle' : old.nanos.toNat ≤ sample.nanos.toNat := hle
    omega

theorem nanosPart_small (old : RawState) (sample : RawSample)
    (ho : old.nanos < 1000000000) (hn : sample.nanos < 1000000000) :
    (nanosPart old sample).toNat < 1000000000 := by
  have ho' : old.nanos.toNat < 1000000000 := ho
  have hn' : sample.nanos.toNat < 1000000000 := hn
  by_cases hlt : sample.nanos < old.nanos
  · have hlt' : sample.nanos.toNat < old.nanos.toNat := hlt
    simp only [nanosPart, hlt, if_true, nanos_borrow _ _ hn ho]
    omega
  · have hle : old.nanos ≤ sample.nanos := BitVec.not_lt.mp hlt
    simp only [nanosPart, hlt, if_false, BitVec.toNat_sub_of_le hle]
    omega

def elapsedLow (seconds nanos : Word) : Word := seconds*1000000000+nanos

def elapsedHigh (seconds nanos : Word) : Word :=
  BitVec.ofNat 64 (seconds.toNat*1000000000/2^64)+
    (if elapsedLow seconds nanos < seconds*1000000000 then 1 else 0)

/-- Keep the multiplier symbolic while applying the word multiplication equation. -/
theorem mul_toNat_billion (a b : Word) (hb : b.toNat = 1000000000) :
    (a*b).toNat = a.toNat*1000000000%2^64 := by
  rw [BitVec.toNat_mul, hb]

theorem carry_wide (product : Nat) (low nanos : Word)
    (hl : low.toNat = product%2^64) (hp : product < 2^64*1000000000) (hn : nanos.toNat < 1000000000) :
    2^64*((BitVec.ofNat 64 (product/2^64)+
      (if low+nanos < low then 1 else 0) : Word).toNat)+(low+nanos).toNat = product+nanos.toNat := by
  have hsum : (low+nanos).toNat = (product%2^64+nanos.toNat)%2^64 :=
    (BitVec.toNat_add low nanos).trans (congrArg (fun n => (n+nanos.toNat)%2^64) hl)
  have hq : product/18446744073709551616 < 1000000000 := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
    omega
  have hqsmall : product/18446744073709551616 < 18446744073709551616 := by omega
  have hqadd : product/18446744073709551616+1 < 18446744073709551616 := by omega
  simp only [show (2^64 : Nat) = 18446744073709551616 by decide] at *
  have hr := Nat.mod_lt product (by decide : 0 < 18446744073709551616)
  have he := Nat.mod_add_div product 18446744073709551616
  by_cases hc : low+nanos < low
  · have hc' : (low+nanos).toNat < low.toNat := hc
    rw [hsum, hl] at hc'
    rw [if_pos hc, hsum]
    change 18446744073709551616*((product/18446744073709551616%18446744073709551616+1)%18446744073709551616)+
      (product%18446744073709551616+nanos.toNat)%18446744073709551616 = _
    rw [Nat.mod_eq_of_lt hqsmall, Nat.mod_eq_of_lt hqadd]
    have hw : 18446744073709551616 ≤ product%18446744073709551616+nanos.toNat := by omega
    rw [Nat.mod_eq_sub_mod hw, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hc' : ¬(low+nanos).toNat < low.toNat := hc
    rw [hsum, hl] at hc'
    rw [if_neg hc, hsum]
    change 18446744073709551616*((product/18446744073709551616%18446744073709551616+0)%18446744073709551616)+
      (product%18446744073709551616+nanos.toNat)%18446744073709551616 = _
    have hw : product%18446744073709551616+nanos.toNat < 18446744073709551616 := by omega
    simp only [Nat.add_zero, Nat.mod_eq_of_lt hqsmall, Nat.mod_eq_of_lt hw]
    omega

theorem multiply_with_carry (seconds nanos : Word) (hn : nanos.toNat < 1000000000) :
    2^64*(elapsedHigh seconds nanos).toNat+(elapsedLow seconds nanos).toNat =
      seconds.toNat*1000000000+nanos.toNat :=
  carry_wide (seconds.toNat*1000000000) (seconds*1000000000) nanos
    (mul_toNat_billion seconds 1000000000 rfl)
    (Nat.mul_lt_mul_of_pos_right seconds.isLt (by decide)) hn

end Libp2pAsm.Refinement.Clock
