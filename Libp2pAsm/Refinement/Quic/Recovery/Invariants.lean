import Libp2pAsm.Spec.Quic.Recovery.Raw

namespace Libp2pAsm.Refinement.Quic.Recovery
open Spec.Quic.Recovery

/-- Honest admission uses the sum of actual and reserved bytes. -/
def AmplificationBound (received sent reserved : Nat) : Prop := sent+reserved ≤ 3*received

theorem amplification_reserve (received sent reserved bytes : Nat)
    (h : sent+reserved+bytes ≤ 3*received) :
    AmplificationBound received sent (reserved+bytes) := by
  unfold AmplificationBound
  omega

theorem amplification_success (received sent reserved bytes : Nat)
    (h : AmplificationBound received sent reserved) (hb : bytes ≤ reserved) :
    AmplificationBound received (sent+bytes) (reserved-bytes) := by
  unfold AmplificationBound at *
  omega

theorem amplification_release (received sent reserved bytes : Nat)
    (h : AmplificationBound received sent reserved) :
    AmplificationBound received sent (reserved-bytes) := by
  unfold AmplificationBound at *
  omega

theorem pending_not_sent (s : State) (i : Nat) (p : Packet)
    (hp : s.packets[i]? = some p) (_pending : p.status = 1) (notSent : p.evidence = false)
    (inSpace : p.space = s.batch.space)
    (cursor : s.batch.cursor = i) (rangeIndex : s.batch.rangeIndex < s.batch.ranges.size)
    (r : AckRange) (hr : s.batch.ranges[s.batch.rangeIndex]! = r)
    (lo : r.lo ≤ p.pn) (hi : p.pn ≤ r.hi) :
    validateOne s = .error .unsentAck := by
  have hi' : i < s.packets.size := Array.getElem?_eq_some_iff.mp hp |>.1
  have hp' : s.packets[i]! = p := by rw [getElem!_def, hp]
  simp [validateOne, cursor, Nat.ne_of_lt rangeIndex, Nat.ne_of_lt hi', hr,
    hp', inSpace, lo, hi, notSent]
  rfl

theorem checked_exact (n : Nat) (h : n < wordLimit) : checked n = .ok n := by
  simp [checked, h]

theorem checked_overflow (n : Nat) (h : wordLimit ≤ n) : checked n = .error .exhausted := by
  simp [checked, Nat.not_lt.mpr h]

theorem unknown_expiry_retains_reservations (s : State) (i now : Nat) (p : Packet)
    (hp : s.packets[i]? = some p) (hs : p.status = 1)
    (hr : s.retired = 0) (hb : s.batch.phase = 0)
    (hn : s.now ≤ now) (hw : now < wordLimit) (hd : p.deadline ≤ now) :
    expire s s.generation i now = .ok
      ({s with now := now, retired := 9, packets := s.packets.set! i {p with status := 7}},
       packetAction 6 i p) := by
  simp [expire, hp, hs, hr, hb, hn, hw, hd]
  rfl

theorem duplicate_ack_only_advances_cursor (s : State) (i : Nat) (p : Packet)
    (hp : s.packets[i]? = some p) (hc : s.batch.cursor = i) (hs : p.status = 4) :
    acknowledgeOne s = .ok
      ({s with batch := {s.batch with cursor := i+1}}, {kind := 10}) := by
  have hi : i < s.packets.size := (Array.getElem?_eq_some_iff.mp hp).1
  have hp' : s.packets[i]! = p := by rw [getElem!_def, hp]
  simp [acknowledgeOne, hc, Nat.ne_of_lt hi, hp', hs]
  rfl

theorem packet_number_final (n : Nat) (h : n < pnLimit) : n+1 ≤ pnLimit := by omega
theorem packet_number_strict (n : Nat) : n < n+1 := by omega

/-- Weighted RTT averages can be computed without ever forming 7*a+b in a word.
The quotient/remainder decomposition is exact, including integer floor rounding. -/
theorem weighted_smoothed (a b : Nat) :
    (7*a+b)/8 = 7*(a/8)+b/8+(7*(a%8)+b%8)/8 := by omega

theorem weighted_variance (a b : Nat) :
    (3*a+b)/4 = 3*(a/4)+b/4+(3*(a%4)+b%4)/4 := by omega

theorem amplification_wide (received sent reserved bytes : Nat)
    (h : sent+reserved+bytes ≤ 3*received) :
    (sent+reserved+bytes)/wordLimit < (3*received)/wordLimit ∨
      ((sent+reserved+bytes)/wordLimit = (3*received)/wordLimit ∧
       (sent+reserved+bytes)%wordLimit ≤ (3*received)%wordLimit) := by
  have hq : (sent+reserved+bytes)/wordLimit ≤ (3*received)/wordLimit := Nat.div_le_div_right h
  by_cases he : (sent+reserved+bytes)/wordLimit = (3*received)/wordLimit
  · right; refine ⟨he, ?_⟩
    have ha := Nat.mod_add_div (sent+reserved+bytes) wordLimit
    have hb := Nat.mod_add_div (3*received) wordLimit
    rw [he] at ha
    omega
  · left; omega

end Libp2pAsm.Refinement.Quic.Recovery
