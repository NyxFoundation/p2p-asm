import Libp2pAsm.Spec.Kernel.Limits
import Libp2pAsm.Spec.Kernel.Registry
import Libp2pAsm.Spec.Kernel.Queue
import Libp2pAsm.Spec.Kernel.Admission

namespace Libp2pAsm.Refinement.Kernel
open Spec.Kernel

theorem release_inactive (s : Slot) : s.release.active = false := by
  simp [Slot.release, Slot.active]

theorem release_clears_borrows (s : Slot) : s.release.borrowed = false := by
  simp [Slot.release, Slot.borrowed]

theorem release_generation_strict (s : Slot) (h : s.generation < wordMax) :
    s.generation < s.release.generation := by
  simp [Slot.release]
  omega

theorem release_generation_bounded (s : Slot) : s.release.generation ≤ wordMax := by
  exact Nat.min_le_left _ _

theorem release_exhausted_retired (s : Slot) (h : s.generation = wordMax) :
    s.release.retired = 1 ∧ s.release.generation = wordMax := by
  simp [Slot.release,h]

theorem reserve_preserves_capacity (r : Reservation) (next : Reservation)
    (h : r.reserve = .ok next) : next.valid := by
  simp only [Reservation.reserve] at h
  split at h
  · cases h
    simp only [Reservation.valid]
    omega
  · contradiction

theorem completion_preserves_capacity (r next : Reservation) (valid : r.valid)
    (h : r.deliver = .ok next) : next.valid := by
  simp only [Reservation.deliver] at h
  split at h
  · cases h
    simp only [Reservation.valid] at *
    omega
  · contradiction

theorem reserved_completion_has_room (r : Reservation) (valid : r.valid) (held : 0 < r.reserved) :
    r.queued < r.capacity := by
  unfold Reservation.valid at valid
  omega

theorem completion_conserves_reservation (r next : Reservation) (h : r.deliver = .ok next) :
    next.queued + next.reserved = r.queued + r.reserved := by
  simp only [Reservation.deliver] at h
  split at h
  · cases h
    simp only
    omega
  · contradiction

theorem charge_within_limits (used limits next : Charge) (cost : Nat)
    (h : used.tryCharge limits cost = .ok next) :
    next.quantum ≤ limits.quantum ∧ next.connection ≤ limits.connection ∧ next.global ≤ limits.global := by
  simp only [Charge.tryCharge] at h
  split at h
  · cases h
    simp_all
  · contradiction

theorem charge_accounts_exactly (used limits next : Charge) (cost : Nat)
    (h : used.tryCharge limits cost = .ok next) :
    next.quantum = used.quantum+cost ∧ next.connection = used.connection+cost ∧ next.global = used.global+cost := by
  simp only [Charge.tryCharge] at h
  split at h
  · cases h; simp
  · contradiction

theorem counted_datagrams_bounded (w : Window) (n : Nat) :
    (w.count n).datagrams ≤ wordMax ∧ (w.count n).bytes ≤ wordMax := by
  exact ⟨Nat.min_le_left _ _, Nat.min_le_left _ _⟩

theorem write_excludes_input_borrow (s : Slot) (flags : s.flags = 3) (borrowed : 0 < s.inputBorrow) :
    s.acquire 2 = .error 15 := by
  have ne : s.inputBorrow ≠ 0 := by omega
  simp [Slot.acquire,Slot.active,Slot.borrowed,flags,ne]
  rfl

theorem resolved_one_past_representable (base capacity offset length : Nat)
    (region : base+capacity ≤ wordMax) (lengthOK : length ≤ capacity)
    (offsetOK : offset ≤ capacity-length) :
    base+offset+length ≤ wordMax := by omega

theorem default_raw_serialization_valid :
    Spec.Kernel.encodeLimits ({} : Spec.Limits) = .ok (pack ({} : Spec.Limits).wordFields) := by rfl

theorem reject_unrepresentable_raw_serialization :
    Spec.Kernel.encodeLimits {maxRegions := 2^64} = .error 1 := by rfl

end Libp2pAsm.Refinement.Kernel
