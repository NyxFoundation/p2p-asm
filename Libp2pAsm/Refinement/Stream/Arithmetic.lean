import Libp2pAsm.Spec.Stream.Receive
import Libp2pAsm.Spec.Stream.Send
import Libp2pAsm.Spec.Stream.Id

namespace Libp2pAsm.Refinement.Stream

/-- Exactly the subtraction-ordered public view check, including zero lengths. -/
theorem source_view_bounds (capacity offset length : Nat)
    (hl : length ≤ capacity) (ho : offset ≤ capacity-length) :
    offset+length ≤ capacity := by omega

theorem source_byte_bounds (capacity offset length index : Nat)
    (hl : length ≤ capacity) (ho : offset ≤ capacity-length) (hi : index < length) :
    offset+index < capacity := by omega

theorem nonwrapping_byte_address (base capacity offset : Nat)
    (h : base+capacity ≤ 2^64) (ho : offset < capacity) : base+offset < 2^64 := by omega

/-- A pending borrow caps collection before its first byte, even if ACKed. -/
theorem collection_preserves_borrow (base released pendingStart pendingEnd : Nat)
    (h : base+released ≤ pendingStart) (hr : pendingStart ≤ pendingEnd) :
    ∀ p, pendingStart ≤ p → p < pendingEnd → ¬p < base+released := by omega

/-- Splitting a ring borrow returns exactly the requested immutable range. -/
theorem split_view (cap offset count : Nat) (ho : offset < cap) (hc : count ≤ cap) :
    let first := min count (cap-offset)
    first ≤ cap-offset ∧ count-first ≤ offset ∧ first+(count-first) = count := by
  dsimp
  omega

theorem reclaim_prefix_only (base count pos : Nat) (h : base+count ≤ pos) :
    ¬(base ≤ pos ∧ pos < base+count) := by omega

theorem final_forbids_byte (off len final i : Nat)
    (h : off+len ≤ final) (hi : i < len) : off+i < final := by omega

theorem zero_length_final (off final : Nat) : off+0 = final ↔ off = final := by omega

theorem reservation_exact (sent endPos : Nat) (h : sent ≤ endPos) :
    sent + Spec.Stream.creditDelta sent endPos = endPos := by
  rw [Spec.Stream.credit_conservation, Nat.max_eq_right h]

end Libp2pAsm.Refinement.Stream
