import Libp2pAsm.Spec.Quic.Wire.Descriptors

namespace Libp2pAsm.Refinement.Quic.Wire
open Spec.Quic.Wire

theorem view_subtraction_iff (v : View) (n : Nat) :
    v.valid n ↔ v.offset+v.length ≤ n := by
  simp only [View.valid]; omega

theorem take_success (s : Cursor) (n : Nat) (h : s.pos+n ≤ s.bytes.size) :
    (take n).run s = .ok (⟨s.pos,n⟩,{s with pos := s.pos+n}) := by
  have h₁ : s.pos ≤ s.bytes.size := by omega
  have h₂ : n ≤ s.bytes.size-s.pos := by omega
  simp [take,require,h₁,h₂,StateT.run,StateT.bind,StateT.pure,StateT.get,StateT.set,
    get,getThe,MonadStateOf.get,set,bind,pure,Except.bind,Except.pure]

theorem take_truncated (s : Cursor) (n : Nat) (h : s.bytes.size < s.pos+n) :
    (take n).run s = .error ⟨1,s.pos⟩ := by
  by_cases hp : s.pos ≤ s.bytes.size
  · have hn : ¬ n ≤ s.bytes.size-s.pos := by omega
    simp only [StateT.run, take, bind, StateT.bind, Except.bind, get, getThe,
      MonadStateOf.get, StateT.get, pure, Except.pure, require, hp, decide_true,
      hn, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, fail,
      throw, throwThe, MonadExceptOf.throw, Function.comp, StateT.lift]
  · simp only [StateT.run, take, bind, StateT.bind, Except.bind, get, getThe,
      MonadStateOf.get, StateT.get, pure, Except.pure, require, hp, decide_false,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, fail, throw, throwThe,
      MonadExceptOf.throw, Function.comp, StateT.lift]

theorem cursor_nonwrapping (pos n size : Nat) (h : pos+n ≤ size) (hs : size < 2^64) :
    pos+n < 2^64 := by omega

theorem ack_pair_bound (previous gap length : Nat) (hg : gap+2 ≤ previous)
    (hl : length ≤ previous-gap-2) :
    previous-gap-2-length ≤ previous-gap-2 ∧ previous-gap-2+2 ≤ previous := by omega

theorem ack_disjoint (previous gap length : Nat) (hg : gap+2 ≤ previous)
    (hl : length ≤ previous-gap-2) :
    previous-gap-2-length ≤ previous-gap-2 ∧ previous-gap-2 < previous := by omega

theorem ack_gap_nonwrapping (gap : Nat) (h : gap ≤ maxVarint) : gap+2 < 2^64 := by
  unfold maxVarint at h; omega

theorem stream_end_bound (offset length : Nat) (ho : offset ≤ maxVarint)
    (hl : length ≤ maxVarint-offset) : offset+length ≤ maxVarint := by omega

theorem count_admission (count remaining capacity : Nat)
    (h : count ≤ remaining/2) (hc : count < capacity) :
    2*count ≤ remaining ∧ count+1 ≤ capacity := by omega

theorem ack_workspace_nonwrapping (count : Nat) (h : count ≤ (2^64-145)/16) :
    128+16*(count+1) < 2^64 := by omega

theorem advancing_parameter (pos idWidth lengthWidth valueLength : Nat)
    (hi : 0 < idWidth) (hl : 0 < lengthWidth) :
    pos+2 ≤ pos+idWidth+lengthWidth+valueLength := by omega

def duplicateComparisons : Nat → Nat
  | 0 => 0 | n+1 => duplicateComparisons n+n

theorem quadratic_scans (n : Nat) : duplicateComparisons n ≤ n*n := by
  induction n with
  | zero => simp [duplicateComparisons]
  | succ n ih =>
    simp only [duplicateComparisons, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

theorem preferred_vector_bounds (off n size : Nat) (hn : 1 ≤ n ∧ n ≤ 20)
    (h : off+41+n ≤ size) :
    off+25+n+16 ≤ size ∧ off+24 < size ∧ off+6+16 ≤ size := by omega

theorem reserve_preserves_bounds (used n outCap workCap : Nat)
    (ho : used ≤ outCap) (hw : used ≤ workCap)
    (hn : n ≤ outCap-used ∧ n ≤ workCap-used) :
    used+n ≤ outCap ∧ used+n ≤ workCap := by omega

theorem packet_coalescing_progress (offset consumed size : Nat)
    (hp : 0 < consumed) (hb : consumed ≤ size-offset) (ho : offset ≤ size) :
    offset < offset+consumed ∧ offset+consumed ≤ size := by omega

theorem integer_bounds (id n : Nat) (h : integerValid id n = true) :
    n ≤ maxVarint ∧ (id = 3 → 1200 ≤ n) ∧
    (id = 8 ∨ id = 9 → n ≤ 2^60) ∧ (id = 10 → n ≤ 20) ∧
    (id = 11 → n < 2^14) ∧ (id = 14 → 2 ≤ n) := by
  simp [integerValid] at h
  omega

theorem bounded_encode_size (cap : Nat) (bs out : List UInt8)
    (h : bounded cap bs = .ok out) : out = bs ∧ out.length ≤ cap := by
  unfold bounded at h
  split at h <;> simp_all

theorem descriptor_encode_header (kind : Nat) (bs : Array UInt8) (server : Bool)
    (bound cap : Nat) (out : List UInt8)
    (h : Descriptors.encode kind bs server bound cap = .ok out) :
    (if kind = 2 then 512 else 128) ≤ bs.size := by
  by_cases hn : (if kind = 2 then 512 else 128) ≤ bs.size
  · exact hn
  · simp [Descriptors.encode, hn, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw, Except.mapError] at h

end Libp2pAsm.Refinement.Quic.Wire
