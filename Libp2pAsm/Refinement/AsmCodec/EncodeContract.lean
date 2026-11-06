import Libp2pAsm.Refinement.AsmCodec.Programs
import Libp2pAsm.Rv64.Logic.Writes

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

/-- Capacity failure is applied only after the spec's value-domain check. -/
def encodeOutcome (result : Except Spec.Codec.Error (List UInt8)) (capacity : Nat) : Word × List UInt8 :=
  match result with
  | .error e => (errorCode e, [])
  | .ok bytes => if bytes.length ≤ capacity then (0, bytes) else (1, [])

def EncodePost (result : Except Spec.Codec.Error (List UInt8)) (capacity : Nat)
    (base : Word) (before : Array UInt8) (frame : List Region) (s : State) : Prop :=
  let out := encodeOutcome result capacity
  Output out.1 (BitVec.ofNat 64 out.2.length) 0 s ∧
    s.memory = heap base (patchBytes before 0 out.2) true frame

theorem encode_memory_frame (result : Except Spec.Codec.Error (List UInt8)) (capacity : Nat)
    (before : Array UInt8) :
    ByteFrame 0 (encodeOutcome result capacity).2.length before
      (patchBytes before 0 (encodeOutcome result capacity).2) := patchBytes_frame _ _ _

theorem encodeOutcome_capacity (result : Except Spec.Codec.Error (List UInt8)) (capacity : Nat) :
    (encodeOutcome result capacity).2.length ≤ capacity := by
  cases result <;> simp only [encodeOutcome]
  · simp
  · split <;> simp_all

theorem encodeOutcome_error (result : Except Spec.Codec.Error (List UInt8)) (capacity : Nat)
    (he : (encodeOutcome result capacity).1 ≠ 0) : (encodeOutcome result capacity).2 = [] := by
  cases result with
  | error e => rfl
  | ok bytes =>
    by_cases hc : bytes.length ≤ capacity
    · simp only [encodeOutcome, if_pos hc] at he
      exact False.elim (he rfl)
    · simp only [encodeOutcome, if_neg hc]

theorem EncodePost.error_memory {result capacity base before frame s}
    (h : EncodePost result capacity base before frame s)
    (he : s.getReg .x10 ≠ 0) : s.memory = heap base before true frame := by
  have hz : (encodeOutcome result capacity).1 ≠ 0 := by
    rw [← h.1.1]; exact he
  simpa only [encodeOutcome_error result capacity hz, patchBytes] using h.2

/-- Exact output bytes, unchanged guard bytes, and an unchanged list of foreign regions. -/
theorem EncodePost.bytes {result capacity base before frame s}
    (h : EncodePost result capacity base before frame s) (hc : capacity ≤ before.size) :
    ∃ after : Array UInt8, s.memory = heap base after true frame ∧
      ByteFrame 0 (encodeOutcome result capacity).2.length before after ∧
      ∀ j (hj : j < (encodeOutcome result capacity).2.length),
        after[j]? = some ((encodeOutcome result capacity).2[j]) := by
  refine ⟨patchBytes before 0 (encodeOutcome result capacity).2, h.2,
    encode_memory_frame result capacity before, ?_⟩
  intro j hj
  have hn := encodeOutcome_capacity result capacity
  have he := patchBytes_get before 0 (encodeOutcome result capacity).2 (by omega) j hj
  have hb : j < (patchBytes before 0 (encodeOutcome result capacity).2).size := by simp; omega
  simpa [Array.getElem?_eq_getElem hb] using congrArg some he

end Libp2pAsm.Refinement.AsmCodec
