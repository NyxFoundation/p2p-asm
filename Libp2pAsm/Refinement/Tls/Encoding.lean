import Libp2pAsm.Refinement.Tls.Helpers
import Libp2pAsm.Spec.Tls.Encode
import Libp2pAsm.Spec.Tls.Bounds
import Libp2pAsm.Asm.Tls.Encode

namespace Libp2pAsm.Refinement.Tls
open Rv64

theorem vector_length (width minimum : Nat) (input encoded : Spec.Tls.Bytes)
    (h : Spec.Tls.vector width minimum input = .ok encoded) :
    encoded.size = width+input.size ∧ input.size < 256^width ∧ minimum ≤ input.size := by
  unfold Spec.Tls.vector at h
  dsimp at h
  split at h
  · change (Except.error Spec.Tls.Error.malformed : Except Spec.Tls.Error _) = .ok encoded at h
    cases h
  · split at h
    · change (Except.error Spec.Tls.Error.malformed : Except Spec.Tls.Error _) = .ok encoded at h
      cases h
    · simp [pure, Except.pure] at h
      subst encoded
      simp_all [Spec.Tls.be, Spec.Crypto.Sha2.encodeBE]

theorem header16_roundtrip (n : Nat) (h : n < 2^16) :
    (Spec.Tls.be 2 n).foldl (fun a b => 256*a+b.toNat) 0 = n := by
  simp [Spec.Tls.be, Spec.Crypto.Sha2.encodeBE, List.range_succ, Nat.toUInt8]
  omega

theorem header8_roundtrip (n : Nat) (h : n < 256) :
    (Spec.Tls.be 1 n).foldl (fun a b => 256*a+b.toNat) 0 = n := by
  simp [Spec.Tls.be, Spec.Crypto.Sha2.encodeBE, List.range_succ, Nat.toUInt8]
  omega

theorem encode_workspace_alignment (n : Nat) :
    (n+11)/8*8 % 8 = 0 ∧ n+4 ≤ (n+11)/8*8 ∧ (n+11)/8*8 ≤ n+11 := by omega

theorem encode_workspace_bound (n : Nat) (h : n < 2^24) :
    Spec.Tls.Bounds.encodeWorkspace n < 2^25 := by
  unfold Spec.Tls.Bounds.encodeWorkspace
  omega

theorem encode_workspace_correspondence (n : Nat) :
    Asm.Tls.Encode.required n = Spec.Tls.Bounds.encodeWorkspace n := by rfl

theorem decode_budget_word (n : Nat) (h : n ≤ 2^24+3) :
    Spec.Tls.Bounds.decodeSteps n < 2^64 := by
  unfold Spec.Tls.Bounds.decodeSteps
  omega

theorem encode_budget_word (n : Nat) (h : n < 2^24) :
    Spec.Tls.Bounds.encodeSteps n < 2^64 := by
  unfold Spec.Tls.Bounds.encodeSteps Spec.Tls.Bounds.decodeSteps Spec.Tls.Bounds.encodeWorkspace
  omega

theorem quic_reject_record (kind : Nat) :
    Spec.Tls.admitQuic true kind = .error .unsupported := by rfl

theorem quic_reject_key_update :
    Spec.Tls.admitQuic false 24 = .error .unsupported := by rfl

/-- A real shift/OR pair in the header-reading instruction implementation.
All registers other than x14, and memory, are preserved by the fragment. -/
theorem header_shift_or_fragment (s : State) :
    execSequence [.SLLI .x14 .x14 8, .OR .x14 .x14 .x6] s =
      .ok (((s.setReg .x14 (s.getReg .x14 <<< 8)).advance.setReg .x14
        ((s.getReg .x14 <<< 8) ||| s.getReg .x6)).advance) := by
  let t := (s.setReg .x14 (s.getReg .x14 <<< 8)).advance
  change (Except.ok ((t.setReg .x14 (t.getReg .x14 ||| t.getReg .x6)).advance) : Except Trap State) = _
  have h14 : t.getReg .x14 = s.getReg .x14 <<< 8 :=
    State.getReg_setReg_same s .x14 _ (by decide)
  have h6 : t.getReg .x6 = s.getReg .x6 :=
    State.getReg_setReg_other s .x14 .x6 _ (by decide)
  rw [h14,h6]

/-- uint24 accumulation cannot wrap a 64-bit RV word. -/
theorem uint24_accumulate_bound (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    (256*a+b)*256+c < 2^24 := by omega

theorem header_shift_or_in_reader :
    (Asm.Tls.Cursor.read 3 .x14).flatten.reverse.take 3 =
      [.ADDI .x9 .x9 3, .OR .x14 .x14 .x6, .SLLI .x14 .x14 8] := by decide

end Libp2pAsm.Refinement.Tls
