import Libp2pAsm.Spec.Crypto.Quic.Basic
import Libp2pAsm.Asm.Crypto.Quic.Number
import Libp2pAsm.Asm.Crypto.Quic.Kdf
import Libp2pAsm.Refinement.Registers
import Libp2pAsm.Rv64.Execution

/-! Universal claims only for the stated arithmetic, encoding, and instruction
fragments. No full packet-composition, fetch, CT or ownership proof is implied. -/
namespace Libp2pAsm.Refinement.Crypto.Quic
open Rv64

theorem nonce_injective (iv : BitVec 96) (a b : BitVec 64)
    (h : Spec.Crypto.Quic.nonceWord iv a = Spec.Crypto.Quic.nonceWord iv b) : a = b := by
  have hx := congrArg (fun x : BitVec 96 => (iv ^^^ x).setWidth 64) h
  simpa [Spec.Crypto.Quic.nonceWord, BitVec.xor_assoc, BitVec.zeroExtend_eq_setWidth] using hx

theorem packet_number_cast_injective (a b : Nat) (ha : a < 2^62) (hb : b < 2^62)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have hx := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at hx
  omega

theorem nonce_62bit_injective (iv : BitVec 96) (a b : Nat) (ha : a < 2^62) (hb : b < 2^62)
    (h : Spec.Crypto.Quic.nonceWord iv (BitVec.ofNat 64 a) =
      Spec.Crypto.Quic.nonceWord iv (BitVec.ofNat 64 b)) : a = b :=
  packet_number_cast_injective a b ha hb (nonce_injective iv _ _ h)

/-- True radix-256 modular decomposition, including the 64-bit high byte. -/
theorem byte_split (n : Nat) : n % 256 + 256*(n/256) = n := by omega

theorem encode_byte_bound (n shift : Nat) : n / 2^shift % 256 < 256 := by omega

theorem pn_padding (n : Nat) (h : n < 2^62) : n / 2^64 = 0 ∧ n / 2^96 = 0 := by omega

theorem packet_capacity_arithmetic (n : Nat) (h : n ≤ 2^36-32) :
    n+16 < 2^64 ∧ n+1616 < 2^64 ∧ n < 2^61 := by omega

theorem retry_capacity_arithmetic (n c : Nat) (hn : n ≤ 2^61-22) (hc : c ≤ 20) :
    n+c+1 ≤ 2^61-1 ∧ n+c+1441 < 2^64 := by omega

theorem sample_contains_pn_and_tag (n offset count : Nat) (h : offset+20 ≤ n)
    (hc : count ≤ 4) : offset+count+16 ≤ n := by omega

/-- No subtraction of expected-half occurs in the instruction implementation. -/
theorem lower_window_comparison (candidate expected half : Nat) :
    candidate+half ≤ expected ↔ half ≤ expected ∧ candidate ≤ expected-half := by omega

theorem reconstruction_add_bounds (candidate window : Nat) (hw : window ≤ 2^32)
    (h : candidate < 2^62-window) : candidate+window < 2^62 := by omega

theorem reconstruction_sub_bounds (candidate window : Nat) (hc : candidate < 2^62+window)
    (hw : window ≤ candidate) : candidate-window < 2^62 := by omega

theorem reconstruction_word_bounds (expected candidate window : Nat)
    (he : expected ≤ 2^62) (hc : candidate < 2^62+window) (hw : window ≤ 2^32) :
    expected+window/2 < 2^64 ∧ candidate+window/2 < 2^64 := by omega

/-- Modular PN low-byte encoding really preserves all transmitted low bits. -/
theorem truncated_congruence (n window : Nat) (_hw : 0 < window) :
    (n/window*window + n%window) = n := by
  simpa [Nat.mul_comm] using Nat.div_add_mod n window

theorem update_omits_hp (secret : List UInt8) :
    Spec.Crypto.Quic.update secret = do
      let next ← Spec.Crypto.Quic.expandLabel secret "quic ku" 32
      return next ++ (← Spec.Crypto.Quic.expandLabel next "quic key" 16) ++
        (← Spec.Crypto.Quic.expandLabel next "quic iv" 12) := by rfl

theorem tls_initial_label :
    (Asm.Crypto.Quic.Kdf.labelBytes "client in" 32).map Nat.toUInt8 =
    [0,32,15,116,108,115,49,51,32,99,108,105,101,110,116,32,105,110,0] := by decide

/-- Actual two-instruction nonce XOR fragment, with symbolic register state.
The memory loads/stores and fetched whole leaf remain separate obligations. -/
theorem nonce_xor_fragment (s : State) (shift : BitVec 6) :
    execSequence [.SRLI .x6 .x12 shift, .XOR .x5 .x5 .x6] s =
      .ok (((s.setReg .x6 (s.getReg .x12 >>> shift.toNat)).advance.setReg .x5
        (s.getReg .x5 ^^^ (s.getReg .x12 >>> shift.toNat))).advance) := by
  let t := (s.setReg .x6 (s.getReg .x12 >>> shift.toNat)).advance
  change (Except.ok ((t.setReg .x5 (t.getReg .x5 ^^^ t.getReg .x6)).advance) : Except Trap State) = _
  have h5 : t.getReg .x5 = s.getReg .x5 :=
    State.getReg_setReg_other s .x6 .x5 _ (by decide)
  have h6 : t.getReg .x6 = s.getReg .x12 >>> shift.toNat :=
    State.getReg_setReg_same s .x6 _ (by decide)
  rw [h5, h6]

theorem nonce_fragment_in_leaf : ∀ i : Fin 8,
    (Asm.Crypto.Quic.nonceBody.flatten.drop (9+4*i.val)).take 2 =
      [.SRLI .x6 .x12 (BitVec.ofNat 6 (8*(7-i.val))), .XOR .x5 .x5 .x6] := by decide

theorem nonce_byte_truncation (b : BitVec 8) (pn : Word) (shift : Nat) :
    ((b.zeroExtend 64) ^^^ (pn >>> shift)).setWidth 8 = b ^^^ (pn >>> shift).setWidth 8 := by
  simp

theorem reconstruct_success_bound (e t c pn : Nat)
    (h : Spec.Crypto.Quic.reconstruct e t c = .ok pn) : pn < 2^62 := by
  unfold Spec.Crypto.Quic.reconstruct at h
  dsimp at h
  repeat' split at h
  all_goals simp_all [pure, Except.pure, throw, bind, Except.bind]

theorem encode64_roundtrip (n : Nat) (h : n < 2^64) :
    (Spec.Crypto.Sha2.encodeBE 8 n).foldl (fun acc b => 256*acc+b.toNat) 0 = n := by
  simp [Spec.Crypto.Sha2.encodeBE, List.range_succ, Nat.toUInt8]
  omega

set_option maxHeartbeats 1000000 in
theorem encode96_roundtrip (n : Nat) (h : n < 2^96) :
    (Spec.Crypto.Sha2.encodeBE 12 n).foldl (fun acc b => 256*acc+b.toNat) 0 = n := by
  simp [Spec.Crypto.Sha2.encodeBE, List.range_succ, Nat.toUInt8]
  omega

theorem xor_array_injective (iv a b : Array UInt8) (ha : a.size = iv.size) (hb : b.size = iv.size)
    (h : iv.zipWith (· ^^^ ·) a = iv.zipWith (· ^^^ ·) b) : a = b := by
  apply Array.ext (by omega)
  intro i hi hj
  have hiv : i < iv.size := by omega
  have hx := congrArg (fun x : Array UInt8 => x[i]!) h
  simp [ha, hb, hiv] at hx
  have hy := congrArg UInt8.toBitVec hx
  apply UInt8.toBitVec_inj.mp
  simpa using hy

theorem nonce_bytes_injective (iv : Array UInt8) (hi : iv.size = 12) (a b : Nat)
    (ha : a < 2^62) (hb : b < 2^62)
    (h : Spec.Crypto.Quic.nonce iv a = Spec.Crypto.Quic.nonce iv b) : a = b := by
  have ha' : ¬a ≥ 2^62 := by omega
  have hb' : ¬b ≥ 2^62 := by omega
  simp [Spec.Crypto.Quic.nonce, ha', hb', hi, pure, Except.pure] at h
  have he := xor_array_injective iv (Spec.Crypto.Sha2.encodeBE 12 a).toArray
    (Spec.Crypto.Sha2.encodeBE 12 b).toArray
    (by simp [Spec.Crypto.Sha2.encodeBE, hi]) (by simp [Spec.Crypto.Sha2.encodeBE, hi]) h
  have hl := congrArg (fun x : Array UInt8 => x.toList.foldl (fun acc v => 256*acc+v.toNat) 0) he
  simpa [encode96_roundtrip a (by omega), encode96_roundtrip b (by omega)] using hl

end Libp2pAsm.Refinement.Crypto.Quic
