import Libp2pAsm.Refinement.Codec.UnsignedHelpers

namespace Libp2pAsm.Refinement.Codec.UnsignedVarint

open Spec.Codec Spec.Codec.UnsignedVarint

/-- The decoder cannot inspect a byte past its fuel bound, including on errors. -/
theorem decodeLoop_take (fuel : Nat) (input : List UInt8) (acc shift consumed : Nat) :
    decodeLoop fuel (input.take fuel) acc shift consumed =
      decodeLoop fuel input acc shift consumed := by
  induction fuel generalizing input acc shift consumed with
  | zero => rfl
  | succ fuel ih =>
    cases input with
    | nil => rfl
    | cons byte rest =>
      simp only [List.take_succ_cons, decodeLoop]
      split
      · rfl
      · exact ih rest _ _ _

theorem decode_bounded (input : List UInt8) : decode (input.take 9) = decode input :=
  decodeLoop_take 9 input 0 0 0

theorem decodeLoop_continuations (leading suffix : List UInt8) (fuel acc shift consumed : Nat)
    (hl : leading.length = fuel) (hc : ∀ byte ∈ leading, 128 ≤ byte.toNat) :
    decodeLoop fuel (leading ++ suffix) acc shift consumed = .error .overflow := by
  induction leading generalizing fuel acc shift consumed with
  | nil => simp only [List.length_nil] at hl; subst fuel; rfl
  | cons byte rest ih =>
    cases fuel with
    | zero => simp at hl
    | succ fuel =>
      have hb : ¬byte.toNat < 128 := by have := hc byte (by simp); omega
      simp only [List.cons_append, decodeLoop, hb, ↓reduceIte]
      exact ih fuel _ _ _ (by simpa using hl) (fun b hm => hc b (by simp [hm]))

/-- Nine continuation bytes overflow regardless of any following bytes. -/
theorem decode_overflow (leading suffix : List UInt8) (hl : leading.length = 9)
    (hc : ∀ byte ∈ leading, 128 ≤ byte.toNat) :
    decode (leading ++ suffix) = .error .overflow :=
  decodeLoop_continuations leading suffix 9 0 0 0 hl hc

theorem decodeLoop_truncated (fuel value : Nat) (bytes : List UInt8)
    (he : encodeLoop fuel value = .ok bytes) (n acc shift consumed : Nat) (hn : n < bytes.length) :
    decodeLoop fuel (bytes.take n) acc shift consumed = .error .truncated := by
  induction fuel generalizing value bytes n acc shift consumed with
  | zero => simp [encodeLoop] at he
  | succ fuel ih =>
    by_cases ht : value < 128
    · simp only [encodeLoop_step, ht, ↓reduceIte, Except.ok.injEq] at he
      subst bytes
      have hz : n = 0 := by simpa using hn
      subst n; rfl
    · cases hr : encodeLoop fuel (value / 128) with
      | error e => simp only [encodeLoop_step, ht, ↓reduceIte, hr] at he; cases he
      | ok tail =>
        simp only [encodeLoop_step, ht, ↓reduceIte, hr, Except.ok.injEq] at he
        subst bytes
        cases n with
        | zero => rfl
        | succ n =>
          have hc : ¬value % 128 + 128 < 128 := by omega
          simp only [List.take_succ_cons, decodeLoop, continuation_byte, hc, ↓reduceIte]
          exact ih _ _ hr n _ _ _ (by simpa using hn)

/-- Every proper leading of an encoded value is rejected as truncated. -/
theorem decode_truncated (value : Nat) (bytes : List UInt8) (he : encode value = .ok bytes)
    (n : Nat) (hn : n < bytes.length) : decode (bytes.take n) = .error .truncated := by
  simp only [encode] at he
  split at he
  · cases he
  · exact decodeLoop_truncated 9 value bytes he n 0 0 0 hn

theorem decodeLoop_nonMinimal (leading suffix : List UInt8) (fuel acc shift consumed : Nat)
    (hl : leading.length < fuel) (hp : 0 < consumed + leading.length)
    (hc : ∀ byte ∈ leading, 128 ≤ byte.toNat) :
    decodeLoop fuel (leading ++ (0 :: suffix)) acc shift consumed = .error .nonMinimal := by
  induction leading generalizing fuel acc shift consumed with
  | nil =>
    cases fuel with
    | zero => simp at hl
    | succ fuel =>
      have hp' : 0 < consumed := by simpa using hp
      simp [decodeLoop, hp']
  | cons byte rest ih =>
    cases fuel with
    | zero => simp at hl
    | succ fuel =>
      have hb : ¬byte.toNat < 128 := by have := hc byte (by simp); omega
      simp only [List.cons_append, decodeLoop, hb, ↓reduceIte]
      apply ih fuel _ _ _ (by simpa using hl) (by simpa [Nat.add_assoc, Nat.add_comm 1] using hp)
      exact fun b hm => hc b (by simp [hm])

/-- A zero terminal group after any nonempty continuation leading is non-minimal. -/
theorem decode_nonMinimal (leading suffix : List UInt8) (hl : leading.length < 9)
    (hp : 0 < leading.length) (hc : ∀ byte ∈ leading, 128 ≤ byte.toNat) :
    decode (leading ++ (0 :: suffix)) = .error .nonMinimal :=
  decodeLoop_nonMinimal leading suffix 9 0 0 0 hl (by simpa using hp) hc

theorem decodeLoop_incomplete (input : List UInt8) (fuel acc shift consumed : Nat)
    (hl : input.length < fuel) (hc : ∀ byte ∈ input, 128 ≤ byte.toNat) :
    decodeLoop fuel input acc shift consumed = .error .truncated := by
  induction input generalizing fuel acc shift consumed with
  | nil =>
    cases fuel with
    | zero => simp at hl
    | succ fuel => rfl
  | cons byte rest ih =>
    cases fuel with
    | zero => simp at hl
    | succ fuel =>
      have hb : ¬byte.toNat < 128 := by have := hc byte (by simp); omega
      simp only [decodeLoop, hb, ↓reduceIte]
      exact ih fuel _ _ _ (by simpa using hl) (fun b hm => hc b (by simp [hm]))

/-- An unterminated input shorter than nine bytes is truncated, not overflowing. -/
theorem decode_incomplete (input : List UInt8) (hl : input.length < 9)
    (hc : ∀ byte ∈ input, 128 ≤ byte.toNat) : decode input = .error .truncated :=
  decodeLoop_incomplete input 9 0 0 0 hl hc

end Libp2pAsm.Refinement.Codec.UnsignedVarint
