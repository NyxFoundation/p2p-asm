import Std
namespace Libp2pAsm.Spec.Multistream

/-- A prefix has some valid UTF-8 completion iff every consumed byte satisfies
these scalar-value encoding intervals. An empty suffix can await continuation. -/
def validUtf8Prefix : List (Nat × Nat) → List UInt8 → Bool
  | _, [] => true
  | (low,high)::tail, b::bs =>
    low ≤ b.toNat && b.toNat ≤ high && validUtf8Prefix tail bs
  | [], b::bs =>
    let n := b.toNat
    if n < 128 then validUtf8Prefix [] bs else
    if 194 ≤ n && n ≤ 223 then validUtf8Prefix [(128,191)] bs else
    if n = 224 then validUtf8Prefix [(160,191),(128,191)] bs else
    if n = 237 then validUtf8Prefix [(128,159),(128,191)] bs else
    if 225 ≤ n && n ≤ 239 then validUtf8Prefix [(128,191),(128,191)] bs else
    if n = 240 then validUtf8Prefix [(144,191),(128,191),(128,191)] bs else
    if n = 244 then validUtf8Prefix [(128,143),(128,191),(128,191)] bs else
    if 241 ≤ n && n ≤ 243 then validUtf8Prefix [(128,191),(128,191),(128,191)] bs else false
termination_by _ bs => bs.length

theorem utf8_rejects_overlong : validUtf8Prefix [] [224,128] = false := by simp [validUtf8Prefix]
theorem utf8_rejects_surrogate : validUtf8Prefix [] [237,160] = false := by simp [validUtf8Prefix]
theorem utf8_rejects_above_unicode : validUtf8Prefix [] [244,144] = false := by simp [validUtf8Prefix]

end Libp2pAsm.Spec.Multistream
