import Libp2pAsm.Spec.Codec.Basic

namespace Libp2pAsm.Spec.Codec.QuicVarint

/-- RFC 9000 section 16: the two high bits select a 1, 2, 4, or 8 byte integer. -/
def widthTag (value : Nat) : Nat × Nat :=
  if value < 2^6 then (1, 0)
  else if value < 2^14 then (2, 64)
  else if value < 2^30 then (4, 128)
  else (8, 192)

def bigEndian (count value : Nat) : List UInt8 :=
  (List.range count).map (fun i => (value / 256^(count - 1 - i) % 256).toUInt8)

def encode (value : Nat) : Except Error (List UInt8) :=
  if value ≥ 2^62 then .error .overflow else
    let (width, tag) := widthTag value
    .ok ((tag + value / 256^(width - 1)).toUInt8 :: bigEndian (width - 1) value)

def decode (input : List UInt8) : Except Error Decoded :=
  match input with
  | [] => .error .truncated
  | first :: rest =>
    let width := 2^(first.toNat / 64)
    let body := rest.take (width - 1)
    if body.length < width - 1 then .error .truncated else
      let value := body.foldl
        (fun acc byte => acc * 256 + byte.toNat) (first.toNat % 64)
      .ok ⟨value, width⟩

/-- Bounded inspection is extensionally equal to the original length-based specification. -/
theorem decode_cons (first : UInt8) (rest : List UInt8) :
    decode (first :: rest) =
      if rest.length < 2^(first.toNat / 64) - 1 then .error .truncated
      else .ok ⟨(rest.take (2^(first.toNat / 64) - 1)).foldl
        (fun acc byte => acc * 256 + byte.toNat) (first.toNat % 64), 2^(first.toNat / 64)⟩ := by
  simp only [decode, List.length_take]
  have hg : (min (2^(first.toNat / 64) - 1) rest.length < 2^(first.toNat / 64) - 1) ↔
      rest.length < 2^(first.toNat / 64) - 1 := by omega
  simp only [hg]

theorem encode_overflow (value : Nat) (h : 2^62 ≤ value) :
    encode value = .error .overflow := by
  simp [encode, h]

theorem decode_empty : decode [] = .error .truncated := rfl

end Libp2pAsm.Spec.Codec.QuicVarint
