import Libp2pAsm.Spec.Crypto.Curve25519.X25519

open Libp2pAsm.Spec.Crypto.Curve25519

/-- RFC 7748 recurrence, independently executed over unbounded modular integers. -/
def main (args : List String) : IO Unit := do
  let [countText,path] := args | throw (IO.userError "usage: count output-file")
  let some count := countText.toNat? | throw (IO.userError "invalid count")
  unless 0 < count && count ≤ 1000 do throw (IO.userError "count out of test bounds")
  let mut k := encodeLE 9 32
  let mut u := k
  for _ in List.range count do
    let .ok next := X25519.raw k u | throw (IO.userError "spec iteration failed")
    u := k
    k := next
  IO.FS.writeBinFile path ⟨k.toArray⟩
