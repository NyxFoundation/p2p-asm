import Libp2pAsm.Spec.Identity.PublicKey
import Libp2pAsm.Asm.Identity.PublicKey
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.Identity
open Rv64

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}")

private def parse (data : List UInt8) (kind offset size : Nat) : IO Unit := do
  let .ok v := Spec.Identity.PublicKey.decode data
    | throw (IO.userError "public-key Spec rejected fixture")
  check "should extract the final required protobuf fields"
    (v.kind == kind && v.offset == offset && v.length == size)

def run : IO Unit := do
  let key : List UInt8 := (List.range 32).map Nat.toUInt8
  parse ([8, 1, 18, 32] ++ key) 1 4 32
  parse ([18, 32] ++ key ++ [8, 1]) 1 2 32
  parse ([8, 1, 18, 32] ++ key ++ [10, 0]) 1 4 32
  parse ([8, 2, 8, 1, 18, 0, 18, 32] ++ key) 1 8 32
  parse ([0x1b, 8, 2, 18, 0, 0x1c, 8, 1, 18, 32] ++ key) 1 10 32
  parse ([0x88, 0, 0x81, 0, 18, 0xa0, 0] ++ key) 1 7 32
  for bytes in [[], [8, 1], [18, 32] ++ key, [8, 3, 18, 32] ++ key,
      [8, 1, 18, 31] ++ key, [0x1c, 8, 1, 18, 32] ++ key,
      [0x1b, 0x24, 8, 1, 18, 32] ++ key] do
    check "should reject absent, unsupported, wrong-size or malformed key fields"
      (match Spec.Identity.PublicKey.decode bytes with | .error _ => true | _ => false)
  let .ok id := Spec.Identity.PublicKey.peerId 1 key
    | throw (IO.userError "peer ID Spec rejected fixture")
  check "should use identity multihash of canonical PublicKey serialization"
    (id == [0, 36, 8, 1, 18, 32] ++ key)
  IO.println "PASS: should parse protobuf public keys and derive canonical inline Peer IDs"

end Libp2pAsm.Tests.Identity
