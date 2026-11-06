import Libp2pAsm.Spec.Crypto.Basic

namespace Libp2pAsm.Tests.Crypto

open Spec.Crypto

def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {name}")

private def nibble (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
  else .error "Invalid hexadecimal vector digit."

private def hexPairs : List Char → Except String Bytes
  | [] => .ok []
  | high :: low :: rest => do
    let h ← nibble high
    let l ← nibble low
    return (16*h+l).toUInt8 :: (← hexPairs rest)
  | [_] => .error "Odd hexadecimal vector length."

/-- Strict test fixture parser: malformed expected bytes fail the test process. -/
def hex (text : String) : IO Bytes :=
  match hexPairs text.toList with
  | .ok bytes => pure bytes
  | .error message => throw (IO.userError message)

def ascii (text : String) : Bytes := text.toUTF8.data.toList

def unwrap (name : String) (result : Except Error Bytes) : IO Bytes :=
  match result with
  | .ok bytes => pure bytes
  | .error e => throw (IO.userError s!"FAIL: {name}: {repr e}")

def expectHex (name : String) (result : Except Error Bytes) (expected : String) : IO Unit := do
  let actual ← unwrap name result
  check name (actual == (← hex expected))

def expectError (name : String) (result : Except Error Bytes) (expected : Error) : IO Unit :=
  check name (match result with | .error actual => actual == expected | .ok _ => false)

def byteRange (start count : Nat) : Bytes :=
  (List.range count).map (fun i => (start+i).toUInt8)

structure HashVector where
  name : String
  byteLength : Nat
  messageHex : String
  digestHex : String

def runHashVector (hash : Bytes → Except Error Bytes) (v : HashVector) : IO Unit := do
  let message ← hex v.messageHex
  check s!"should preserve published input length when loading {v.name}"
    (message.length == v.byteLength)
  expectHex s!"should match published bytes when hashing {v.name}" (hash message) v.digestHex

end Libp2pAsm.Tests.Crypto
