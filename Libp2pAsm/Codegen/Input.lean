import Libp2pAsm.Rv64.Basic

namespace Libp2pAsm.Codegen

def parseWord (text : String) : Option Rv64.Word := do
  if text.isEmpty || text.length > 20 then none else do
    let n ← text.toNat?
    if n < 2^64 then some (BitVec.ofNat 64 n) else none

private def nibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def hexLoop : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest => do
    let high ← nibble a
    let low ← nibble b
    let tail ← hexLoop rest
    return (high * 16 + low).toUInt8 :: tail

def parseHex (text : String) : Option (List UInt8) :=
  if text.length > 2048 then none else hexLoop text.toList

def wordBytes (words : List Rv64.Word) : ByteArray :=
  words.foldl (fun (bytes : ByteArray) (word : Rv64.Word) =>
    (List.range 8).foldl (fun (out : ByteArray) (i : Nat) =>
      out.push ((word >>> (8 * i)).toNat.toUInt8)) bytes) ByteArray.empty

end Libp2pAsm.Codegen
