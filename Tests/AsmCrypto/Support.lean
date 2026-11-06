import Libp2pAsm.Asm.Crypto.SHA256
import Libp2pAsm.Asm.Crypto.SHA512
import Libp2pAsm.Spec.Crypto.SHA256
import Libp2pAsm.Spec.Crypto.SHA512
import Libp2pAsm.Codegen.Assembly
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.AsmCrypto

open Rv64
open Asm.Crypto.Sha2

def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: should {name}")

def wordBytes (words : List Word) : Array UInt8 :=
  (words.flatMap fun (w : Word) => (List.range 8).map fun i =>
    ((w >>> (8*i) : Word).toNat).toUInt8).toArray

def readLE (bytes : Array UInt8) (offset : Nat) : Word :=
  (List.range 8).foldl (fun (w : Word) i =>
    w ||| (BitVec.ofNat 64 bytes[offset+i]!.toNat <<< (8*i))) 0

def constants (v : Variant) : Array UInt8 :=
  wordBytes (match v with
    | .sha256 => Spec.Crypto.SHA256.roundConstants.toList.map (·.zeroExtend 64)
    | .sha512 => Spec.Crypto.SHA512.roundConstants.toList)

def specState (w : Nat) (bytes : Array UInt8) : Spec.Crypto.Sha2.State w :=
  let wordAt := fun i => BitVec.ofNat w (readLE bytes (8*i)).toNat
  ⟨wordAt 0, wordAt 1, wordAt 2, wordAt 3, wordAt 4, wordAt 5, wordAt 6, wordAt 7⟩

def stateBytes (s : Spec.Crypto.Sha2.State w) : Array UInt8 :=
  wordBytes ([s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h].map (·.zeroExtend 64))

def reference (v : Variant) (state block : Array UInt8) : Array UInt8 :=
  match v with
  | .sha256 => stateBytes (Spec.Crypto.SHA256.compress (specState 32 state)
      (Vector.ofFn fun i => block[i.val]!))
  | .sha512 => stateBytes (Spec.Crypto.SHA512.compress (specState 64 state)
      (Vector.ofFn fun i => block[i.val]!))

def guarded (bytes : Array UInt8) (before : Nat := 8) : Array UInt8 :=
  Array.replicate before 0xa5 ++ bytes ++ Array.replicate 8 0x5a

def seedReg (case : Nat) (i : Fin 32) : Word :=
  BitVec.ofNat 64 (0x8192a3b4c5d6e700 + 64*case + i.val)

def initial (v : Variant) (case : Nat) (state block : Array UInt8) : State :=
  let memory : Memory := { regions := #[
    ⟨0x20000, guarded state, true⟩,
    ⟨0x30000, guarded block (8 + case % 8), false⟩,
    ⟨0x40000, guarded (constants v), false⟩,
    ⟨0x50000, guarded (Array.replicate (v.rounds*8) 0xcc), true⟩,
    ⟨0x60000, Array.replicate 96 0x69, true⟩] }
  let s : State := { regs := Vector.ofFn (seedReg case), pc := 0x10000, memory := memory }
  let s := (((s.setReg .x1 0x18000).setReg .x2 0x60050).setReg .x3 0x70000)
  let s := (s.setReg .x10 0x20008).setReg .x11 (BitVec.ofNat 64 (0x30008 + case % 8))
  (s.setReg .x12 0x50008).setReg .x13 0x40008

def registerBytes (s : State) : Array UInt8 :=
  wordBytes ((List.finRange 32).map fun i => if i.val == 0 then 0 else s.regs[i])

def snapshot (s : State) : ByteArray :=
  ⟨s.memory.regions.foldl (fun out r => out ++ r.bytes) (registerBytes s)⟩

def expected (v : Variant) (s : State) (state block : Array UInt8) : State :=
  let regions := s.memory.regions.mapIdx fun i r =>
    let bytes := if i == 0 then guarded (reference v state block)
      else if i == 3 then guarded (Array.replicate (v.rounds*8) 0)
      else if i == 4 then Array.replicate 16 0x69 ++ Array.replicate 64 0 ++ Array.replicate 16 0x69
      else r.bytes
    { r with bytes := bytes }
  let s := cleared.foldl (fun acc r => acc.setReg r 0) s
  { s with pc := 0x18000, memory := ⟨regions⟩ }

end Libp2pAsm.Tests.AsmCrypto
