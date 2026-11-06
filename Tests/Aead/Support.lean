import Lean
import Tests.Aead.Spec
import Libp2pAsm.Asm.Crypto.GCM.Api
import Libp2pAsm.Codegen.Assembly
import Libp2pAsm.Rv64.Execution
import Tests.AsmCrypto.Trace

namespace Libp2pAsm.Tests.Aead
open Rv64
open Asm.Crypto

structure Fixture where
  label : String
  key : Array Nat := #[]
  nonce : Array Nat := #[]
  aad : Array Nat := #[]
  input : Array Nat := #[]
  output : Array Nat := #[]
  expected : Array Nat := #[]
  status : Nat := 0
  keyLength : Nat := 16
  nonceLength : Nat := 12
  aadLength : Nat := 0
  inputLength : Nat := 0
  capacity : Nat := 0
  workspaceCapacity : Nat := 1280
  alignment : Nat := 0
  traceGroup : String := ""
  deriving Lean.FromJson, Repr, Inhabited

def bytes (xs : Array Nat) : Array UInt8 := xs.map Nat.toUInt8

def wordBytes (xs : List Nat) : Array UInt8 :=
  (xs.flatMap fun x => (List.range 8).map fun i => (x / 2^(8*i) % 256).toUInt8).toArray

def guard (xs : Array UInt8) (alignment : Nat := 0) : Array UInt8 :=
  Array.replicate (8+alignment) 0xa5 ++ xs ++ Array.replicate 8 0x5a

def base (i : Nat) : Nat := 0x200000 + 0x10000*i

def addr (f : Fixture) (i : Nat) : Nat := base i + 8 + (if i < 1 || i > 5 then 0 else f.alignment)

def scratchSize (kind : String) : Nat :=
  if kind == "seal" || kind == "open" then 1280 else if kind == "ghash" then 0 else 1024

def frameSize (kind : String) : Nat :=
  if kind == "seal" || kind == "open" then 128 else if kind == "aes" || kind == "hp" then 16 else 0

def descriptor (f : Fixture) : Array UInt8 := wordBytes [
  addr f 1, f.keyLength, addr f 2, f.nonceLength, addr f 3, f.aadLength,
  addr f 4, f.inputLength, addr f 5, f.capacity, addr f 6, f.workspaceCapacity]

def program (kind : String) : SAsm.Stmt :=
  match kind with
  | "expand" => AES.expand | "aes" => AES.encrypt | "hp" => AES.headerProtection
  | "ghash" => GCM.update | "seal" => GCM.seal | "open" => GCM.open
  | _ => Asm.sequence [AES.subBytes 16, AES.wipe .x12 1024, AES.finish 0]

def initial (kind : String) (f : Fixture) : State := Id.run do
  let data := #[descriptor f, bytes f.key, bytes f.nonce, bytes f.aad,
    bytes f.input, bytes f.output, Array.replicate (scratchSize kind) 0xcc]
  let regions := data.mapIdx fun i xs =>
    (⟨BitVec.ofNat 64 (base i), guard xs (if i > 0 && i < 6 then f.alignment else 0), i ≥ 5⟩ : Region)
  let memory := Memory.mk (regions.push ⟨BitVec.ofNat 64 (base 7), Array.replicate 160 0x69, true⟩)
  let mut s : State := {
    pc := 0x10000
    memory := memory
    regs := Vector.ofFn fun i => BitVec.ofNat 64 (0x8192a3b4c5d6e700 + i.val) }
  s := (((s.setReg .x1 0x80000).setReg .x2 0x270090).setReg .x3 0x280000)
  let args := match kind with
    | "expand" => [addr f 1, f.keyLength, addr f 5, f.capacity, addr f 6, f.workspaceCapacity]
    | "aes" | "hp" => [addr f 1, addr f 4, f.inputLength, addr f 5, f.capacity, addr f 6, f.workspaceCapacity]
    | "ghash" => [addr f 5, addr f 1, addr f 4]
    | "seal" | "open" => [addr f 0]
    | _ => [0, addr f 5, addr f 6]
  for (r, n) in ([Reg.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17].zip args) do
    s := s.setReg r (BitVec.ofNat 64 n)
  return s

def registerBytes (s : State) : Array UInt8 :=
  wordBytes ((List.finRange 32).map fun i => if i.val == 0 then 0 else s.regs[i].toNat)

def snapshot (s : State) : ByteArray :=
  ⟨s.memory.regions.foldl (fun xs r => xs ++ r.bytes) (registerBytes s)⟩

def expectedState (kind : String) (f : Fixture) (start : State) : State :=
  let executed := f.status == 0 || (kind == "open" && f.status == 6)
  let regions := start.memory.regions.mapIdx fun i r =>
    let xs := if i == 5 then guard (bytes f.expected) f.alignment
      else if i == 6 && executed then guard (Array.replicate (scratchSize kind) 0)
      else if i == 7 && executed then
        Array.replicate (144-frameSize kind) 0x69 ++ Array.replicate (frameSize kind) 0 ++ Array.replicate 16 0x69
      else r.bytes
    { r with bytes := xs }
  let s := AES.clearRegs.foldl (fun acc r => acc.setReg r 0) start
  { s.setReg .x10 (BitVec.ofNat 64 f.status) with pc := 0x80000, memory := ⟨regions⟩ }

def footprint (kind : String) (f : Fixture) (e : AsmCrypto.Event) : Bool :=
  match e.access with
  | none => true
  | some (write, width, address) =>
    let inside := fun a n => a ≤ address.toNat && address.toNat+width ≤ a+n
    let executed := f.status == 0 || (kind == "open" && f.status == 6)
    let desc := !write && (kind == "open" || kind == "seal") && inside (addr f 0) 96
    desc || (executed && (
      (!write && (inside (addr f 1) f.key.size || inside (addr f 2) f.nonce.size ||
        inside (addr f 3) f.aad.size || inside (addr f 4) f.input.size)) ||
      inside (addr f 5) f.output.size || inside (addr f 6) (scratchSize kind) ||
      inside (base 7 + 144 - frameSize kind) (frameSize kind)))

def validateFixture (f : Fixture) : IO Unit := do
  check "bound fixture arrays and bytes" ([f.key,f.nonce,f.aad,f.input,f.output,f.expected].all
    fun a => a.size ≤ 8192 && a.all (· < 256))
  check "bound metadata and preserve output size" (f.alignment < 8 && f.status ≤ 8 &&
    f.output.size == f.expected.size && [f.keyLength,f.nonceLength,f.aadLength,
      f.inputLength,f.capacity,f.workspaceCapacity].all (· < 2^64))

end Libp2pAsm.Tests.Aead
