import Lean
import Libp2pAsm.Asm.Crypto.Weierstrass.Ecdsa
import Libp2pAsm.Spec.Crypto.Weierstrass.Ecdsa
import Libp2pAsm.Codegen.Assembly
import Libp2pAsm.Rv64.Execution
import Tests.AsmCrypto.Trace
import Tests.Weierstrass.Fragments

namespace Libp2pAsm.Tests.Weierstrass
open Rv64 Asm.Crypto Asm.Crypto.Weierstrass

structure Fixture where
  label : String
  regions : Array (Array Nat)
  args : Array Nat
  expected : Array Nat
  outputRegion : Nat := 2
  outputOffset : Nat := 8
  status : Nat := 0
  wipeRegion : Nat := 3
  wipeLength : Nat := 1024
  stackDepth : Nat := 224
  stack : Nat := 0x251000
  traceGroup : String := ""
  deriving Lean.FromJson, Inhabited

def base (i : Nat) : Nat := 0x200000 + 0x10000*i
def stackTop : Nat := base 5 + 4096
def guard (xs : Array UInt8) : Array UInt8 :=
  Array.replicate 8 0xa5 ++ xs ++ Array.replicate 8 0x5a

def wordBytes (xs : List Nat) : Array UInt8 :=
  (xs.flatMap fun x => (List.range 8).map fun i => (x / 2^(8*i) % 256).toUInt8).toArray

def initial (f : Fixture) : State := Id.run do
  let regions := f.regions.mapIdx fun i xs =>
    (⟨BitVec.ofNat 64 (base i), xs.map Nat.toUInt8, i ≥ 2⟩ : Region)
  let mut s : State := {
    pc := 0x10000
    memory := ⟨regions⟩
    regs := Vector.ofFn fun i => BitVec.ofNat 64 (0x8192a3b4c5d6e700+i.val) }
  s := ((s.setReg .x1 0x80000).setReg .x2 (BitVec.ofNat 64 f.stack)).setReg .x3 0x280000
  for (r,n) in ([Reg.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17].zip f.args.toList) do
    s := s.setReg r (BitVec.ofNat 64 n)
  return s

def snapshot (s : State) : ByteArray :=
  let rs := wordBytes ((List.finRange 32).map fun i => if i.val == 0 then 0 else s.regs[i].toNat)
  ⟨s.memory.regions.foldl (fun xs r => xs ++ r.bytes) rs⟩

def replace (xs : Array UInt8) (off : Nat) (ys : Array UInt8) : Array UInt8 :=
  xs.extract 0 off ++ ys ++ xs.extract (off+ys.size) xs.size

def expected (f : Fixture) (start : State) : State :=
  let regions := start.memory.regions.mapIdx fun i r =>
    let xs := if i == f.outputRegion then replace r.bytes f.outputOffset (f.expected.map Nat.toUInt8)
      else if i == f.wipeRegion then replace r.bytes 8 (Array.replicate f.wipeLength 0)
      else if i == 5 then replace r.bytes (4096-f.stackDepth) (Array.replicate f.stackDepth 0)
      else r.bytes
    { r with bytes := xs }
  let s := Sha2.cleared.foldl (fun s r => s.setReg r 0) start
  { s.setReg .x10 (BitVec.ofNat 64 f.status) with pc := 0x80000, memory := ⟨regions⟩ }

def coreProgram (c : Spec.Crypto.Weierstrass.Curve) (kind : String) : Except String SAsm.Stmt :=
  if kind == "public" then Asm.Crypto.Weierstrass.publicKey c else
  if kind == "parseder" then parseFragment c else
  if kind == "encodeder" then encodeFragment c else
  if kind == "signnonce" then nonceFragment c else
  if kind == "signfailure" then failureFragment c else
  if kind == "ecdh" then Asm.Crypto.Weierstrass.ecdh c else
  if kind == "sign" then Asm.Crypto.Weierstrass.sign c else
  if kind == "signcompact" then Asm.Crypto.Weierstrass.sign c true else
  if kind == "verify" then Asm.Crypto.Weierstrass.verify c else
  if kind == "verifyzero" then Asm.Crypto.Weierstrass.verify c else
  if kind == "verifycompact" then Asm.Crypto.Weierstrass.verify c true else
  if kind == "verifylow" then Asm.Crypto.Weierstrass.verify c false true else
  if kind == "pointadd" || kind == "pointmul" then Link.program (.seq [
    .asm Util.enter, .asm (Util.block [.ADDI .x8 .x13 0, .ADDI .x9 .x12 0]),
    (if kind == "pointadd" then .asm (wordsCopy .x8 .x10 0 0 12) else
      .asm (decode .x8 .x10 0 0)),
    .asm (wordsCopy .x8 .x11 96 0 12),
    op (if kind == "pointadd" then 8 else 9) 192 0 96, op 10 192 192 192,
    .asm (encode .x9 .x8 0 192), .asm (encode .x9 .x8 32 224),
    .asm (zeroWords .x8 0 128), .asm (Util.block [.ADDI .x10 .x0 0]),
    .asm Util.leave]) (callees c) else
  let target := if kind == "mul" then 0 else if kind == "add" then 1 else
    if kind == "sub" then 2 else if kind == "qmul" then 3 else
    if kind == "qadd" then 4 else if kind == "qsub" then 5 else if kind == "inv" then 6 else 7
  Link.program (.seq [.asm Util.enter,
    .asm (Util.block [.ADDI .x8 .x13 0, .ADDI .x9 .x12 0]),
    .asm (decode .x8 .x10 0 0), .asm (decode .x8 .x11 32 0),
    op target 64 0 32, .asm (encode .x9 .x8 0 64),
    .asm (zeroWords .x8 0 128), .asm (Util.block [.ADDI .x10 .x0 0]), .asm Util.leave]) (callees c)

def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

end Libp2pAsm.Tests.Weierstrass
