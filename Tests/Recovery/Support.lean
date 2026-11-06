import Libp2pAsm.Spec.Quic.Recovery.Raw
import Libp2pAsm.Spec.Quic.Recovery.Memory
import Libp2pAsm.Asm.Quic.Recovery.Api
import Tests.HashCrypto.Support

namespace Libp2pAsm.Tests.Recovery
open Rv64 AsmCrypto
open Spec.Quic.Recovery

def words (bytes : Array UInt8) : Array Nat :=
  (List.range (bytes.size/8)).toArray.map (fun i => (readLE bytes (8*i)).toNat)

def invoke (kind : String) (state input : Array Nat) : Transition := do
  let v := wordAt input
  if kind == "init" then
    let c : Config := ⟨v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15⟩
    return (← init c (v 1) (v 3) (v 2) (v 4 != 0), {})
  let s ← stateFromWords state
  unless v 1 == s.generation do throw .stale
  let now := v 2
  return ← match kind with
  | "keys" => installKeys s now (v 3)
  | "reserve" => reserve s now ⟨v 3,v 4,v 5,v 6 % 2 == 1,v 6 / 2 % 2 == 1, v 7,v 8,v 9,v 10,v 6 / 4 % 2 == 1,v 6 / 8 % 2 == 1⟩
  | "result" => result s (v 1) (v 3) (v 4) now (v 5) (v 6)
  | "retry" => retry s (v 1) (v 3) now
  | "expire" => expire s (v 1) (v 3) now
  | "receive" => receiveBytes s now (v 3) (v 4)
  | "validate" => validatePath s now (v 3) (v 4)
  | "challenge" => challenge s now (v 3) (v 4) (v 5)
  | "response" => response s now (v 3) (v 4) (v 5)
  | "handshake" => handshake s now (v 3 != 0) (v 4 != 0) (v 5 != 0)
  | "ack" => beginAck s now (v 3) (v 4) ((List.range (v 5)).toArray.map fun i => ⟨v (16+2*i),v (17+2*i)⟩)
  | "resume" => resume s (v 1)
  | "timer" => (timer s now).map (fun a => (s,a))
  | "pto" => firePto s now (v 3) (v 4)
  | "discard" => beginDiscard s now (v 3)
  | "loss" => beginLoss s now (v 3)
  | "newpath" => newPath s now (v 3) (v 4)
  | "activate" => activatePath s now (v 3) (v 4)
  | "persistent" => collapse s now (v 3) (v 4)
  | _ => throw .malformed

def regionPayload (s : Rv64.State) (i : Nat) : Array UInt8 :=
  let bytes := (s.memory.regions[i]?.getD ⟨0,#[],false⟩).bytes
  bytes.extract 8 (bytes.size-8)

def expected (c : HashCrypto.Case) (answer : Transition) (wipeWork := true) : Rv64.State :=
  let status := match answer with | .ok _ => 0 | .error err => err.code
  let regions := c.start.memory.regions.mapIdx fun i r =>
    let bytes := if i == 3 && wipeWork then HashCrypto.replaced r.bytes 8 (Array.replicate (r.bytes.size-16) 0)
      else match answer with
        | .ok (s,a) => if i == 2 then HashCrypto.replaced r.bytes 8 (wordBytes (s.words.toList.map (BitVec.ofNat 64)))
          else if i == 5 then HashCrypto.replaced r.bytes 8 (wordBytes (a.words.toList.map (BitVec.ofNat 64))) else r.bytes
        | .error _ => r.bytes
    {r with bytes := bytes}
  let s := Asm.Crypto.Sha2.cleared.foldl (fun s r => s.setReg r 0) c.start
  {s.setReg .x10 (BitVec.ofNat 64 status) with pc := 0x80000, memory := ⟨regions⟩}

def permitted (s : Rv64.State) (event : AsmCrypto.Event) : Bool := match event.access with
  | none => true
  | some (write,width,addr) => ((s.memory.regions.mapIdx fun i r => (i,r)).any fun (i,r) =>
    i != 1 && (!write || r.writable) && r.base.toNat+8 ≤ addr.toNat &&
    addr.toNat+width ≤ r.base.toNat+(if i == 5 then 72 else r.bytes.size-8))

def execute (p : Program) (before : Rv64.State) : Nat → Rv64.State → Nat → Except String (Rv64.State × Nat)
  | 0,_,_ => .error "quantum exhausted"
  | fuel+1,s,n => do
    if s.pc == 0x80000 then return (s,n)
    let i ← (p.fetch s.pc).mapError reprStr
    unless permitted before (AsmCrypto.event i s) do throw s!"access footprint {repr (AsmCrypto.event i s)}"
    execute p before fuel (← (execInstr i s).mapError reprStr) (n+1)

end Libp2pAsm.Tests.Recovery
