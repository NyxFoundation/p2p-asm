import Tests.QuicCrypto.Support

namespace Libp2pAsm.Tests.QuicCrypto
open Rv64

def readBytes (s : State) (base count : Nat) : Except String (Array UInt8) := do
  (List.range count).foldlM (fun out i => do
    let b ← (s.memory.load 1 (BitVec.ofNat 64 (base+i))).mapError reprStr
    return out.push b.toNat.toUInt8) #[]

/-- Observe the five actual HP output stores before the workspace wipe, then
compare the real ciphertext sample in memory. No implementation intermediate
is provided by the Spec or Python at execution time. -/
def observeHP (p : Program) (sampleAddr : Nat) (sample mask : Array UInt8) :
    Nat → State → Nat → Except String Unit
  | 0,_,_ => .error "HP observation fuel"
  | fuel+1,s,count => do
    let instruction ← (p.fetch s.pc).mapError reprStr
    let event := AsmCrypto.event instruction s
    let next ← (execInstr instruction s).mapError reprStr
    let matched := event.access == some (true,1,BitVec.ofNat 64 (0x400008+288+count))
    let count := if matched then count+1 else count
    if count == 5 then
      unless (← readBytes next (0x400008+288) 5) == mask do throw "RFC HP mask differs"
      unless (← readBytes next sampleAddr 16) == sample do throw "RFC ciphertext sample differs"
      return ()
    observeHP p sampleAddr sample mask fuel next count

end Libp2pAsm.Tests.QuicCrypto
