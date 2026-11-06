import Libp2pAsm.Refinement.Quic.Wire.PermissionCode
import Libp2pAsm.Spec.Quic.Wire.Frame
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Refinement.Quic.Wire
open Rv64

def permissionCheck (tag level role : Nat) : Bool := Id.run do
  let initial : State := {pc := 0x10000, memory := ⟨#[]⟩}
  let initial := (((initial.setReg .x1 0x80000).setReg .x10 (BitVec.ofNat 64 tag)).setReg
    .x11 (BitVec.ofNat 64 level)).setReg .x12 (BitVec.ofNat 64 role)
  let .ok done := runLoop ⟨0x10000,permissionCode⟩ 0x80000 500 initial 0 | return false
  let lev := if level == 0 then Spec.Quic.Wire.Level.initial else
    if level == 1 then .handshake else if level == 2 then .zeroRtt else .oneRtt
  let yes := Spec.Quic.Wire.permitted tag lev (role == 1)
  return done.state.getReg .x10 == (if yes then 0 else 9) &&
    done.state.getReg .x11 == (if yes && Spec.Quic.Wire.ackEliciting tag then 1 else 0) &&
    done.state.getReg .x12 == (if yes && Spec.Quic.Wire.countsInFlight tag then 1 else 0) &&
    done.state.pc == 0x80000

end Libp2pAsm.Refinement.Quic.Wire
