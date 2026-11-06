import Libp2pAsm.Asm.Codec.Der
import Libp2pAsm.Spec.Codec.Der
import Libp2pAsm.Refinement.AsmProtobuf.ReadContract

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def decoder : Program := ⟨65536,Asm.Codec.Der.decode.flatten.toArray⟩
def encoder : Program := ⟨65536,Asm.Codec.Der.encodeHeader.flatten.toArray⟩

theorem decoder_lowered : Asm.Codec.Der.decode.lower = .ok decoder.code := by rfl
theorem encoder_lowered : Asm.Codec.Der.encodeHeader.lower = .ok encoder.code := by rfl

theorem decoder_layout : LeafLayout decoder := by
  exact ⟨by decide,by decide,by decide,by decide,by decide⟩

theorem encoder_layout : LeafLayout encoder := by
  exact ⟨by decide,by decide,by decide,by decide,by decide⟩

theorem decoder_no_stores : ∀ i ∈ decoder.code, writesMemory i=false := by decide

theorem callee_saved {p stop n s t} (hp : p=decoder ∨ p=encoder)
    (h : Trace p stop n s t) : PreservesCallee s t := by
  intro r hr
  apply h.register_frame
  rcases hp with rfl | rfl
  all_goals rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def DecodePost (result : Except Spec.Codec.Der.Error Spec.Codec.Der.Decoded) (t : State) : Prop :=
  match result with
  | .error e => t.getReg .x10=BitVec.ofNat 64 e.code ∧ t.getReg .x11=0 ∧
      t.getReg .x12=0 ∧ t.getReg .x13=0 ∧ t.getReg .x14=0
  | .ok d => t.getReg .x10=0 ∧ t.getReg .x11=BitVec.ofNat 64 d.tag.toNat ∧
      t.getReg .x12=BitVec.ofNat 64 d.header ∧ t.getReg .x13=BitVec.ofNat 64 d.length ∧
      t.getReg .x14=BitVec.ofNat 64 d.consumed

end Libp2pAsm.Refinement.AsmDer
