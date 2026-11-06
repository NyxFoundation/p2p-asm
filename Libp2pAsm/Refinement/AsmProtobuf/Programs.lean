import Libp2pAsm.Asm.Codec.ProtobufVarint
import Libp2pAsm.Refinement.AsmCodec.Relocation
import Libp2pAsm.Rv64.Logic.Complete
import Libp2pAsm.Refinement.AsmProtobuf.Specification

namespace Libp2pAsm.Refinement.AsmProtobuf
open Rv64 Rv64.Logic

set_option maxRecDepth 16384

def program : Program := ⟨65536, Asm.Codec.ProtobufVarint.decode.flatten.toArray⟩

theorem lowered : Asm.Codec.ProtobufVarint.decode.lower = .ok program.code := by rfl

theorem leaf_layout : LeafLayout program := by
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem no_stores : ∀ i ∈ program.code, writesMemory i = false := by decide

theorem callee_saved {stop n s t} (h : Trace program stop n s t) : PreservesCallee s t := by
  intro r hr
  apply h.register_frame
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def Cleared (s : State) : Prop :=
  ∀ r ∈ Asm.Crypto.Sha2.cleared, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = 0

def Post (result : Except Spec.Codec.Error Spec.Codec.Decoded) (s : State) : Prop :=
  AsmCodec.DecodePost result s ∧ Cleared s

end Libp2pAsm.Refinement.AsmProtobuf
