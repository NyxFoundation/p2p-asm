import Libp2pAsm.Asm.Codec.QuicVarint
import Libp2pAsm.Asm.Codec.UnsignedVarint
import Libp2pAsm.Rv64.Logic.Fetch
import Libp2pAsm.Rv64.Logic.State
import Libp2pAsm.Rv64.Logic.Memory
import Libp2pAsm.Spec.Codec.Basic

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

/-- Fixed instruction placement; these arrays are the existing ASM functions verbatim. -/
def program (body : SAsm.Stmt) : Program := ⟨0x10000, body.flatten.toArray⟩

def quicEncode : Program := program Asm.Codec.QuicVarint.encode
def quicDecode : Program := program Asm.Codec.QuicVarint.decode
def unsignedEncode : Program := program Asm.Codec.UnsignedVarint.encode
def unsignedDecode : Program := program Asm.Codec.UnsignedVarint.decode

theorem quicEncode_lower : Asm.Codec.QuicVarint.encode.lower = .ok quicEncode.code := by rfl
theorem quicDecode_lower : Asm.Codec.QuicVarint.decode.lower = .ok quicDecode.code := by rfl
theorem unsignedEncode_lower : Asm.Codec.UnsignedVarint.encode.lower = .ok unsignedEncode.code := by rfl
theorem unsignedDecode_lower : Asm.Codec.UnsignedVarint.decode.lower = .ok unsignedDecode.code := by rfl

/-- Concrete ABI results, shared by success and all three error outcomes. -/
def Output (status first second : Word) (s : State) : Prop :=
  s.getReg .x10 = status ∧ s.getReg .x11 = first ∧ s.getReg .x12 = second

def errorCode : Spec.Codec.Error → Word
  | .truncated => 1 | .overflow => 2 | .nonMinimal => 3

def DecodePost (result : Except Spec.Codec.Error Spec.Codec.Decoded) (s : State) : Prop :=
  match result with
  | .error e => Output (errorCode e) 0 0 s
  | .ok d => Output 0 (BitVec.ofNat 64 d.value) (BitVec.ofNat 64 d.consumed) s

end Libp2pAsm.Refinement.AsmCodec
