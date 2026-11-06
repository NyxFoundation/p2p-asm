import Libp2pAsm.Refinement.AsmCodec.QuicEntry
import Libp2pAsm.Refinement.AsmCodec.UnsignedEntry
import Libp2pAsm.Refinement.AsmCodec.UnsignedEncodeCorrect

namespace Libp2pAsm.Tests.AsmCodecProof

open Rv64 Rv64.Logic Refinement.AsmCodec

def foreignFrame : List Region := [⟨196608, #[0x11, 0x22], true⟩]

def encoderEntry (value capacity : Word) : State :=
  let s : State := { pc := 65536, memory := heap 131072 #[0xaa, 0xaa, 0xaa] true foreignFrame }
  (((s.setReg .x2 262144).setReg .x10 value).setReg .x11 131072).setReg .x12 capacity

theorem quic_entry_valid : quicEncode.valid (encoderEntry 64 2).memory = true := by cbv
theorem unsigned_entry_valid : unsignedEncode.valid (encoderEntry 128 2).memory = true := by cbv

/-- The universal theorem instantiates to a real owned buffer, guard byte, and writable frame. -/
theorem quic_encoder_example : ∃ done,
    runUntil quicEncode 0 128 (encoderEntry 64 2) = .ok done ∧ done.steps ≤ 128 ∧
    done.state.pc = 0 ∧ Output 0 2 0 done.state ∧
    done.state.memory = heap 131072 #[0x40, 0x40, 0xaa] true foreignFrame ∧
    PreservesCallee (encoderEntry 64 2) done.state ∧
    WriteTrace quicEncode 0 131072 131074 done.steps (encoderEntry 64 2) done.state := by
  obtain ⟨done, he, hn, hp, hout, hc, hw⟩ := quic_encode_runUntil (encoderEntry 64 2)
    131072 #[0xaa, 0xaa, 0xaa] foreignFrame rfl rfl rfl (by decide) (by decide) quic_entry_valid rfl
  exact ⟨done, he, hn, hp, hout.1, hout.2, hc, hw⟩

theorem unsigned_encoder_example : ∃ done,
    runUntil unsignedEncode 0 160 (encoderEntry 128 2) = .ok done ∧ done.steps ≤ 160 ∧
    done.state.pc = 0 ∧ Output 0 2 0 done.state ∧
    done.state.memory = heap 131072 #[0x80, 1, 0xaa] true foreignFrame ∧
    PreservesCallee (encoderEntry 128 2) done.state ∧
    WriteTrace unsignedEncode 0 131072 131074 done.steps (encoderEntry 128 2) done.state := by
  obtain ⟨done, he, hn, hp, hout, hc, hw⟩ := unsigned_encode_runUntil (encoderEntry 128 2)
    131072 #[0xaa, 0xaa, 0xaa] foreignFrame rfl rfl rfl (by decide) (by decide) unsigned_entry_valid rfl
  exact ⟨done, he, hn, hp, hout.1, hout.2, hc, hw⟩

end Libp2pAsm.Tests.AsmCodecProof
