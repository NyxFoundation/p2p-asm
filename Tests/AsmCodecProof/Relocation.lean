import Libp2pAsm.Refinement.AsmCodec.EmbeddedDecode
import Libp2pAsm.Refinement.AsmCodec.EmbeddedEncode

namespace Libp2pAsm.Tests.AsmCodecProof

open Rv64 Rv64.Logic Refinement.AsmCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All four routines share one image, with a real continuation before the leaves.
The continuation deliberately writes a callee-saved register if mistakenly fetched. -/
def combinedImage : Program := ⟨524288,
  #[.ADDI .x8 .x0 17] ++ quicEncode.code ++ quicDecode.code ++
    unsignedEncode.code ++ unsignedDecode.code ++ #[.SD .x10 .x11 0]⟩

def relocatedEntry (pc a0 a1 a2 : Word) (bytes : Array UInt8) : State :=
  let s : State := { regs := Vector.replicate 32 0xdeadbeef, pc := pc, memory := heap 65536 bytes true [] }
  (((s.setReg .x1 524288).setReg .x10 a0).setReg .x11 a1).setReg .x12 a2

/-- The data buffer occupies the old proof code address, demonstrating that only
separation from the actual containing image is needed. -/
def embeddedQuicEncoder : State := relocatedEntry 524292 64 65536 2 #[0xa5, 0xa5, 0xcc]
def embeddedQuicDecoder : State := relocatedEntry 524480 65536 2 91 #[0x40, 0, 0xcc]
def embeddedUnsignedEncoder : State := relocatedEntry 524600 128 65536 2 #[0xa5, 0xa5, 0xcc]
def embeddedUnsignedDecoder : State := relocatedEntry 524740 65536 2 91 #[0x80, 0, 0xcc]

private theorem combined_valid (s : State) (bytes : Array UInt8)
    (hm : s.memory = heap 65536 bytes true []) (hb : 0 < bytes.size) (hs : bytes.size ≤ 8) :
    ValidImage combinedImage s.memory := by
  rw [hm]
  refine ⟨?_, by decide, by decide, by decide, ?_⟩
  · simp [heap, LeanAsm.Rv64.Memory.valid, LeanAsm.Rv64.Region.valid, LeanAsm.Rv64.Region.endAddr]; omega
  · intro r hr hw
    simp [heap] at hr
    subst r
    left
    change 65536 + bytes.size ≤ 524288
    omega

theorem quic_encoder_invocation :
    Invocation quicEncode combinedImage 524292 (embeddedQuicEncoder.getReg .x1) 1
      embeddedQuicEncoder.memory := by
  refine ⟨combined_valid _ #[0xa5, 0xa5, 0xcc] rfl (by decide) (by decide),
    ⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide, ?_⟩⟩
  have h : ∀ j : Fin 47, combinedImage.code[1+j.val]'(by change 1+j.val < 158; omega) =
      quicEncode.code[j.val]'j.isLt := by decide
  intro j hj
  exact h ⟨j, hj⟩

theorem quic_decoder_invocation :
    Invocation quicDecode combinedImage 524480 (embeddedQuicDecoder.getReg .x1) 48
      embeddedQuicDecoder.memory := by
  refine ⟨combined_valid _ #[0x40, 0, 0xcc] rfl (by decide) (by decide),
    ⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide, ?_⟩⟩
  have h : ∀ j : Fin 30, combinedImage.code[48+j.val]'(by change 48+j.val < 158; omega) =
      quicDecode.code[j.val]'j.isLt := by decide
  intro j hj
  exact h ⟨j, hj⟩

theorem unsigned_encoder_invocation :
    Invocation unsignedEncode combinedImage 524600 (embeddedUnsignedEncoder.getReg .x1) 78
      embeddedUnsignedEncoder.memory := by
  refine ⟨combined_valid _ #[0xa5, 0xa5, 0xcc] rfl (by decide) (by decide),
    ⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide, ?_⟩⟩
  have h : ∀ j : Fin 35, combinedImage.code[78+j.val]'(by change 78+j.val < 158; omega) =
      unsignedEncode.code[j.val]'j.isLt := by decide
  intro j hj
  exact h ⟨j, hj⟩

theorem unsigned_decoder_invocation :
    Invocation unsignedDecode combinedImage 524740 (embeddedUnsignedDecoder.getReg .x1) 113
      embeddedUnsignedDecoder.memory := by
  refine ⟨combined_valid _ #[0x80, 0, 0xcc] rfl (by decide) (by decide),
    ⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide, ?_⟩⟩
  have h : ∀ j : Fin 44, combinedImage.code[113+j.val]'(by change 113+j.val < 158; omega) =
      unsignedDecode.code[j.val]'j.isLt := by decide
  intro j hj
  exact h ⟨j, hj⟩

theorem embedded_quic_encode : ∃ done,
    Returns combinedImage (relocated quicEncode 524292) 524288 128 embeddedQuicEncoder done ∧
    EncodePost (.ok [0x40, 0x40]) 2 65536 #[0xa5, 0xa5, 0xcc] [] done.state ∧
    WriteTrace combinedImage 524288 65536 65538 done.steps embeddedQuicEncoder done.state := by
  exact quic_encode_embedded combinedImage 524292 1 embeddedQuicEncoder 65536
    #[0xa5, 0xa5, 0xcc] [] quic_encoder_invocation rfl rfl rfl (by decide) (by decide)

theorem embedded_quic_decode : ∃ done,
    Returns combinedImage (relocated quicDecode 524480) 524288 64 embeddedQuicDecoder done ∧
    DecodePost (.ok ⟨0, 2⟩) done.state ∧ done.state.memory = embeddedQuicDecoder.memory := by
  exact quic_decode_embedded combinedImage 524480 48 [0x40, 0] [0xcc] 65536 true []
    embeddedQuicDecoder quic_decoder_invocation rfl (by decide) (by decide) rfl rfl rfl

theorem embedded_unsigned_encode : ∃ done,
    Returns combinedImage (relocated unsignedEncode 524600) 524288 160 embeddedUnsignedEncoder done ∧
    EncodePost (.ok [0x80, 1]) 2 65536 #[0xa5, 0xa5, 0xcc] [] done.state ∧
    WriteTrace combinedImage 524288 65536 65538 done.steps embeddedUnsignedEncoder done.state := by
  exact unsigned_encode_embedded combinedImage 524600 78 embeddedUnsignedEncoder 65536
    #[0xa5, 0xa5, 0xcc] [] unsigned_encoder_invocation rfl rfl rfl (by decide) (by decide)

theorem embedded_unsigned_decode : ∃ done,
    Returns combinedImage (relocated unsignedDecode 524740) 524288 128 embeddedUnsignedDecoder done ∧
    DecodePost (.error .nonMinimal) done.state ∧ done.state.memory = embeddedUnsignedDecoder.memory := by
  exact unsigned_decode_embedded combinedImage 524740 113 [0x80, 0] [0xcc] 65536 true []
    embeddedUnsignedDecoder unsigned_decoder_invocation rfl (by decide) (by decide) rfl rfl rfl

/-- An image may start at zero and return to the largest aligned 64-bit address. -/
def zeroBaseEntry : State :=
  (relocatedEntry 0 64 65536 2 #[0xa5, 0xa5, 0xcc]).setReg .x1 18446744073709551612

theorem zero_base_invocation :
    Invocation quicEncode (relocated quicEncode 0) 0 (zeroBaseEntry.getReg .x1) 0 zeroBaseEntry.memory := by
  refine ⟨⟨by cbv, by decide, by decide, by decide, ?_⟩,
    ⟨by decide, by decide, by decide, by decide⟩, CodeSlice.refl _⟩
  intro r hr hw
  have hr' : r = ⟨65536, #[0xa5, 0xa5, 0xcc], true⟩ := by
    simpa [zeroBaseEntry, relocatedEntry, heap] using hr
  subst r
  decide

theorem zero_base_encode : ∃ done,
    Returns (relocated quicEncode 0) (relocated quicEncode 0) 18446744073709551612 128 zeroBaseEntry done ∧
    EncodePost (.ok [0x40, 0x40]) 2 65536 #[0xa5, 0xa5, 0xcc] [] done.state ∧
    WriteTrace (relocated quicEncode 0) 18446744073709551612 65536 65538 done.steps zeroBaseEntry done.state := by
  exact quic_encode_embedded (relocated quicEncode 0) 0 0 zeroBaseEntry 65536
    #[0xa5, 0xa5, 0xcc] [] zero_base_invocation rfl rfl rfl (by decide) (by decide)

/-- The image's exclusive end may equal 2^64; its last instruction still cannot wrap. -/
def topBaseEntry : State :=
  (relocatedEntry 18446744073709551496 65536 2 91 #[0x40, 0, 0xcc]).setReg .x1 0

theorem top_base_invocation :
    Invocation quicDecode (relocated quicDecode 18446744073709551496)
      18446744073709551496 (topBaseEntry.getReg .x1) 0 topBaseEntry.memory := by
  refine ⟨⟨by cbv, by decide, by decide, by decide, ?_⟩,
    ⟨by decide, by decide, by decide, by decide⟩, CodeSlice.refl _⟩
  intro r hr hw
  have hr' : r = ⟨65536, #[0x40, 0, 0xcc], true⟩ := by
    simpa [topBaseEntry, relocatedEntry, heap] using hr
  subst r
  decide

theorem top_base_decode : ∃ done,
    Returns (relocated quicDecode 18446744073709551496) (relocated quicDecode 18446744073709551496)
      0 64 topBaseEntry done ∧ DecodePost (.ok ⟨0, 2⟩) done.state ∧
      done.state.memory = topBaseEntry.memory := by
  exact quic_decode_embedded (relocated quicDecode 18446744073709551496)
    18446744073709551496 0 [0x40, 0] [0xcc] 65536 true []
    topBaseEntry top_base_invocation rfl (by decide) (by decide) rfl rfl rfl

end Libp2pAsm.Tests.AsmCodecProof
