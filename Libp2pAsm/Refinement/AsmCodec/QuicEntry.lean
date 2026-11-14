import Libp2pAsm.Refinement.AsmCodec.QuicCorrect

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

/-- Full fetch/runUntil correspondence from a concrete owned byte layout.
`padding` and `frame` are arbitrary, and may include guard bytes and unrelated regions. -/
theorem quic_decode_runUntil (bytes padding : List UInt8) (base : Word)
    (w : Bool) (frame : List Region) (s : State)
    (hm : s.memory = heap base (bytes ++ padding).toArray w frame)
    (hb : base.toNat + (bytes ++ padding).length ≤ 2^64)
    (hl : bytes.length < 2^64) (hp : s.pc = 65536)
    (hptr : s.getReg .x10 = base) (hlen : s.getReg .x11 = BitVec.ofNat 64 bytes.length)
    (hra : s.getReg .x1 = 0) (hv : quicDecode.valid s.memory = true) :
    ∃ done, runUntil quicDecode 0 64 s = .ok done ∧ done.steps ≤ 64 ∧
      done.state.pc = 0 ∧ DecodePost (Spec.Codec.QuicVarint.decode bytes) done.state ∧
      done.state.memory = s.memory ∧ PreservesCallee s done.state := by
  have hmem : s.memory.valid = true := by
    simp only [LeanAsm.Rv64.Image.valid, Bool.and_eq_true] at hv
    exact hv.1.1
  have hread : Reads s.memory (s.getReg .x10) bytes := by
    rw [hm, hptr]
    have hr := (heap_reads base (bytes ++ padding) w frame (by simpa [hm] using hmem) hb).take bytes.length
    simpa using hr
  obtain ⟨n, t, hn, ht, htpc, hout⟩ := quic_decode_trace bytes s hl hlen hra hread
  have he := trace_at_pc hp ht
  exact ⟨⟨t, n⟩, he.runUntil htpc hv 64 hn, hn, htpc, hout,
    decoders_memory_frame (.inl rfl) he, codecs_callee_saved (.inr (.inl rfl)) he⟩

/-- A concrete satisfiable entry layout; this check does not stand in for universal correctness. -/
def quicExample : State :=
  let s : State := { pc := 65536, memory := heap 131072 #[0x40, 0] false [] }
  (s.setReg .x10 131072).setReg .x11 2

theorem quicExample_valid : quicDecode.valid quicExample.memory = true := by
  cbv

theorem quicExample_result : ∃ done, runUntil quicDecode 0 64 quicExample = .ok done ∧
    done.steps ≤ 64 ∧ done.state.pc = 0 ∧ Output 0 0 2 done.state ∧
    done.state.memory = quicExample.memory ∧ PreservesCallee quicExample done.state := by
  exact quic_decode_runUntil [0x40, 0] [] 131072 false [] quicExample
    rfl (by decide) (by decide) rfl (by rfl) (by rfl) (by rfl) quicExample_valid

end Libp2pAsm.Refinement.AsmCodec
