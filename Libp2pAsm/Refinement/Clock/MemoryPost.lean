import Libp2pAsm.Refinement.Clock.Memory
import Libp2pAsm.Rv64.Logic.WordFrame

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic

def anchor (sample : RawSample) (mode : Word) : RawState :=
  ⟨mode, sample.afterNs, sample.seconds, sample.nanos⟩

theorem stopBytes_state (bytes : Array UInt8) (old : RawState) (hb : 32 ≤ bytes.size)
    (hs : StateBytes bytes old) : StateBytes (stopBytes bytes) ⟨3, old.afterNs, 0, 0⟩ := by
  have h8 : 8 ≤ bytes.size := by omega
  have h16 : 16 ≤ bytes.size := by omega
  have h24 : 24 ≤ bytes.size := by omega
  simp [StateBytes, stopBytes, readLE64_write_other, readLE64_writeLE64, h8, h16, h24, hb, hs.2.1]

theorem sampleBytes_state (bytes : Array UInt8) (mode : Word) (sample : RawSample) (hb : 32 ≤ bytes.size) :
    StateBytes (sampleBytes bytes mode sample) (anchor sample mode) := by
  have h8 : 8 ≤ bytes.size := by omega
  have h16 : 16 ≤ bytes.size := by omega
  have h24 : 24 ≤ bytes.size := by omega
  simp [StateBytes, sampleBytes, anchor, readLE64_write_other, readLE64_writeLE64, h8, h16, h24, hb]

theorem unavailableBytes_state (bytes : Array UInt8) (sample : RawSample) (hb : 32 ≤ bytes.size) :
    StateBytes (unavailableBytes bytes sample) ⟨2, sample.afterNs, 0, 0⟩ :=
  sampleBytes_state bytes 2 { sample with seconds := 0, nanos := 0 } hb

theorem stateBytes_mode (bytes : Array UInt8) (old : RawState) (mode : Word) (hb : 32 ≤ bytes.size)
    (hs : StateBytes bytes old) : StateBytes (writeLE64 bytes 0 mode) { old with mode } := by
  have h8 : 8 ≤ bytes.size := by omega
  have h16 : 16 ≤ bytes.size := by omega
  have h24 : 24 ≤ bytes.size := by omega
  simp [StateBytes, readLE64_write_other, readLE64_writeLE64, h8, h16, h24, hb,
    hs.2.1, hs.2.2.1, hs.2.2.2]

theorem stopBytes_frame (bytes : Array UInt8) : ByteFrame 0 32 bytes (stopBytes bytes) := by
  exact (((ByteFrame.refl 0 32 bytes).write_word 3 (by decide) (by decide)).write_word 0
    (by decide) (by decide)).write_word 0 (by decide) (by decide)

theorem sampleBytes_frame (bytes : Array UInt8) (mode : Word) (sample : RawSample) :
    ByteFrame 0 32 bytes (sampleBytes bytes mode sample) := by
  exact ((((ByteFrame.refl 0 32 bytes).write_word mode (by decide) (by decide)).write_word sample.afterNs
    (by decide) (by decide)).write_word sample.seconds (by decide) (by decide)).write_word sample.nanos
    (by decide) (by decide)

end Libp2pAsm.Refinement.Clock
