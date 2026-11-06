import Libp2pAsm.Refinement.Clock.Prefix
import Libp2pAsm.Rv64.Logic.WordHeap

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic

structure RawSample where
  status : Word
  beforeNs : Word
  afterNs : Word
  seconds : Word
  nanos : Word
  deriving Repr

def RawSample.toSpec (s : RawSample) : Spec.Clock.Sample :=
  ⟨s.status.toNat, s.beforeNs.toNat, s.afterNs.toNat, s.seconds.toInt, s.nanos.toNat⟩

def SampleAt (m : Memory) (ptr : Word) (s : RawSample) : Prop :=
  ptr.toNat+40 ≤ 2^64 ∧ WordAt m ptr s.status ∧ WordAt m (ptr+8) s.beforeNs ∧
    WordAt m (ptr+16) s.afterNs ∧ WordAt m (ptr+24) s.seconds ∧ WordAt m (ptr+32) s.nanos

def StateBytes (bytes : Array UInt8) (s : RawState) : Prop :=
  readLE64 bytes 0 = s.mode ∧ readLE64 bytes 8 = s.afterNs ∧
    readLE64 bytes 16 = s.seconds ∧ readLE64 bytes 24 = s.nanos

theorem stateBytes_owned (base : Word) (bytes : Array UInt8) (frame : List Region) (s : RawState)
    (hv : (heap base bytes true frame).valid = true) (ha : base.toNat%8 = 0)
    (hb : 32 ≤ bytes.size) (hs : StateBytes bytes s) : StateAt (heap base bytes true frame) base s := by
  obtain ⟨hm, ht, hs, hn⟩ := hs
  refine ⟨by have := heap_bounded hv; omega, ?_, ?_, ?_, ?_⟩
  · simpa [hm] using heap_wordAt base bytes true frame hv ha 0 (by decide) (by omega)
  · simpa [ht] using heap_wordAt base bytes true frame hv ha 8 (by decide) (by omega)
  · simpa [hs] using heap_wordAt base bytes true frame hv ha 16 (by decide) (by omega)
  · simpa [hn] using heap_wordAt base bytes true frame hv ha 24 (by decide) (by omega)

theorem store_at (base value : Word) (before after : Array UInt8) (frame : List Region)
    (hv : (heap base before true frame).valid = true) (ha : base.toNat%8 = 0)
    (hs : after.size = before.size) (offset : Nat) (ho : offset%8 = 0) (hb : offset+8 ≤ before.size) :
    (heap base after true frame).store 8 (base+BitVec.ofNat 64 offset) value =
      .ok (heap base (writeLE64 after offset value) true frame) := by
  apply heap_store_word_offset base value after frame _ ha offset ho (by omega)
  rw [heap_valid_congr base after before true frame hs]
  exact hv

theorem store_bounds (base : Word) (bytes : Array UInt8) (frame : List Region)
    (hv : (heap base bytes true frame).valid = true) (hb : 32 ≤ bytes.size)
    (offset : Nat) (ho : offset+8 ≤ 32) :
    base.toNat ≤ (base+BitVec.ofNat 64 offset).toNat ∧
      (base+BitVec.ofNat 64 offset).toNat+8 ≤ base.toNat+32 := by
  rw [word_offset_toNat hv offset (by omega)]
  omega

def stopBytes (bytes : Array UInt8) : Array UInt8 :=
  writeLE64 (writeLE64 (writeLE64 bytes 0 3) 16 0) 24 0

def sampleBytes (bytes : Array UInt8) (mode : Word) (sample : RawSample) : Array UInt8 :=
  writeLE64 (writeLE64 (writeLE64 (writeLE64 bytes 0 mode) 8 sample.afterNs) 16 sample.seconds) 24 sample.nanos

def unavailableBytes (bytes : Array UInt8) (sample : RawSample) : Array UInt8 :=
  sampleBytes bytes 2 { sample with seconds := 0, nanos := 0 }

@[simp] theorem stopBytes_size (bytes : Array UInt8) : (stopBytes bytes).size = bytes.size := by
  simp [stopBytes]

@[simp] theorem sampleBytes_size (bytes : Array UInt8) (mode : Word) (sample : RawSample) :
    (sampleBytes bytes mode sample).size = bytes.size := by simp [sampleBytes]

@[simp] theorem unavailableBytes_size (bytes : Array UInt8) (sample : RawSample) :
    (unavailableBytes bytes sample).size = bytes.size := by simp [unavailableBytes]

end Libp2pAsm.Refinement.Clock
