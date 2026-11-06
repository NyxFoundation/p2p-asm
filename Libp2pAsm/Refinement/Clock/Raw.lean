import Libp2pAsm.Refinement.Clock.MemoryPost
import Libp2pAsm.Refinement.Clock.ElapsedArithmetic
import Libp2pAsm.Refinement.Clock.DriftArithmetic
import Libp2pAsm.Refinement.Clock.StateSpec

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def validRaw (old : RawState) : Prop :=
  old.mode ≤ 4 ∧ ((old.mode = 1 ∨ old.mode = 4) → old.nanos < 1000000000)

instance (old : RawState) : Decidable (validRaw old) := inferInstanceAs (Decidable (_ ∧ _))

def monotonicBad (old : RawState) (sample : RawSample) : Prop :=
  ¬sample.status < 2 ∨ ¬sample.beforeNs ≤ sample.afterNs ∨
    (old.mode ≠ 0 ∧ ¬old.afterNs ≤ sample.beforeNs)

instance (old : RawState) (sample : RawSample) : Decidable (monotonicBad old sample) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def wallBad (sample : RawSample) (span : Word) : Prop :=
  sample.status ≠ 0 ∨ ¬sample.afterNs-sample.beforeNs ≤ span ∨ ¬sample.nanos < 1000000000

instance (sample : RawSample) (span : Word) : Decidable (wallBad sample span) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def wallBackwards (old : RawState) (sample : RawSample) : Prop :=
  sample.seconds.toInt < old.seconds.toInt ∨ (sample.seconds = old.seconds ∧ ¬old.nanos ≤ sample.nanos)

instance (old : RawState) (sample : RawSample) : Decidable (wallBackwards old sample) :=
  inferInstanceAs (Decidable (_ ∨ _))

def coherent (old : RawState) (sample : RawSample) (drift : Word) : Prop :=
  ¬wallBackwards old sample ∧
    withinDrift (elapsedHigh (secondsPart old sample) (nanosPart old sample))
      (elapsedLow (secondsPart old sample) (nanosPart old sample)) (sample.afterNs-old.afterNs) drift

instance (old : RawState) (sample : RawSample) (drift : Word) : Decidable (coherent old sample drift) :=
  inferInstanceAs (Decidable (_ ∧ _))

def rawUpdate (old : RawState) (sample : RawSample) (drift span : Word) : Spec.Clock.Status × RawState :=
  if drift = 0 ∨ span = 0 ∨ drift < span then (.invalidLimits, old)
  else if ¬validRaw old then (.invalidState, old)
  else if old.mode = 3 then (.monotonicFailure, old)
  else if monotonicBad old sample then (.monotonicFailure, ⟨3, old.afterNs, 0, 0⟩)
  else if wallBad sample span then (.wallUnavailable, ⟨2, sample.afterNs, 0, 0⟩)
  else if old.mode = 2 then (.wallUnavailable, anchor sample 4)
  else if old.mode = 0 ∨ coherent old sample drift then (.trusted, anchor sample 1)
  else (.wallUnavailable, anchor sample 4)

def rawBytes (old : RawState) (sample : RawSample) (drift span : Word) (bytes : Array UInt8) : Array UInt8 :=
  if drift = 0 ∨ span = 0 ∨ drift < span then bytes
  else if ¬validRaw old then bytes
  else if old.mode = 3 then bytes
  else if monotonicBad old sample then stopBytes bytes
  else if wallBad sample span then unavailableBytes bytes sample
  else if old.mode = 2 then sampleBytes bytes 4 sample
  else if old.mode = 0 ∨ coherent old sample drift then writeLE64 (sampleBytes bytes 4 sample) 0 1
  else sampleBytes bytes 4 sample

theorem rawBytes_post (old : RawState) (sample : RawSample) (drift span : Word) (bytes : Array UInt8)
    (hb : 32 ≤ bytes.size) (hs : StateBytes bytes old) :
    StateBytes (rawBytes old sample drift span bytes) (rawUpdate old sample drift span).2 ∧
      ByteFrame 0 32 bytes (rawBytes old sample drift span bytes) := by
  unfold rawBytes rawUpdate
  by_cases hlim : drift = 0 ∨ span = 0 ∨ drift < span
  · simpa only [if_pos hlim] using And.intro hs (ByteFrame.refl 0 32 bytes)
  simp only [if_neg hlim]
  by_cases hv : ¬validRaw old
  · simpa only [if_pos hv] using And.intro hs (ByteFrame.refl 0 32 bytes)
  simp only [if_neg hv]
  by_cases hm3 : old.mode = 3
  · simpa only [if_pos hm3] using And.intro hs (ByteFrame.refl 0 32 bytes)
  simp only [if_neg hm3]
  by_cases hmono : monotonicBad old sample
  · simpa only [if_pos hmono] using And.intro (stopBytes_state bytes old hb hs) (stopBytes_frame bytes)
  simp only [if_neg hmono]
  by_cases hwall : wallBad sample span
  · simpa only [if_pos hwall, unavailableBytes] using And.intro (unavailableBytes_state bytes sample hb)
      (sampleBytes_frame bytes 2 { sample with seconds := 0, nanos := 0 })
  simp only [if_neg hwall]
  by_cases hm2 : old.mode = 2
  · simpa only [if_pos hm2] using And.intro (sampleBytes_state bytes 4 sample hb) (sampleBytes_frame bytes 4 sample)
  simp only [if_neg hm2]
  by_cases htrust : old.mode = 0 ∨ coherent old sample drift
  · simp only [if_pos htrust]
    exact ⟨stateBytes_mode _ (anchor sample 4) 1 (by simpa using hb)
      (sampleBytes_state bytes 4 sample hb), (sampleBytes_frame bytes 4 sample).write_word 1 (by decide) (by decide)⟩
  · simpa only [if_neg htrust] using And.intro (sampleBytes_state bytes 4 sample hb) (sampleBytes_frame bytes 4 sample)

end Libp2pAsm.Refinement.Clock
