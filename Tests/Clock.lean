import Libp2pAsm.Spec.Clock

namespace Libp2pAsm.Tests.Clock

open Spec.Clock

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}")

def run : IO Unit := do
  let first : Sample := { beforeNs := 100, afterNs := 200, seconds := 1794000000, nanos := 0 }
  let (status, trusted) := update {} first 250000000 1000000
  check "should anchor a valid first wall-clock sample" (status == .trusted && trusted.mode == 1)
  let next := { first with beforeNs := 1000000100, afterNs := 1000000200, seconds := first.seconds + 1 }
  check "should accept coherent elapsed wall and monotonic time"
    ((update trusted next 250000000 1000000).1 == .trusted)
  let (jumpStatus, suspended) := update trusted { next with seconds := first.seconds + 20 } 250000000 1000000
  check "should stop authentication when wall time jumps" (jumpStatus == .wallUnavailable && suspended.mode == 4)
  let (down, _) := update trusted { next with seconds := first.seconds - 1 } 250000000 1000000
  check "should reject even a small wall-clock rollback" (down == .wallUnavailable)
  let (_, unavailable) := update trusted { next with sourceStatus := 1 } 250000000 1000000
  let recovery := { next with
    beforeNs := next.beforeNs + 1000000000
    afterNs := next.afterNs + 1000000000
    seconds := next.seconds + 1 }
  let (candidateStatus, candidate) := update unavailable recovery 250000000 1000000
  check "should require a candidate before restoring authentication"
    (candidateStatus == .wallUnavailable && candidate.mode == 4)
  let later := { recovery with
    beforeNs := recovery.beforeNs + 1000000000
    afterNs := recovery.afterNs + 1000000000
    seconds := recovery.seconds + 1 }
  check "should restore trust after a coherent recovery pair" ((update candidate later 250000000 1000000).1 == .trusted)
  let (_, stopped) := update trusted { next with beforeNs := 0 } 250000000 1000000
  check "should stop permanently after monotonic regression"
    (stopped.mode == 3 && (update stopped later 250000000 1000000).1 == .monotonicFailure)
  check "should reject unbounded wall-clock drift" ((update trusted next (2^64) 1).1 == .invalidLimits)
  check "should reject noncanonical nanoseconds" ((update trusted { next with nanos := 1000000000 } 250000000 1000000).1 == .wallUnavailable)
  IO.println "PASS: should suspend and recover wall-clock trust without wrapping elapsed time"

end Libp2pAsm.Tests.Clock
