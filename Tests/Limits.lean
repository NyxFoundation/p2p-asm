import Libp2pAsm.Spec.Limits

namespace Libp2pAsm.Tests.Limits

open Spec

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}")

def run : IO Unit := do
  let defaults : Limits := {}
  check "should accept finite internally consistent default limits" defaults.validate.isOk
  check "should fit declared reservations inside the arena"
    (defaults.reservedBytes == 22560768 && defaults.reservedBytes ≤ defaults.arenaBytes)
  let bad := [
    { defaults with maxConnections := 0 },
    { defaults with maxConnections := 2^64 },
    { defaults with maxConnectionsPerSource := 17 },
    { defaults with maxHandshakes := 17 },
    { defaults with maxDatagramBytes := 1199 },
    { defaults with maxRxBatch := 1025 },
    { defaults with maxRxBytes := 2047 },
    { defaults with completionSlots := 623 },
    { defaults with maxInputEvents := 640 },
    { defaults with maxTimers := 1 },
    { defaults with maxCertificateBytes := 65537 },
    { defaults with maxWallClockDriftNs := 0 },
    { defaults with maxClockSampleSpanNs := 250000001 },
    { defaults with maxInstructionsPerQuantum := 2^30 + 1 },
    { defaults with maxStackBytes := 15 },
    { defaults with arenaBytes := defaults.reservedBytes - 1 }]
  for limits in bad do
    check "should reject omitted, overflowing or inconsistent resource limits" (!limits.validate.isOk)
  IO.println "PASS: should validate finite limits, completion reservations and arena accounting"

end Libp2pAsm.Tests.Limits
