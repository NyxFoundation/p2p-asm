# QUIC recovery leaves

Independent executable natural-number Specs live in `Libp2pAsm/Spec/Quic/Recovery`.
Independent typed RV64IM implementations live in `Libp2pAsm/Asm/Quic/Recovery`.
`Asm.Quic.Recovery.program name` returns a checked `SAsm.Stmt`; lower and emit it
using the existing RV64 encoder. It contains ordinary RV64IM instructions only.
There is no runtime Spec interpreter, host protocol implementation, cryptographic
callback, new opcode, or external allocation.

## Entry contract and ownership

Call a named leaf with `a0` pointing to the descriptor below. Return `a0` is status;
all other caller temporaries are zero. `ra/sp/gp/tp` and all callee-saved registers
are preserved. Stack use is **zero**, so no stack wipe is necessary. Validated work
is wiped exactly, including its staged action; work capacity beyond that extent is
untouched. Invalid memory descriptors cause no writes, including no work wipe.

Every word is **unsigned LE64, aligned to 8 bytes**. The descriptor is 64 bytes:

| Byte offset | Field |
|---|---|
| 0, 8 | context address, exact context byte size |
| 16, 24 | event address, event byte length (at least 128) |
| 32, 40 | action address, capacity (at least 64) |
| 48, 56 | work address, capacity (at least context bytes + 64) |

The descriptor, context, event, action's first 64 bytes, and full declared work
capacity must be mutually disjoint, mapped with appropriate permissions, and
disjoint from executable code. The leaf checks alignment, all nonwrapping spans,
and these pairwise aliases before copying. Mapping, code permission/separation,
exclusive ownership and immutable inputs are caller obligations. Empty/dangling
host pointers are not authenticated network inputs. `sp` must be 16-byte aligned.
Frame/buffer handles are integers, never dereferenced host addresses. Byte payloads
may be unaligned; the recovery API consumes only aligned metadata words.

One owner serializes each connection. The leaf copies its context into work,
executes the transition there, and commits context and action only on success.
This is atomic at the call boundary under the ownership/mapping contract, not a
hardware transaction against a concurrently mutating host. On semantic failure,
context and action are unchanged. No partial ACK or capacity failure commits a
partially calculated *quantum*. Valid batch continuations can commit individually.

## Layout

Let `N=history`, `P=paths`, `R=ranges`, all caller configured. Context length is
`8 * (64 + 32*P + 20*N + 2*R)` bytes. Word indices below are relative to the context.
The header has 64 words; packet-space entries are embedded in it.

| Words | Meaning, in order |
|---|---|
| 0–2 | magic `0x5245434f5631`, connection generation, connection slot |
| 3–11 | N, P, R, maxPending, maxLive, maxSendAttempts, maxSendWaitNs, maxDatagramBytes, quantum instruction limit |
| 12–16 | allocated history count, next attempt ID, pending count, live count, last event time |
| 17–22 | server, handshake complete, handshake confirmed, peer completed address validation, active path index, PTO count |
| 23–30 | batch phase, space, frozen time, raw ACK delay, range count, ledger cursor, any newly ACKed, largest ACK in batch |
| 31 | installed-key bitmap: bit 0 Initial, bit 1 Handshake, bit 2 Application |
| 32–55 | three 8-word PN-space records (Initial, Handshake, Application) |
| 56–60 | RTT sample **record index**, sample newly ACKed, any newly ACKed eliciting packet, range cursor, evidence count for range |
| 61–63 | peer ACK delay exponent, peer max ACK delay **nanoseconds**, retirement reason (0 active) |

Each PN-space record is: next PN, discarded flag, largest ACK + 1, last eliciting
OS send time, outstanding eliciting count, pending record index + 1, largest
actually sent PN + 1, loss deadline. Zero in the two `+1` fields means absent.
Zero send timestamps are legal; counts distinguish them from absent history.
PN can reach `2^62` only as the exhausted **next** counter. No packet uses it.

Path `i` starts at word `64 + 32*i`:

| Relative words | Meaning |
|---|---|
| 0–7 | used, path generation, address validated, attributable received bytes, actual transmitted bytes, reserved bytes, bytes in flight, reserved flight bytes |
| 8–11 | cwnd, ssthresh, recovery start time, recovery-start-present flag |
| 12–17 | latest RTT, minimum RTT, smoothed RTT, RTT variance, sample count, first sample time |
| 18–24 | pacing deadline, latest OS send time, challenge token, challenge expiry, challenge live, failed, path MTU |
| 25–27 | anti-deadlock PTO anchor, two reserved zero words |
| 28–31 | end time of last applied persistent-congestion interval, remaining probe credits, probe PN-space + 1, reserved zero |

Packet record `i` starts at word `64 + 32*P + 20*i`:

| Relative words | Meaning |
|---|---|
| 0–6 | status, space, path index, PN, UDP payload bytes, in-flight flag, ACK-eliciting flag |
| 7–10 | immutable frame-batch handle/generation, immutable datagram-buffer handle/generation |
| 11–17 | attempt ID, attempts consumed, original first submission time, original deadline, OS send time, actually-sent evidence flag, latest attempt submission time |
| 18–19 | application-limited-at-send flag supplied by core, PTO probe flag |

Statuses: 1 pending, 2 would-block, 3 actually sent, 4 acknowledged, 5 lost,
6 abandoned unsent, 7 unresolved/quarantined, 8 discarded with keys. Status 0 is
only an unused history slot. Immutable identity/frame/buffer fields never change.
The evidence bit persists through ACK, loss and discard. Records are append-only
for this connection generation; they are never recycled or inferred from a high PN.
ACK ranges start at word `64 + 32*P + 20*N`, each `(lo,hi)` inclusive. They must
descend with at least one unacknowledged number between ranges.

## Events and real entry points

Every event begins with words `[reserved=0, connectionGeneration, monotonicNow]`.
Unused words through word 15 are ignored. Parameters below start at word 3.
Except `init`, every leaf checks the connection generation. `resume` uses its
owned snapshot time and ranges; the event time is not substituted into a batch.

| Name | Parameters starting at event word 3 |
|---|---|
| `init` | slot, server, N, P, R, maxPending, maxLive, maxAttempts, waitNs, datagramBytes, quantum, exponent, maxAckDelayNs |
| `keys` | PN space (install keys; cannot resurrect discarded keys) |
| `reserve` | space, path, bytes, flags, frame handle, frame generation, buffer handle, buffer generation |
| `result` | record index, attempt ID, outcome, OS submission timestamp |
| `retry` / `expire` | record index |
| `receive` | path, attributable received UDP payload bytes |
| `validate` | path, path generation |
| `challenge` | path, caller entropy token, absolute expiry |
| `response` | path, path generation, exact echoed token |
| `handshake` | complete, confirmed, peer completed address validation (monotone flags) |
| `ack` | space, raw wire ACK delay, range count; pairs begin at **byte 128** |
| `resume` | no additional parameters |
| `timer` | no additional parameters |
| `pto` | previously returned absolute deadline, space |
| `discard` / `loss` | space |
| `newpath` / `activate` | path index, path generation |
| `persistent` | first and last lost record indices |

`init` requires an uninitialized context (magic word zero). Other context bytes
are overwritten. Initially only Initial keys are installed. `reserve` flags are
bit 0=in-flight, bit 1=eliciting, bit 2=probe, bit 3=application-limited. Padding
counts in flight; ACK/CONNECTION_CLOSE-only packets do not. Core must classify
frames, enforce encryption levels, verify AEAD, and validate transport parameters.
No recovery state asserts that network authentication or TLS identity was checked.

Outgoing datagrams contain **one QUIC packet** in this leaf API. The core can use
this legal sending profile; coalesced receive parsing is a separate Wire/core
responsibility. At most one send is pending per PN space, enforcing PN send order
while one datagram is blocked. Other PN spaces can progress independently and
completion delivery can reorder. A successful OS timestamp can predate another
space's previously delivered result. Address and RTT/CC state remain per path.

Result outcomes: 0 success, 1 would-block, 2 message-too-large, 3 irreversible
failure. Only matched outcome 0 establishes sent evidence and flight bytes.
Outcome 1 retains identical PN, datagram, reservation, original deadline and
attempt limit. `retry` is callable on a **host writability notification only** and
issues a fresh token. Failure/would-block must never later transmit that trial.
Attempt IDs start at 1; `2^64-1` is the exhausted next-ID sentinel, never wrapped.

`expire` is independently schedulable even during an ACK/loss batch. A known
blocked packet releases its reservation and fails that path. An unresolved trial
retains its reservation, retires the connection and emits quarantine/cancel.
Preemption of an active batch also retires the connection; it never resumes the
abandoned snapshot. The host must quiesce the loan before reclaiming its buffer.
Expiry is due at the original deadline, or after the last allowed *would-block*
result; the final still-pending trial is not prematurely treated as exhausted.

## Status, actions and lifecycle

Status 0 succeeds; 2 malformed input; 3 arithmetic/counter exhaustion; 4 memory
layout/alignment; 5 local capacity; 6 stale/duplicate/mismatched completion;
7 admission/backpressure; 8 expired; 9 invalid host outcome/time; 10 raw state or
lifecycle; 11 batch busy; 12 ACK of never-actually-sent PN; 13 retired connection.
On status 3, or history exhaustion (5), core must retire the connection locally.
It must not retry allocation indefinitely or reset PN/attempt counters. An invalid
authenticated ACK maps to QUIC's appropriate protocol error in core; arbitrary
host API misuse is not automatically a peer protocol violation.

An action is eight LE64 words: kind, record/space index, PN, attempt/count, absolute
time, frame handle/path index, frame generation, buffer handle. For packet actions,
buffer generation and newly ACKed byte count are read from the immutable indexed
packet record. The frame handle denotes a caller-owned immutable, bounded frame
list, not payload bytes or stored ciphertext. Core retains its generation mapping
until all referencing history is retired, and deduplicates retransmitted STREAM/
CRYPTO frame delivery using those frame identities. The leaf never delivers bytes
to an application. A duplicate packet ACK does not emit another frame notification.

Kinds: 0 none, 1 send, 2 return completed buffer loan, 3 wait for writability,
4 repacketize after MTU reduction, 5 fail path, 6 cancel/quarantine unresolved I/O,
7 newly ACKed frames, 8 lost frames, 9 discard frames, 10 resume, 11 arm recovery
timer, 12 request probes. For 11, word 1 is space, word 3 is 1=loss/2=PTO, word 4
is deadline; word 5 is the PTO path. For 12, word 3 is the budget **2**, word 5 is
path. Probe credits are bound to that path and PN space and consumed by reserve.
PTO admission may exceed cwnd for those two packets, but never amplification limits.

After mutation, core queries `timer` to arm/cancel its generation-tagged timer.
Kind 0 cancels the recovery timer; pending-send deadlines remain independent.
The earliest nonzero loss deadline wins; discarded spaces contribute none. Probe
and loss actions request necessary CRYPTO/STREAM frames in **new PNs**, never old
ciphertext. The only identical ciphertext resubmission is a completed would-block
trial. Core's timer registry validates its own timer IDs/generations and reserves
completion/action capacity before issuing host operations.

For every `result` that returns stale/expired/retired or a fatal status, core must
consult its buffer registry by `(connection slot, generation, attempt ID)`. Reclaim
only that registry's outstanding loan after host completion/cancellation; do not
free the buffer named by a stale index or free an already returned loan. Logical
state and output stay unchanged on these errors. This obligation also applies to
results for a connection whose entire recovery arena has already been retired.

Generation advancement is performed by core's owning slot registry. Reuse requires
all loans quiesced, a new zeroed context, and a strictly greater nonzero generation.
An exhausted 64-bit generation slot is permanently retired. Recovery never reuses
a path slot within a connection: `newpath` requires unused storage. Validation
sets only address-validation metadata; `activate` requires validation. It does
not authenticate a peer or implement a migration FSM.

## RFC decisions, arithmetic and batches

RTT uses nanoseconds, initial 333 ms, 1 ms granularity, sample count (not zero time)
as the first-sample sentinel. Wire delay is microseconds times `2^exponent`; use a
wide calculation/clamp to max_ack_delay after confirmation in Application only.
This implementation ignores peer ACK delay before confirmation, permitted by
RFC9002 §5.3. Variance uses the **old** smoothed value (verified erratum 7539).
EWMA divides once with floor rounding: `(3*v+abs(old-rtt))/4`, `(7*old+rtt)/8`.
RV64 quotient/remainder decomposition avoids intermediate overflow. Time loss is
`max(1ms,ceil(9*max(latest,smoothed)/8))`; packet loss threshold is 3.

PTO is checked `srtt+max(4*var,1ms)` plus max_ack_delay only for confirmed
Application, then multiplied by `2^count`. Application PTO is suppressed before
confirmation. Client anti-deadlock probes choose installed Handshake keys, else
Initial. Queries retain an explicit anti-deadlock anchor so polling or received traffic
cannot extend a deadline. The anchor advances on new ACKs, PTO firing and key discard. Servers require amplification room for a 1200-byte probe. Timers select
the last eliciting send's path in each space. New ACKs reset backoff only once the
peer has validated the address (always true for a server); duplicates do not.

NewReno starts at `min(10*M,max(2*M,14720))`, minimum `2*M`. Loss is processed
before ACK window growth, once per recovery epoch. Avoidance growth floors
`M*ackedBytes/cwnd`; a 128-bit MUL/MULHU and fixed 64-step division implements the
product exactly. Pacing uses `ceil(bytes*srtt/cwnd)` with no accumulated idle
credit, and preserves cwnd over idle periods. The core supplies the application-
limited flag from its actual send demand, preventing growth while underutilized.

`persistent(first,last)` validates both lost eliciting endpoints, a prior RTT
sample, duration strictly above `3*(srtt+max(4*var,1ms)+max_ack_delay)`, and every
sent packet in the interval across **all spaces**. Acknowledged or still-outstanding
packets prevent collapse. A successful collapse sets cwnd to `2*M` and refreshes
minimum RTT. Core checks candidate lost endpoints after loss processing, using
bounded history; this leaf does not claim to schedule a migration/recovery FSM.
Repeated certificates are rejected; later reordered ACKs cannot double-decrement.

ACK begin copies validated descending ranges into owned storage. Phase 1 walks
each range against the entire immutable sent ledger, counting exact evidence;
there is **no loop over numeric range width**. Unsent, failed, reserved and abandoned
gaps are rejected even below largest sent. Only after complete range validation
does recovery change. Phase 3 detects loss; phase 2 applies ACKs one ledger slot
per quantum. Phase 4 discards one slot per quantum. Other mutations return busy;
independent send expiry can preempt and retire. No borrowed external ACK snapshot
survives begin. Caller must consume each one-action output before reusing it.

ECN is disabled locally. Wire may parse ACK_ECN and pass its authenticated ranges;
no ECN counts are consumed and no ECN validation/support is claimed.

## Resource formulas and verification limits

Let `W = 64+32*P+20*N+2*R` words. Context is `8W`, work is `8W+64`, action is 64,
descriptor is 64, maximum event is `128+16R` bytes; total disjoint leaf storage is
`16W+320+16R`, excluding the caller's frame/data registry and executable code.
All capacities are explicit positive caller values. `maxPending <= maxLive <= N`.
Configured datagram size is 1200..65507, exponent <=20, max_ack_delay <16384 ms.

Conservative control-flow bound per call is `B=200000+100W+500*N*P` instructions.
Configuration rejects `B > quantum`; it never increases core's limit. The constant
covers checks and fixed 64-iteration arithmetic; copies/wipes are bounded by W,
record validation by N, path accounting by NP, space scans by 3N, range copying or
membership by R. A valid ACK requires at most `1+R*(N+1)+2*N+3` calls including begin;
loss/discard requires at most N+2. Inputs/owned ledger are frozen between those
parts. These are conservative code-structure estimates, **not machine-checked full
resource theorems**; finite measured counts are checked against B, not used as proof.

Mapping to main's actual Limits is explicit: N may use maxSentPackets (128), P uses
maxPathsPerConnection (2), R uses maxAckRanges (64), live <= maxSentPackets,
pending <= maxPendingSends, attempts/wait/datagram/quantum use their namesakes.
With N=128, P=2, R=64: W=2816; total leaf storage=46400 bytes; B=609600, below
16777216. This policy retains **128 lifetime allocated PNs**, including failures;
it retires locally when full, even if all packets were ACKed. It is an explicit
finite-history policy, not an outstanding-only eviction scheme. N=4096 instead
requires 1,316,160 bytes for these leaf arenas and B=12,513,600; main's 65536-byte
connectionMetadataBytes cannot hold that policy. Core must budget it explicitly.
CPU limits across quanta and scheduler fairness remain core obligations.

Run:

```sh
python3 Tests/Recovery/check.py --qemu /path/to/qemu-riscv64
python3 Tests/Recovery/audit.py
```

The default QEMU lookup is PATH (or `QEMU_RISCV64`). The suite compares independent
Python RFC calculations, pure Specs and actual lowered instruction execution,
complete before/after register/memory/guard/wipe snapshots, and every load/store
footprint. GNU bytes must equal direct encoder bytes. Both ELF variants run under
QEMU against the same complete snapshot. Tests cover old/duplicate/reordered ACKs,
pending-before-success rejection, MTU/new PN, would-block/tokens/deadlines, expiry
during a batch, stale generations, overflow, spaces/keys, RTT, PTO, NewReno,
persistent congestion, path isolation, wide amplification and ABI failures.

`audit.py` automatically enumerates every recovery theorem, kernel checks imports
and audits transitive axioms (only Lean's standard propext/choice/quotient axioms).
Proved results include amplification accounting, rejection of pending ACK evidence,
unknown-expiry reservation retention, duplicate-ACK accounting, overflow/carry
arithmetic, exact EWMA decomposition, and actual ADD/SLTU fragment execution and
its membership in emitted amplification code. There is **no claim of full FSM
refinement, whole-leaf memory/resource proof, universal CT, or complete QUIC/core
integration from these lemmas or finite traces**. Recovery metadata is public;
no secret payload is read or logged.

## Sources checked

- [RFC9002](https://www.rfc-editor.org/rfc/rfc9002.html), §§5–7 and appendices.
- [Verified erratum 7539](https://www.rfc-editor.org/rfc/inline-errata/rfc9002.html): variance update order.
- [Reported erratum 9169](https://mailarchive.ietf.org/arch/msg/quic/TGngerJ2xCfHwhTV70YaLAEH1gc/): zero deadline excluded from minimum; not described as verified.
- [RFC9000](https://www.rfc-editor.org/rfc/rfc9000.html), §§8,12.3,13,19.3.
- [Verified erratum 8240](https://www.rfc-editor.org/errata/eid8240): CONNECTION_CLOSE-only packets do not count in flight.
- [RFC9000 errata](https://www.rfc-editor.org/errata/rfc9000): reported 8875's challenge-flood issue is bounded here by path slots; response scheduling/rate admission belongs to core.

Checked 2026-11-06/07. Errata endpoints redirected unreliably; verified inline
rendering and IETF report archives were also consulted.
