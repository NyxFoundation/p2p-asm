# Streams leaf integration contract

Status: receive, send, multistream and Ping standalone leaves implemented; new
files only. Root QUIC/TLS/recovery integration remains with main. Parent design §§5/6/8/9 and
`Spec/Limits` are authoritative. Runtime bodies are typed RV64IM SAsm, using
frozen Util/Link/Model; Spec and Python are independent test/reference semantics.

## Common ABI and ownership

Standard RV64 call/return, a0 status, a1..a4 documented outputs (all zero on
error); other caller temporaries are zeroed. ra/sp/gp/tp and s0..s11 preserved.
State and stack are 8-byte aligned (stack 16-byte aligned); byte views may be
unaligned. Exactly 128 stack bytes below entry sp are writable, exclusively owned,
restored/wiped on every post-entry return; early metadata rejection uses no stack.
Return target is 4-byte aligned executable RV64 code; code is immutable, mapped,
validly lowered/encoded and disjoint from writable memory. No ecall or oracle.

Caller validates registered region/handle/generation, actual mappings and R/W
permissions, exclusive state ownership and lifetime BEFORE invoking a leaf.
State, data, presence/ACK storage, input, stack, work and code are pairwise disjoint.
Read-only input aliases are permitted only between separately read-only views.
State pointer fields are trusted caller-owned addresses, never decoded packet
integers. Frame offsets/lengths/flags are untrusted. Raw capacity, alignment,
nonwrapping addresses, view bounds and scalar metadata are checked before the
corresponding access. Correct presence/ACK contents and logical state consistency
are caller-maintained invariants; corrupt arbitrary state is outside this contract.
Caller supplies finite Limits-derived capacities and instruction budget admission;
there is no smaller hidden byte cap in these leaves. No concurrent invocation or
external mutation during a call. On error persistent state/data are unchanged.

Statuses: 0 success, 1 invalid metadata/argument, 2 offset overflow,
3 flow violation, 4 final size, 5 conflicting overlap, 6 receive/send capacity,
7 CRYPTO_BUFFER_EXCEEDED, 8 unavailable/backpressure, 9 closed, 10 timeout,
11 authentication gate, 12 Ping mismatch, 13 negotiation format, 14 proposal limit.
The caller maps transport errors only after packet authentication: conflict is the
local authenticated PROTOCOL_VIOLATION policy; final/flow use the RFC errors.
No constant-time or whole-program refinement claim follows from finite tests.
Payload comparison accumulates XOR and releases only its final match/conflict.

## Receive: 80-byte LE64 state

| Offset | Value |
| --- | --- |
| 0 | capacity C, 1..2^62-1 |
| 8 | owned data base, C bytes |
| 16 | owned presence base, C bytes, each 0/1 |
| 24 | consumed absolute offset |
| 32 | highest received absolute end offset |
| 40 | final size, or UINT64_MAX for unknown |
| 48 | supplied stream credit limit, <=2^62-1 |
| 56 | supplied remaining aggregate connection allowance, <=2^62-1 |
| 64 | 0 STREAM, 1 CRYPTO |
| 72 | reset Boolean |

Initialize with zero consumed/highest/reset/data/presence and unknown final.
CRYPTO owns a separate state per encryption level; it ignores stream/connection
credit and rejects FIN/RESET. `C` is sliding storage, never an absolute offset cap.
Active position p is data[p%C], presence[p%C]; only [consumed,consumed+C) may
be present. Caller may monotonically increase the limit and refresh allowance.

`receive(a0=state,a1=stateCapacity,a2=registeredSourceBase,a3=sourceCapacity,
a4=sourceOffset,a5=length,a6=absoluteStreamOffset,a7=0 data/1 FIN/2 RESET)`.
RESET has zero input length and a6=final size. Returns a1 exact connection credit
delta and a4=input flag. Zero-length high-offset frames charge highest-offset
increase even without storage; final-size/credit checks still apply. Repeated
consistent FIN/RESET has zero additional credit. RESET wipes exactly both C-byte
regions; subsequent data is checked for final/flow errors then ignored.
No byte at or beyond final can be stored (empty FIN at final is allowed).

Overlaps in retained bytes are compared in a read-only pass before publishing.
Consumed bytes are retired, wiped and ignored on retransmission (RFC9000 §2.2);
detecting historical conflicts after retirement is impossible with bounded storage.
`consume(a0=state,a1=stateCapacity,a2=count)` first validates every consumed byte,
then wipes exactly that range and advances consumed. Gaps/suffixes remain intact.
`peek(a0=state,a1=stateCapacity)` returns a2=data-region-relative offset,
a3=contiguous length up to wrap, a4=1 EOF / 2 reset / 0 open. Borrow remains valid
until consume/reset; caller copies or consumes it before mutation. Reinvoke after
consuming at wrap. Outputs are uncommitted application actions until caller has
both authenticated peer identity and handshakeConfirmed. CRYPTO is TLS input,
not application delivery, and its gate is the caller's encryption-level FSM.

No aggregate connection mutation occurs here. Caller atomically commits returned
delta with state under single-event-loop ownership; do not apply a leaf before
all other packet-wide transactional preconditions are met.

Receive cost <=5000+200*(input length+C), consume <=5000+200*C, peek <=5000+200*C
RV64 instructions. Data scan consumes one input byte per iteration (two passes);
reset/consume/peek loops consume one capacity/count unit. Memory: 80+2C persistent,
128 stack, no work allocation. Tests check these conservative bounds; general
resource proofs are separate obligations.

## Sources and reproducibility

- [RFC9000 §§2–4, 19.4–19.6, 19.8, 19.11](https://www.rfc-editor.org/rfc/rfc9000.html)
  govern offsets, final size, highest-offset flow accounting, cancellation and IDs.
- [multistream-select 9a1fbe8](https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md)
  fixes length-including-newline framing, simultaneous headers, na and optional ls.
- [libp2p Ping c750236](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/ping/ping.md)
  fixes random32 echo, repeated exchanges, half-close and per-peer limits.
- [RFC9000 verified errata index](https://www.rfc-editor.org/rfc/inline-errata/rfc9000.html)
  inspected 2026-11-06. 6811 (CID sequence), 7365 (RETIRE_CONNECTION_ID packet
  type), 7861 (Retry token), 8240 (CONNECTION_CLOSE congestion marking) affect
  core integration, not stream payload/state rules. The fetched index also lists
  9273/9274 but their bodies were not retrievable; applicability is not asserted.

`python3 Tests/Streams/test_oracle.py` then `python3 Tests/Streams/check.py`.
`build.py` creates ignored `build/streams/lake-probe`, requiring the parent repo;
root exports and Lake configuration are never changed. Fixtures precede runtime
implementation. Full register/memory snapshots and every read/write tuple
(pc,write,address,width as LE64 words) are retained in `build/streams/<leaf>`.

## Send: 128-byte LE64 state

| Offset | Value |
| --- | --- |
| 0, 8, 16 | C, owned data base (C bytes), ACK flag base (C bytes, 0/1) |
| 24 | base: lowest retained absolute offset |
| 32 | queued end (includes unsent plaintext) |
| 40 | sent end (contiguous successful actual-send prefix) |
| 48, 56 | supplied stream limit, supplied connection allowance |
| 64 | final size or UINT64_MAX |
| 72, 80, 88 | FIN sent, FIN ACKed, reset Booleans |
| 96, 104, 112, 120 | pending start, length, FIN, active Boolean |

Initialize zero counters/flags/storage, unknown final. Invariant:
`base <= sent <= queued <= base+C`, all offsets <=2^62-1;
known final equals queued. ACK flags describe retained successfully sent bytes.
One reservation per stream is explicit; this is a pending-lifecycle choice, not
an implicit byte cap. Concurrent stream reservations live in separate states;
core supplies the aggregate Limits.maxPendingSends admission and PN records.

- `append(state,stateCapacity,sourceBase,sourceCapacity,sourceOffset,length,FIN,0)`
  queues bytes and optionally seals final size; it reserves no flow credit.
  Capacity overflow is backpressure; calls after finish/reset return closed.
- `reserve(state,stateCapacity,start,length,FIN,0,0,0)` checks retained range,
  `start <= sent`, end <= queued, stream limit and connection allowance. New
  bytes are `max(sent,end)-sent`; exactly this a1 delta is reserved by core.
  a2=first ring-relative view offset, a3=first length, a4=second length at offset
  zero. Core retains FIN/start/length in its send record. Old retransmission
  reserves zero new bytes. Zero-length FIN is represented by an active zero-byte
  reservation. The pending fields remain immutable until settle.
- `settle(state,stateCapacity,success,0,0,0,0,0)` takes 0 known-unsent cancellation
  or 1 actual SendResult success. a1 is the reservation delta: cancellation
  releases it, success transfers it to aggregate committed credit. a4 echoes
  success. Duplicate completion is rejected. Would-block retains the reservation;
  it must NOT settle. Caller validates token/generation and owns PN/history,
  actual send timestamps, congestion/anti-amplification budget and send deadlines.
- `acknowledge(state,stateCapacity,start,length,FIN,0,0,0)` requires a caller-
  authenticated ACK of a recorded successfully sent range. It rejects unsent
  ends; duplicate/retired ACK ranges are harmless. a1 is newly reclaimed storage,
  never flow credit. Only the contiguous ACK prefix is wiped and released, and
  collection stops before any pending borrow. Settling retries collection.
- `stop(state,stateCapacity,0,0,0,0,0,0)` handles local reset/STOP_SENDING. Resolve
  pending I/O first (otherwise status8). It wipes exactly both C-byte regions,
  discards queued unsent data, and publishes reset with final=sent (a4=2). Core
  reliably emits RESET_STREAM with application error code and this final size;
  STOP_SENDING in the opposite direction is not conflated with receive reset.

Bytes remain available for fresh-PN repacketization until reclaimed. Core never
asks this module to retransmit ciphertext. Borrowed plaintext remains immutable
while pending; do not reset/free storage while core has additional copies/views
outside this borrow contract. Stream flow credit is lifetime credit, not returned
by ACK/storage reclamation. Queued unsent=`queued-sent`; retained=`queued-base`;
pending range from the four fields; reserved new credit from its end minus sent.

`validateId(id,localRole,maxStreams,direction,0,0,0,0)` is a separate register-only
leaf, no allocation. role=0 client/1 server, direction=0 receive/1 send.
Status15 is MAX_STREAMS/count violation (count <=2^60); 16 is direction violation.
Returns a1 initiator, a2 unidirectional, a3 ordinal, a4 locally initiated.
Core must select the appropriate advertised/peer limit for type and initiator,
validate locally created IDs/registry/generation, apply implicit opening of lower
peer streams, allocate state, and enforce this profile's zero unidirectional
admission. Validation success alone never claims creation. `ordinal` is a smaller
register-only leaf returning `id/4` in a0; its full execSequence correspondence,
return, register frame, memory preservation and lowering are kernel checked.

Send memory 128+2C persistent, 128 stack, no work. Append has at most length byte
iterations; ACK mark+collection each <=C; settle collection <=C; stop <=C.
Each bound is <=5000+200*(length+C), register-only validation <=5000 instructions.
No packet-number or authentication state is inferred by a stream leaf.

## Multistream: 120-byte LE64 state

| Offset | Value |
| --- | --- |
| 0, 8, 16 | maximum payload bytes, proposal limit, proposals consumed |
| 24, 32 | role (0 dialer/1 listener), phase (0 header/1 proposal/2 selected/3 closed) |
| 40, 48 | partial length accumulator, varint shift (0,7,...,56) |
| 56, 64 | remaining payload bytes, payload position |
| 72 | candidate mask: header1/Ping2/na4 |
| 80, 88, 96 | UTF8 continuations remaining, next-byte low/high |
| 104, 112 | payload-mode Boolean, absolute monotonic deadline |

Initialize phase/parser/proposal fields zero, UTF8 low=128/high=191, configured
finite limits/deadline. Limit <=2^63-1 is the multiformats u63 framing limit, not
a small buffer restriction. There is no payload allocation: unknown valid UTF8
proposals are streamed through scalar validation and rejected with na.

`emit(outputBase,capacity,kind,0,0,0,0,0)` emits framed constants; kind0 listener
header, kind1 dialer header+Ping proposal, kind2 Ping acceptance, kind3 na. Returns
a1 byte length, no stack or state. Caller invokes start exactly once when its
stream opens, queues the output, and sends indicated responses before releasing
related selected-protocol actions. Both sides may emit start simultaneously.
Listing is neither offered nor implemented (`ls\n` receives na as unsupported).
No Noise, TLS-over-QUIC, or Yamux negotiation is emitted.

`feed(state,stateCapacity,sourceBase,sourceCapacity,sourceOffset,length,now,0)`
returns a1 consumed bytes, a2 response kind (0 none/2 Ping/3 na), a3 selected.
At most one frame completes per call. Continue on the same view at `offset+a1`;
when selected, ALL remaining bytes go immediately to Ping (including coalesced
payload). Selected with zero consumption is an explicit dispatch instruction,
not permission to loop on the negotiation leaf. Empty partial input consumes zero
and waits for input/clock; every active loop consumes one byte. Canonical uvarint
length includes newline. UTF8 is strict, embedded newline/zero length rejected.
Every accepted listener proposal increments its configured bound, including Ping.
Dialer na is unsupported/status9; unexpected dialer response is format/status13.
Content errors publish nothing, including parser progress in that fragment;
caller aborts/resets that negotiation, not retries invalid bytes indefinitely.

`timer(state,stateCapacity,now,0,0,0,0,0)` marks an unfinished expired negotiation
closed, clears parser state and returns a4=1 once. Early/stale completed timers
return no action. Caller owns timer ID/generation, clock validation and dispatch.
Feed checks the absolute deadline too; attempts never extend it. All selection
outputs remain uncommitted until peer-authenticated AND handshakeConfirmed.

Memory: 120 persistent +128 stack, no payload work buffer; internal Link calls
use that same frame. One feed is <=5000+300*inputLength instructions; prefix <=9
bytes, payload iterations <=min(remaining,inputLength). Caller caps frames/actions
per quantum, using Limits; (proposalLimit+1) bounds whole negotiation messages.

## Ping: 128-byte state, first 64 bytes LE64

| Offset | Value |
| --- | --- |
| 0, 8 | role (0 outbound/1 inbound), phase (0 idle/1 awaiting reply/2 ready/3 closed) |
| 16, 24 | received byte count (0..32), absolute monotonic deadline |
| 32 | gate bits: authenticated1, handshakeConfirmed2; exactly3 permits application work |
| 40, 48, 56 | local FIN, remote FIN, expected EntropyReady token |
| 64..95 | receive/echo bytes |
| 96..127 | outbound expected entropy payload |

Initialize phase/count/FIN/payload zero. Core sets authentication bits only after
its authentication FSM succeeds. `begin(state,stateCapacity,sourceBase,
sourceCapacity,sourceOffset,length,now,entropyToken)` requires outbound idle,
length=32 and exact expected token. It returns a2=96,a3=32,a4=1 (queue request).
Caller MUST validate a live OS entropy request and generation, single-use token
and deadline before invocation; update expected token for each new request. No
network event can manufacture EntropyReady. Reused test entropy is test-only.

`feed` uses the same source-view arguments but a7=FIN Boolean. It consumes at most
32-count bytes (a1), preserves partial messages and returns one action: a4=1 echo
with state-relative a2=64,a3=32, a4=2 full outbound match (no echo view), a4=3 close
write after clean inbound EOF. Other outputs zero until a whole message exists.
No match result is released early. Partial FIN or missing outbound response is
status13; mismatch is status12. Coalesced messages require release then another
feed on the leftover; FIN applies only after consuming the entire supplied view.

`release(state,stateCapacity,now,0,0,0,0,0)` requires ready and gate/deadline,
after core copies echo into send storage or commits match. It wipes both payloads,
returns idle, or closes after half-close; a4=1 requests next outbound entropy,
3 closes write, 0 waits inbound. `finish(state,stateCapacity,...)` half-closes
write (a4=3) while allowing an outstanding outbound reply; inbound ready echo
must be released first. `cancel(...,now,...)` wipes payload and closes (a4=4).
`cancel true` is the timer leaf: early/already closed is no-op, expiration wipes
and closes (a4=5). Core resolves borrowed views before cancel/timer reclamation,
removes peer quota exactly once, and cancels pending entropy/send/timer records.

`quota(peerCounters,capacity,role,acquire,0,0,0,0)` operates on 16 LE64 bytes:
outbound count at0, inbound at8. acquire=1 or release=0 checks 1/2 local limits,
underflow and malformed counters; a1 is new count. Caller pairs it with validated
live stream handles/generations so one stream cannot release another's slot.

Ping: 128 persistent +128 stack, no work, every payload loop <=32 (wipe <=64),
<=5000 instructions per call. Quota:16+128 bytes, no loops, <=5000 instructions.
Deadline/close actions are internal until core applies authenticated app gating;
only cancellation/timer cleanup may run without gate3.

## Validation and limits of the result

The exact code is emitted from typed SAsm, independently GNU assembled and also
executed from Lean-encoded bytes under QEMU. The harness compares all registers,
all region bytes (including guards and capacity suffixes), every memory access,
and documented instruction budgets. Error fixtures permit only stack writes.
`fixtures.json` pins protocol wire examples and their source revisions;
`manifest.json` exposes machine-readable layouts and callable entries.

`ProofAudit.lean` automatically walks every theorem in owned Spec/Refinement
namespaces and rejects transitive axioms beyond propext/Classical.choice/Quot.sound.
The audit includes compiler-generated theorems; its declaration count is not the
count of substantive protocol invariants. The arithmetic proofs establish source
bounds, credit conservation/idempotence/telescoping, ring-index injectivity,
reservation bounds, retention safety, delivery size and quota limits. The ordinal
leaf has a full 16-instruction fetch/execute/return theorem and runUntil contract
for arbitrary input word/memory, at the stated code/return mapping; its execSequence
and register/memory frame theorems are address-independent.

Whole receive/send/negotiation/Ping refinement, whole-engine termination/resource
proofs and generic constant-time claims remain unproved. No line/branch coverage
percentage or live libp2p network interoperability is claimed. Main must integrate
these leaves with its QUIC frame/recovery/TLS-authentication FSM and validate the
caller obligations above. Historical consumed STREAM overlap conflicts cannot
be detected once bounded storage is released; retained overlap conflicts are
rejected atomically. Only the RFC errata that could be inspected are classified.

Reproduce native checks with `python3 Tests/Streams/check.py --native` and set
`QEMU_RISCV64` / `RISCV_PREFIX` if tools are not on PATH. Defaults are
`qemu-riscv64` and `riscv64-unknown-elf-`. The report verifier is
`python3 Tests/Streams/report.py`; it fails on missing or stale snapshots and
writes `build/streams/report.json` with hashes. It can additionally check the
session's frozen-input inventory with `--baseline <inventory.json>`.
