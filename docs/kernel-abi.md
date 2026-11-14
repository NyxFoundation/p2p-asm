---
title: Kernel resource ABI
last_updated: 2026-11-07
tags:
  - kernel
  - abi
  - rv64im
  - resource-limits
---

# Kernel resource ABI

This module supplies resource operations to main's connection/runtime implementation.
The executable source is typed RV64IM `SAsm`; `Spec/Kernel` is an independent pure
model used by tests and proofs. It supplies no TLS/authentication verdict, packet
number allocation, recovery algorithm, protocol success, or OS memory mapping.

## Calling convention and ownership

Unless stated otherwise, `a0=state`, `a1=state extent`, `a2=input bytes`,
`a3=input length`, `a4=output bytes`, `a5=output capacity`, `a6=selector`,
`a7=reserved`. Return `a0=status, a1=first, a2=second`.
State/output are 8-byte aligned; input bytes may be unaligned. `initBegin` requires
a 16-byte-aligned arena. Every span has a representable nonwrapping one-past end.
`ra/sp/gp/tp/s0..s11` survive. All unused caller registers are zero on return.
Normal leaves use and wipe exactly 256 stack bytes, including saved registers and
scratch. `issueOwned` and `reapOwned` use/wipe 512 bytes and preflight that full extent.
The frozen resolver's aligned reference is copied into wiped stack scratch first.

The caller owns mapped, live state/input/output/stack regions and immutable code.
The mutable spans, input, code, and stack are disjoint; registered external storage
is disjoint from private state/code/stack. These ownership/mapping properties are
host contracts; integer bounds checks do not create a mapping. Numeric span,
alignment, pairwise ABI overlap, capacity, and event-field checks run before access.
Writable external aliases are rejected during registration; read-only aliases are
permitted. Host writes are forbidden while any read/send lease is outstanding.

State is core-owned and structurally valid, with capacities/offsets derived by init,
counts within capacities, live IDs unique, cursors within tables, and matching lease
ownership. Structural validity includes the exact table extent and disjoint payload
partitions. Untrusted selectors, lengths, IDs, generations, times, references, and
response bytes are checked by the operations. Successful execution or a desired
result is never a state precondition. Packet bytes cannot select an ABI entry point,
trusted source envelope, raw pointer, or private state location.

Pass the extent owned by the particular leaf. For root metadata operations this can
be `globalMetadataBytes`; for registry/request/queue operations use the corresponding
table extent. Root-private connection buffers and the reserved stack can then serve
as separate output/work spans. The stack reservation starts at directory[10].
`initBegin` uses a separate 256-byte bootstrap call frame, validates the full mapped
allocation before publication, and records the actual required extent. Steady-state
core stack/storage is bounded by the allocated layout. Host adapter/bootstrap
storage remains an environmental allocation, not a successful-allocation premise.

Content errors leave state and output unchanged, apart from the specified stack wipe.
Successful admission decisions, abort outcomes, cancellation, and scan progress are
state transitions even when their outcome denotes drop/failure. Returned cleanup
records must be consumed by main before advancing the cleanup walk. Kernel cleanup
erases its owned rows/payloads and returns owner handles; main erases TLS/connection
secrets and performs its own teardown.

## Limits serialization and validation

Raw Limits is exactly 488 bytes: 61 unsigned LE64 fields, in the order below.
Every value must be positive. `Spec.Kernel.encodeLimits` validates the original Nat
values before serializing, so nonrepresentable values cannot be truncated.
`decodeLimits` decodes fields; `validateRaw` applies the frozen validator.
`Asm.Kernel.validateLimits` returns `(0,reservedBytes,0)` or the frozen error code.
`exportLimits` validates and copies exactly 488 bytes to output, returning `(0,488,0)`.

| Byte offset | Field | Frozen default |
| ---: | --- | ---: |
| 0 | `maxConnections` | 16 |
| 8 | `maxConnectionsPerSource` | 4 |
| 16 | `maxHandshakes` | 8 |
| 24 | `maxHandshakesPerSource` | 2 |
| 32 | `maxSources` | 64 |
| 40 | `maxStarts` | 16 |
| 48 | `maxStartsPerSource` | 4 |
| 56 | `startWindowNs` | 1000000000 |
| 64 | `handshakeTimeoutNs` | 10000000000 |
| 72 | `maxSockets` | 4 |
| 80 | `maxDatagramBytes` | 2048 |
| 88 | `maxRxBatch` | 32 |
| 96 | `rxWindowNs` | 1000000000 |
| 104 | `maxRxDatagrams` | 1024 |
| 112 | `maxRxBytes` | 2097152 |
| 120 | `maxQueuedDatagrams` | 64 |
| 128 | `maxStreamsPerConnection` | 8 |
| 136 | `streamReceiveBytes` | 65536 |
| 144 | `streamSendBytes` | 65536 |
| 152 | `cryptoBufferBytes` | 65536 |
| 160 | `maxAckRanges` | 64 |
| 168 | `trackedPacketNumbers` | 4096 |
| 176 | `maxSentPackets` | 128 |
| 184 | `maxPathsPerConnection` | 2 |
| 192 | `maxActiveConnectionIds` | 8 |
| 200 | `maxPacketsPerQuantum` | 4 |
| 208 | `maxFramesPerQuantum` | 64 |
| 216 | `maxInputEvents` | 1024 |
| 224 | `completionSlots` | 640 |
| 232 | `maxApplicationRequests` | 64 |
| 240 | `maxPendingSends` | 64 |
| 248 | `maxTimers` | 512 |
| 256 | `maxEntropyRequests` | 32 |
| 264 | `maxClockRequests` | 16 |
| 272 | `maxContinuations` | 32 |
| 280 | `maxActions` | 16 |
| 288 | `maxWallClockDriftNs` | 250000000 |
| 296 | `maxClockSampleSpanNs` | 1000000 |
| 304 | `maxSendWaitNs` | 5000000000 |
| 312 | `maxSendAttempts` | 16 |
| 320 | `maxEntropyWaitNs` | 1000000000 |
| 328 | `maxClockWaitNs` | 1000000000 |
| 336 | `idleTimeoutNs` | 60000000000 |
| 344 | `negotiationTimeoutNs` | 10000000000 |
| 352 | `pingTimeoutNs` | 10000000000 |
| 360 | `maxNegotiationBytes` | 1024 |
| 368 | `maxProposals` | 8 |
| 376 | `maxInboundPings` | 2 |
| 384 | `maxOutboundPings` | 1 |
| 392 | `maxCertificateBytes` | 16384 |
| 400 | `maxHostPublicKeyBytes` | 4096 |
| 408 | `maxInstructionsPerQuantum` | 16777216 |
| 416 | `maxInstructionsPerConnection` | 268435456 |
| 424 | `maxInstructionsGlobal` | 1073741824 |
| 432 | `cpuWindowNs` | 1000000000 |
| 440 | `arenaBytes` | 33554432 |
| 448 | `connectionMetadataBytes` | 65536 |
| 456 | `cryptoScratchBytes` | 65536 |
| 464 | `globalMetadataBytes` | 1048576 |
| 472 | `maxStackBytes` | 16384 |
| 480 | `maxRegions` | 256 |

Frozen validation priority is `range=1`, `connections=2`, `packets=3`, `streams=4`,
`completions=5`, `clocks=6`, `execution=7`, `memory=8`.
`Asm/Kernel/Limits.lean` preserves that order. Sums check carry before using the sum;
products check `MULHU` before using the low product. Overflow in an inequality whose
right side is u64 is rejection in its original error category, matching Nat arithmetic.

Discovered frozen-policy gaps, handled by additional layout rejection (22):

- `reservedBytes` reserves `globalMetadataBytes` without proving all actual resource
  tables fit inside it. It does not independently account for registry, request,
  source, continuation, action, and queue-header tables. Kernel measures them.
- Field positivity permits unaligned metadata and payload segment sizes. Kernel
  requires metadata alignment and adds checked payload/event alignment padding.
- Policy validation alone does not relate an instruction quantum to actual init,
  copy, or request work. Kernel init requires at least 1,000,000 instructions as a
  conservative implementation admission charge; it does not raise the configured
  quantum. This estimate is not a proved full-machine cost theorem.
- No explicit per-source RX caps exist. Kernel derives `max(1,maxRxDatagrams/maxSources)`
  and `max(maxDatagramBytes,maxRxBytes/maxSources)` from the sole Limits policy.

Frozen Limits files are unchanged. Default `reservedBytes=22,560,768`; actual used
bytes equal that value and metadata use is 349,248 within the 1,048,576 reservation.

## Init and arena directory

Root header occupies 1024 bytes. Words 0..6 are `(phase,used,cursor,metadataUsed,
allocated,codeBase,codeLength)`. Phase 1 means initializing; phase 2 means ready.
Words 8..19 hold the byte-offset directory below. Raw Limits occupies bytes 512..999.
Words 20/21 own connection-cleanup mode/cursor; word 22 owns the scheduler lane.

| Directory index | Region | Size |
| ---: | --- | --- |
| 0 | Registry | `128 + 64*maxRegions` |
| 1 | Requests and timers | `256 + 128*N + stride*R` |
| 2 | Ingress/source quotas | `256 + 128*maxSources` |
| 3 | Connection quota/CPU leases | `128 + 64*maxConnections` |
| 4 | Continuations | `64 + 256*maxContinuations` |
| 5 | Actions | `64 + 256*maxActions` |
| 6 | Three input queue headers | `3*64` |
| 7 | Connection buffers | Frozen per-connection reservation |
| 8 | Datagram buffers | `(maxQueuedDatagrams+maxPendingSends)*maxDatagramBytes` |
| 9 | Input event cells | `256*maxInputEvents` |
| 10 | Stack | `maxStackBytes` |
| 11 | End | Actual used bytes |

`R=maxPendingSends+maxEntropyRequests+maxClockRequests`, `N=R+maxTimers`,
`stride=alignUp(maxDatagramBytes,8)`. Metadata regions start at 1024 and are contiguous.
Connection buffers start at `globalMetadataBytes`; event cells start after checked
16-byte alignment of the datagram end. All sums/products/rounding are checked.
The three queue headers point into disjoint event-cell slices for network,
application, and completion. Remaining event cells remain reserved and zero.

`initBegin`: input=raw Limits, state=actual mapped arena, a6/a7=code base/length.
It validates everything, clears the 1024-byte header, installs offsets and Limits,
and returns `(0,1,1024)`. It does not publish ready.
`initResume`: no input. Clears at most 4096 bytes from the owned cursor. Returns
`(0,1,nextCursor)` while pending. The final call initializes table headers and
returns `(0,0,used)` with phase 2. Repeating after ready is stale (14).
Large allocations never imply one large unbounded clear.

## Registered storage and borrowed views

Registry header words: `capacity,active,inputBorrowCount,sendBorrowCount,privateBase,
privateLength,codeBase,codeLength,pending,slot,base,length,writable,scanCursor,
expectedGeneration,inputDrainCursor`. Pending registration owns words 8..14.
Input drain cursor is zero when idle, otherwise next slot index plus one.

After the header are `capacity` original 32-byte resolver descriptors:
`generation,base,capacity,flags`. Flags are `active=1,writable=2` only.
After descriptors are equally many 32-byte side records:
`inputBorrow,sendBorrow,writeBorrow,retired`, each 0 or 1.
A reference remains exactly `(slot,generation,offset,length)` as four LE64 values.
The original `Asm.resolveBuffer` is unchanged, including its strict nonwrapping
one-past contract, flag validation, and status 1..5 meanings.

| Entry | Input | Result / effect |
| --- | --- | --- |
| `registryBegin` | slot,gen,base,length,writable | Validate and stage; `(0,1,0)` |
| `registryResume` | empty | Scan at most 32 descriptors; first 1=more, 0=published, 2=aborted overlap (second=18) |
| `registryMutation 2` | slot,gen | Unregister only without borrows; clear descriptor; increment generation or retire permanently |
| `registryMutation 3/4` | slot,gen | Acquire/release input read lease |
| `registryMutation 5/6` | slot,gen | Acquire/release immutable send lease |
| `registryMutation 7/8` | slot,gen | Acquire/release exclusive write lease |
| `registryEndStep` | empty | Clear at most 32 input leases; first 1=more, 0=finished; second=cursor |
| `resolveRegistered` | reference; a6=write 0/1 | Call original resolver; require matching lease; return address,length |
| `copyRegistered` | reference | Copy complete borrowed view to disjoint private output; return length,0 |

Read and send leases can coexist. Each kind has at most one outstanding lease per
region, so double release is rejected without decrementing another borrow. Writes
exclude every read/send lease. Unregister/retire and mutation cannot invalidate a
borrow. Borrow release remains available during a registration scan. Registration
checks every existing active descriptor before publication; scan collisions clear
only the staged candidate and leave published descriptors unchanged.
`copyRegistered` is bounded to 65536 bytes per call (an instruction-work bound);
caller also enforces the relevant Limits payload policy. Oversized copies return
backpressure before writes. A continuation must own the completed private copy;
finish `registryEndStep` before returning host memory. No continuation retains the
resolved host pointer. Private code/state is excluded by registration, and mapped
lifetime and alias permissions remain host obligations.

## Queues and source envelopes

Queue header is 64 bytes: `(capacity,head,count,reserved,source,dataOffset,0,0)`.
Cells are 256 bytes: `(source,payloadLength,0,0)` followed by 224 owned payload bytes.
Unused bytes are zero. `dataOffset` is relative to the queue header, allowing the
input cell slices to be separate from metadata. Ordinary contiguous queues use 64.

Sources: `0=network,1=application,2=host completion,3=continuation,4=action`.
The adapter/core chooses the source from the call channel, never from packet bytes.
Enqueue overwrites the stored source with that trusted envelope. Application and
continuation payloads larger than 224 bytes require an owned private buffer/reference
managed by main; raw host pointers cannot be retained as executable references.

`queueReserve false` reserves before dispatch; `queueReserve true` cancels an owned
reservation. `queueEnqueue false` requires `count+reserved<capacity`: full network
returns drop 20 and other producers backpressure 19. `queueEnqueue true` accepts
only source 2 and consumes an existing completion reservation. It is an internal
leaf called after request matching, not an untrusted callback authorization oracle.
`queueDequeue` copies exactly 256 bytes and wipes the cell, returning source,length.
Completion reservations are linear kernel-owned resources. A reservation is never
created by network/application input or inferred from completion payload bytes.
Request/timer completions also have their own reserved in-place cells below; they
remain available even when ordinary input or notification queues are full.

## Requests, completion reservations, and timers

Header is 256 bytes. Words 0..14 are `(N,reserved,nextID,completionCapacity,
sendCap,entropyCap,clockCap,timerCap,sendUsed,entropyUsed,clockUsed,timerUsed,
stride,maxActions,actionsUsed)`. Words 16/17 own cleanup mode/cursor; 18..20 hold
send/entropy/clock deadlines; 22 is the ready cursor; 23 is the expiry cursor.
All remaining words initialize to zero. Next ID starts at 1. Zero means exhausted;
issuing the maximum ID explicitly sets that sentinel without emitting ID zero.

A slot is 128 bytes, words `(generation,phase,id,kind,deadline,expectedLength,
ownerSlot,ownerGeneration,pendingAuthentication,leaseSlot,leaseGeneration,0,0,0,
outcome,responseTime)`. Phases: 0=free, 1=pending, 2=completed, 4=retired.
Kinds: 0=send, 1=entropy, 2=clock, 3=timer. Timer slots are the final `maxTimers`
slots and have no payload allocation. Non-timer payloads are fixed disjoint strides
after the slot array. Kind quotas and total completion reservations include both
pending and completed rows. Thus completed resources remain reserved until consumed.
`pendingAuthentication` is core bookkeeping derived from the owning connection's
phase; it is never a host-supplied authentication verdict.

- `requestIssue`: input 11 words `(slot,gen,kind,now,timerDelay,expectedLength,
  owner,ownerGen,pendingAuthentication,leaseSlot,leaseGen)`. It validates the slot,
  quotas, ID, action allowance, and nonwrapping deadline before any write. It reserves
  its completion cell before publishing a 128-byte action descriptor. Returns ID,deadline.
  Non-timer delays come from Limits; only generic timers use the supplied timer delay.
- `requestComplete`: trusted host envelope a6=2; input seven words `(slot,gen,id,
  kind,now,result,length)` plus response bytes. Matching precedes mutation. Result
  codes 0=success, 1=would-block, 2=message-too-large, 3=failure; nonzero results for
  entropy/clock abort that request. Exact length and actual body length must match.
  Invalid duplicate/stale responses do nothing. Late responses abort; early timer
  expiry returns 25. Private payload is wiped before any successful fresh response
  copy. No failed entropy/clock bytes are reused.
- Outcomes stored/returned: 0=success, 1..3=external result, 4=expired, 5=canceled,
  6=length mismatch. Length mismatch takes precedence over other abort outcomes.
  A matched abort returns status 0 with the outcome in first, and phase 2.
- `requestReap`: input slot,gen; output capacity at least `128+stride`. Copies the
  descriptor and non-timer payload, wipes private payload and row fields, releases
  reservation/kind count, and increments generation or retires. Returns ID,outcome.
  Sensitive output belongs to main's private consumer; main controls its lifetime.
- `requestStop false/true`: cancel/expire by `(slot,gen,id[,now])`. Marks exactly one
  completion, wipes owned payload, preserves its reservation for cleanup delivery.
- `requestNext`: inspect at most 32 slots, using the owned round-robin ready cursor.
  First=slot+1 when ready, else zero; second=next cursor. It does not consume/apply.
- `requestExpireNext`: input now; inspect one deadline slot using its owned cursor.
  Expiry independently wipes and queues a completion, even if no host response arrives.
  First=slot+1 on expiry, else zero; second=outcome or visited slot when unchanged.
- `requestCleanup`: a6=1 pending authentication or 2 all owners. One slot per call,
  preserving scope/cursor in state. Both pending and queued matching requests are
  canceled and wiped. First 1=more, second=cursor; first 0=done. Consume/reap the
  reserved results afterwards; no cleanup completion is thrown away.

`issueOwned`/`reapOwned` take root metadata and combine request issuance/consumption
with registry send leases. Failed issuance rolls a newly acquired lease back.
Successful consumption releases its immutable send lease exactly once. Recovery
owns packet numbers, send attempt semantics, would-block policy, MTU, and retry limits.
These leaves report OS/request outcomes without treating them as peer delivery.

## Admission, quota leases, and scheduling

Ingress header is 256 bytes and source records are 128 bytes. Header words are:
`0 sourceCount; 1..5 RX epoch/currentDatagrams/currentBytes/previousDatagrams/previousBytes;
6 lastTime; 7 batchUsed; 8/9 global RX caps; 10 window; 11 maxBatch; 12 drops;
13..15 start epoch/current/previous; 16/17 handshake caps; 18/19 start caps;
20 startWindow; 21 globalHandshakes; 22 globalConnections; 23/24 connection caps;
25/26 derived source RX caps; 28 maxDatagramBytes`.
Source words 0..5 hold the same RX window plus last time; 6..8 hold start window;
9 handshakes, 10 connections, 11 drops. Remaining fields are zero/reserved.
Host source-key mapping must keep a stable source slot during a live window/lease.

`admitDatagram` input `(sourceSlot,now,length,truncated)` counts every valid-envelope
UDP arrival before parser/authentication work. Current+entire previous buckets are
counted, conservatively enforcing rolling-window caps. Oversized/truncated/invalid
or authentication-failed datagrams still consume admission counters. Counters saturate
at u64 max with no per-drop logging. Status 0 first=0 accepts; first=1 yields with
second `1 rate,2 batch,3 length,4 truncation` (later checks take precedence).
Saturation does not allocate connections, close an existing connection, or consume
completion reservations. Source indices and time regressions fail before indexing.

Connection/CPU header is 128 bytes: `(capacity,globalEpoch,globalUsed,quantumUsed,
window,maxQuantum,maxConnection,maxGlobal,maxActions,actionsUsed,roundRobinCursor,0...)`.
Each 64-byte slot is `(generation,quotaPhase,source,epoch,used,0,0,0)`.
Quota phases 0=free, 1=handshake lease, 2=connection lease, 3=retired.
`connectionAcquire` takes root and `(slot,gen,source,now)`; checks global/source
concurrent and conservative rolling start quotas atomically before granting a lease.
`connectionRelease true` returns the handshake quota without authenticating anything.
`connectionRelease false` returns all remaining quotas and advances/retire generation.
`connectionCleanup` a6=1 handshake leases or 2 all leases walks one slot per call;
first 1=skip/more, 2=released (mandatory 32-byte owner record), 0=done. Second is the
visited index. Main performs TLS/core cleanup for the returned handle before advancing.
New allocation is locked throughout that walk.

`charge` input `(connectionSlot,generation,now,operationCharge,actionCharge)` admits
positive work against quantum, per-connection, global-window, and action budgets.
All additions are guarded by available-budget subtraction. The charge is supplied by
the caller's certified bound or conservative estimate; a measured number is not a
proof. Every operation, including failure/cleanup work, must be admitted by main's
quantum driver before invocation. The local request action allowance is an additional
guard; the global ledger accounts for actions across every producer.

`kernelQuantum` takes root and rejects outstanding input leases/drain cursors. It
resets per-quantum RX/request/action counters and cycles lanes independently of
payload: `0 completions,1 timers,2 connection continuations,3 applications,4 network`.
First is the current connection slot, second the lane. The connection cursor advances
only on lane 2, preventing starvation when connection count is a multiple of five.
Invoke the ready/deadline walkers on their lanes and bounded FIFO work on the other
lanes. An ingress drop/yield ends network work for that slice. Main owns the actual
execution loop; these leaves do not claim a full runtime fairness theorem.
`nextQuantum` is the lower-level ledger-only round-robin helper.

Time inputs must already be accepted by main's unchanged `Asm.checkClock` contract.
Guard 24 is an arithmetic regression rejection, not a replacement clock verdict.
Wall-clock faults select pending-authentication cleanup; monotonic faults select all
owners. Main controls authentication suspension, connection failure, and TLS erasure.

## Status and proof scope

Outside frozen Limits/resolver-specific codes, statuses are: `9 nonwrapping span`,
`10 alignment/ABI alias`, `11 capacity`, `12 selector`, `13 bounds`, `14 stale`,
`15 busy`, `16 retired`, `17 exhausted/overflow`, `18 region overlap`,
`19 backpressure`, `20 network queue drop`, `21 read-only`, `22 layout/charge`,
`23 source envelope`, `24 time regression`, `25 not yet expired`.

Every loop has an actual instruction counter: registry scan/drain 32 slots,
request-ready scan 32, expiry/cleanup one slot, initialization 4096 bytes, queue
copy 224 bytes, payload operations at most the derived stride (65514 at maximum
validated datagram policy), and borrowed copy 65536 bytes. No budget is increased to
fit observations. The test execution ceiling remains the existing 2^24 quantum.

Proofs cover release/inactive/retirement behavior, reservation conservation and
capacity, exact admitted charges and bounds, pointer arithmetic, and the actual
four-instruction generation block with exact machine state. Two fetched small-leaf
boundary executions are kernel-checked as well. They do not establish full kernel,
layout, memory separation, complete lifecycle refinement, or whole-core resource
proofs. Transitive axiom audit automatically enumerates every owned theorem and
permits only Lean's `propext`, `Quot.sound`, and `Classical.choice`.

## Reproduction

Run `python3 Tests/Kernel/check.py` and `python3 Tests/Kernel/audit.py`.
Set `QEMU_RISCV64` / `RISCV_PREFIX` or use `--qemu` / `--prefix` when tools are not on
PATH. The native model is built by Lake in ignored `build/kernel/lake-probe`.
When this worktree lacks the frozen Limits sources, `KERNEL_FROZEN_ROOT` selects a
read-only source tree (default sibling `p2p-asm`); only the ignored package is
written. No shared/frozen source or another worktree is modified.
Tests compare independent Python states and arithmetic, pure Lean Specs, full fetched
RV64 instruction registers/memory/footprints, GNU byte equality, GNU-assembled QEMU,
and encoded-byte QEMU. Measurements are observations recorded separately from proofs.
