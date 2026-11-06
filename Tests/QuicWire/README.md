# QUIC v1 wire leaves

This component owns the wire syntax and local transport-parameter semantics only.
It contains independent pure Lean specifications and ordinary typed RV64IM
instructions, using the frozen QUIC varint leaves and Crypto.Util/Link. No runtime
protocol library, crypto library, host callback, or protocol opcode is involved.
The root integration must import `Libp2pAsm.Spec.Quic.Wire` and
`Libp2pAsm.Asm.Quic.Wire`; root files and shared Limits are intentionally untouched.

## Reproduce

Run from a clean checkout with Lean **4.33.0** (`lean-toolchain`), Python **3.14.8**,
GNU RISC-V binutils **2.47**, QEMU user **11.1.2**, and Go **1.24.1** for the separate
oracle. Python uses only its standard library. Executables are resolved from PATH;
`QEMU_RISCV64`, `RISCV_PREFIX`, and `GO` can select explicit tool locations.

```sh
python3 Tests/QuicWire/check.py --help
python3 Tests/QuicWire/check.py --qemu "$QEMU_RISCV64"
python3 Tests/QuicWire/oracle.py
python3 Tests/QuicWire/audit.py
python3 Tests/QuicWire/report.py
```

`check.py` creates a nested Lake test executable under `build/quic-wire/lake-probe`;
it does not edit the root package. Semantic fixtures compare independent Python,
Lean Spec, and fetched RV64 instructions. ABI preflight/capacity fixtures use
explicit ABI expectations; permission fixtures use the independent table and
the separate kernel proof described below. Every execution checks all 32 registers
and every mapped byte, strict per-instruction access footprints, GNU assembled bytes, and QEMU
executions of **both** GNU assembly and directly encoded bytes. Results and
instruction counts are saved under `build/quic-wire/<leaf>/`. All admitted stack
and workspace bytes, output sentinels, source bytes, and callee registers are
checked. Error outputs retain their original sentinels. Source/output pointers
are deliberately unaligned; workspace is word aligned.

The oracle uses a generated, pinned `github.com/quic-go/quic-go v0.59.0` module,
with extensions disabled, under `build/quic-wire/go-oracle`. Its `go.sum` is seeded
from the pinned test lock. Offline execution uses an existing Go module cache.
This is a codec comparison, not a live QUIC handshake or interoperability claim.
quic-go's CRYPTO codec accepts offset+length overflow and leaves that check to
its caller; this intentional recorded difference is rejected here. Its packet
codec accepts Length=0 and has different unsupported-version/VN boundaries, so
those cases are checked against the independent Python/Lean specifications.
Empty STREAM encoding can be refused by quic-go's builder even when its parser
accepts it; parse success is compared separately from its optional re-encoding.
TP oracle inputs include the mandatory connection CIDs because quic-go also
checks their presence. Cross-message matching remains outside this wire codec.

## Public ABI

All public parser/encoder leaves have the following arguments:

| Register | Meaning |
|---|---|
| a0, a1 | input base and **attacker-controlled** available byte length |
| a2, a3 | output base and capacity in bytes |
| a4, a5 | workspace base and capacity in bytes |
| a6 | packet: short destination CID length; TP: sender server=1/client=0; frame: unused |
| a7 | frame: maximum ACK **total** ranges; TP: maximum parameters including unknown IDs |

Return a0 is status, a1 is error offset (zero on success), a2 is consumed input
bytes for parsers or written bytes for encoders (zero on error). Encoder errors
use offset zero. Parser error offsets identify the checked cursor at failure;
semantic rejection can point immediately after the offending scalar or vector.
Preflight errors use zero; batches add the element's source base.
All other caller-saved integer registers are zero. s0..s11, ra,
sp, gp, and tp are preserved. Standard leaves use **256 bytes** below a 16-byte
aligned sp; the complete frame is wiped. There are no heap allocations.

| Status | Meaning / caller handling |
|---|---|
| 0 | success; only then is output published |
| 1 | truncated source or invalid source view |
| 2 | malformed envelope/value representation |
| 3 | RFC scalar/vector/range constraint failed |
| 4 | address-range wrap or stack underflow |
| 5 | local output/work/range/iteration capacity exhausted |
| 6 | writable/input/stack overlap or alignment violation |
| 7 | unknown RFC 9000 frame type; FRAME_ENCODING_ERROR |
| 8 | repeated TP ID, including an unknown ID; TRANSPORT_PARAMETER_ERROR |
| 9 | sender-role or encryption-level violation |
| 10 | invalid local option or unsupported builder kind/features |

For authenticated frame inputs, 1/2/3/7 map to FRAME_ENCODING_ERROR (0x07).
For TP input, 1/2/3/8/9 map to TRANSPORT_PARAMETER_ERROR (0x08).
Permission rejection maps to PROTOCOL_VIOLATION (0x0a). Local capacity and ABI
errors are not automatically peer transport errors. Packet parsing never
authorizes closing a connection based on unauthenticated bytes.

Preflight checks nonwrapping input/output/work ranges, capacity, alignment,
and pairwise disjointness of input, complete declared output/work spans and
the stack frame **before reads or writes**. Empty spans are not dereferenced.
Ranges ending at 2^64 are allowed when the last accessed byte is representable.
Caller must map the entire admitted spans with correct permissions, map the
stack, provide aligned executable code, and keep code disjoint from writable
storage. These are mapping/ownership preconditions, not assertions that a load
will validate an arbitrary pointer. Code mapping is checked by the test ISA model.

Parsers initialize private staging and publish only after all validation.
Encoders wipe the entire declared workspace on entry, then stage output, publish
on success, and wipe the written staging prefix on every exit. Preflight failure
touches no memory. Output after successful encoding contains intentional network
plaintext until the caller protects it; source plaintext belongs to the caller,
which must wipe/release it after use. Views expire with the source loan.

## Descriptor layouts

Descriptors are arrays of **64-bit little-endian words**. Listed indices are
word indices (byte offset = index * 8). View pairs are `(source offset,length)`;
they are never pointers. Reserved words are zero. Output descriptors may be
unaligned, since publication uses byte stores.

Packet parser (`packetParse`), 128 bytes:

| Words | Meaning |
|---|---|
| 0, 1 | consumed length; kind: short=0, Initial=1, 0RTT=2, Handshake=3, Retry=4, VN=5, unsupported=6 |
| 2, 3 | raw first byte; version (short uses zero) |
| 4–5, 6–7 | destination/source CID views |
| 8–9 | Initial/Retry token view |
| 10, 11 | PN offset and protected wire length (including PN) |
| 12–13 | VN version list / Retry integrity tag / unsupported-version opaque tail view |
| 14–15 | zero; no PN-length/key-phase interpretation before crypto |

Version-zero lists are nonempty and a multiple of four bytes. Retry exposes a
nonempty token and exactly 16 tag bytes without asserting tag validity. Short,
Retry, VN, and unsupported versions consume the remaining datagram. Supported
long packet Length bounds **only that packet**, permitting coalescing. CID lengths
are at most 20. Nonminimal received varints are accepted. PN/sample/tag bounds,
removing protection, reserved bits after authentication, PN reconstruction,
AEAD, Retry integrity, VN role/version/CID policy, and minimum datagram size are
caller obligations. The raw byte is not an authenticated field.

Frame parser (`frameParse`), 128 bytes plus ACK ranges. Words 0/1 are consumed
length/type. The following fields start at word 2:

| Type | Successive fields starting at word 2 |
|---|---|
| PADDING/PING/HANDSHAKE_DONE | none |
| ACK(+ECN) | largest, delay, additional-range-count, first-range-length, ECT0, ECT1, CE, encoded-ranges-offset, encoded-ranges-length |
| RESET_STREAM | stream ID, application error, final size |
| STOP_SENDING | stream ID, application error |
| CRYPTO | logical offset, data offset, data length |
| NEW_TOKEN | token offset, token length |
| STREAM | stream ID, logical offset, data offset, data length; flags retained in type |
| MAX_DATA / MAX_STREAMS / DATA_BLOCKED / STREAMS_BLOCKED | limit/count |
| MAX_STREAM_DATA / STREAM_DATA_BLOCKED | stream ID, limit |
| NEW_CONNECTION_ID | sequence, retire-prior-to, CID offset, CID length, reset-token offset, 16 |
| RETIRE_CONNECTION_ID | sequence |
| PATH_CHALLENGE/RESPONSE | data offset, 8 |
| CONNECTION_CLOSE | error, triggering frame type (zero for application form), reason offset, reason length |

ACK word 16 onward holds **all** inclusive `(low,high)` pairs in descending order,
including the first range: required size `128+16*(additional-count+1)`.
Each range is nonempty, disjoint, and separated by at least one unacknowledged PN.
Remaining-byte and caller-capacity checks precede the range loop. Unsent-PN and
ACK delay semantics belong to recovery. Stream/CRYPTO offset+length is bounded
by 2^62-1. Stream counts are at most 2^60. Implicit STREAM length consumes the
remaining plaintext packet, including anything resembling a subsequent frame.
Unknown types are rejected, never skipped. Nonminimal type reception is tolerated
under RFC 9000 12.4's MAY reject rule; builders always use the shortest type.

TP parser (`transportParse`), 512 bytes: word 0 consumed, word 1 total parameter
count, word 2 presence mask for known IDs 0..16, word 3 zero. For known ID `i`,
words `4+2*i` and `5+2*i` contain `(integer,0)`, a view, or `(1,0)` for
disable_active_migration. Absent integer defaults are idle/data/streams=0,
max_udp_payload_size=65527, ack_delay_exponent=3, max_ack_delay=25,
active_connection_id_limit=2. Presence mask distinguishes absence and zero.

Known IDs are the RFC 9000 18.2 assignments. For preferred_address, the ordinary
pair is its full raw view; words 40..49 additionally contain IPv4 offset,4,port,
IPv6 offset,16,port,CID offset,CID length,token offset,16. Addresses and ports
are fully bounded and ports are returned as host-independent scalar integers.
CID length is 1..20 and vector length is exactly 41+CID length.
Unknown well-formed IDs are ignored **after** duplicate checking. Integers consume
their entire value span; nonminimal integer encoding is legal. The caller checks
required original/initial/retry CID presence and equality across messages, whether
Retry was used, and state-dependent preferred-address/CID restrictions.

## Builders and permission leaf

`packetEncode` consumes the same 16-word input format followed by source bytes.
The fixed header is required in full (128 bytes for packet/frame builders,
512 for the TP builder), even when a selected form uses fewer fields. Packet
builders validate all four supplied views, including views unused by that kind.
Input word 1 selects kinds 0..5; word 2 permits only spin bit 0x20 and key-phase
bit 0x04 (both used only by short headers), word 14 is PN width 1..4,
word 15 is the already truncated PN fitting
that width. Views 4/6/8 refer to CID/token bytes; view 12 refers to payload bytes
excluding PN, or the Retry tag / VN list. It emits v1 (VN emits zero), minimal
length/token varints, zero reserved bits, and fixed bits. Packet protection is a
separate caller step. Unused source bytes are not silently interpreted as payload.

`frameEncode` consumes the frame descriptor plus source bytes, with view offsets
adjusted to that combined source. ACK pairs follow its 128-byte header and must
agree with largest/first/count. Every type and STREAM flag variant has a bounded
encoder. Zero implicit offsets, PN/count bounds, and lengths are checked rather
than truncated. All varints are minimal; byte-string contents are preserved.

`transportEncode` consumes the 64-word TP descriptor plus source bytes. It
serializes supplied idle, UDP, data, bidirectional flow/stream, ACK and active-CID
limits, always advertises no active migration and zero uni stream/data capacity,
and includes initial SCID. Presence bits 0/2/16 request server original DCID,
reset token, and Retry SCID. Preferred address/unknown mask bits are rejected;
no extension is advertised. The pure typed API is `ProfileParameters`.

`framePermission` instead takes a0=type, a1=Initial(0)/Handshake(1)/0RTT(2)/1RTT(3),
a2=sender client(0)/server(1). It returns status in a0 and ack-eliciting/in-flight
flags in a1/a2 (zero on rejection). It has no stack or memory accesses. It handles
server-only NEW_TOKEN/HANDSHAKE_DONE, client-only 0RTT, and the full level table.
The profile's unconditional rejection of 0RTT is still the core's policy.

## Batches and admission bounds

`batchParse true/false` is an actual RV64 caller of the packet/frame leaf. a6 is
the short CID length for packets or maximum ACK total ranges for frames; a7 is
batch capacity. The complete batch is staged; an invalid second element cannot
publish a valid first element. Empty input succeeds with count zero. Capacity
exhaustion returns status 5 and the next element's source offset.

The output is `[consumed,count]` followed by fixed-capacity slots. A slot contains
`[element-source-base,descriptor...,zero-padding]`. Slot bytes are 144 for packets,
or `144+16*ackCapacity` for frames. Views within each element are relative to its
recorded source base. Output bytes = `16+slotBytes*batchCapacity`; required work
bytes = output bytes + slot bytes - 16. Multiplication/addition are checked before
use. All spare slots are zero. Stack is 512 bytes (256 caller + 256 child); unused
child stack is untouched when no child is invoked. Single-call batches preserve
coalescing semantics; they do not concatenate distinct UDP datagrams.

`Asm.Quic.Wire.Resources` exposes natural-number workspace and instruction
admission calculations. In `instructionBound`, S is the entire linked instruction
count, n the input length, R=min(ACK capacity,n/2+1), P=min(TP capacity,n/2).
It conservatively charges S for each bounded loop/call iteration: packet byte
publication/wipes and at most four varints; frame staging plus ACK pairs/varints;
TP staging plus at most P previous-ID scans per parameter; encoder workspace
wiping/output and bounded source/range loops; batches plus all child ceilings.
TP duplicate checking is quadratic: at most P(P-1)/2 prior entries, with at most
two bounded varints and one checked skip per entry. Every iteration consumes at
least two input bytes. No declared count can cause a loop without byte/capacity
admission. All arithmetic in admission calculations must remain mathematical
integers until checked against RV64 word limits. Main must charge these costs
against its configured quantum; local caps are not RFC maxima.

These are structural ceilings checked against each test execution. General
instruction/heap/stack bounds for the **entire linked parsers** are not yet
kernel-proved. Theorems cover checked parser consumption/truncation, span and
stream bounds, ACK disjointness/admission/workspace arithmetic, parameter-loop
progress/scan count, encoder capacity/header admission, reserved-bit construction,
and actual RV64 arithmetic/advance macros. The permission proof kernel-checks
all 31 standard frame tags × four levels × two roles against fetched RV64
execution, from an explicit zero-register state with its ABI inputs/return set.
The materialized instruction array is kernel-proved equal to the actual builder's
flattened code; it is not a second unchecked implementation. Finite execution
tests check nonzero register preservation, cleared temporaries, and memory
footprints; this theorem does not prove preservation for arbitrary initial states.
The axiom audit enumerates every declaration
with a theorem type in the owned refinement namespace. Full parser refinement,
FSM correctness, authentication, CT, liveness, and end-to-end integration are
not claimed. Finite cases do not establish source coverage.

## Normative sources and errata

- [RFC 9000](https://www.rfc-editor.org/rfc/rfc9000.html): 12.2/12.4/12.5, 16–19.
- [RFC 9001](https://www.rfc-editor.org/rfc/rfc9001.html): 5.4, 5.8, Appendix A.
- Verified [EID 7365](https://www.rfc-editor.org/errata/eid7365): RETIRE_CONNECTION_ID
  is excluded from 0RTT; reflected in permission checks.
- Verified [EID 8240](https://www.rfc-editor.org/errata/eid8240): CONNECTION_CLOSE
  does not count toward bytes in flight; reflected in classification.
- Verified [EID 6811](https://www.rfc-editor.org/errata/eid6811) concerns CID
  issuance state; [EID 7861](https://www.rfc-editor.org/errata/eid7861) concerns
  Retry-token policy. Both belong to the caller, not envelope authentication.

- Verified EIDs [9273](https://www.rfc-editor.org/errata/eid9273) and
  [9274](https://www.rfc-editor.org/errata/eid9274) fix threat-model/registry
  terminology and do not change these wire layouts.
- RFC 9001 [EID 7785](https://www.rfc-editor.org/errata/rfc9001) is rejected;
  reconstructed packet numbers remain 62 bits. The
  [EID 9231 report](https://mailarchive.ietf.org/arch/msg/quic/aqdxmeYDs7v17d4f9Xqxc6M29fA/)
  proposes changing the Appendix A.2 example's SCID/PN layout. Its available
  October 21, 2026 notice says **Reported**, not Verified. Original RFC vectors
  are retained as wire/protection fixtures, not as a cross-message CID-valid
  handshake. The errata website's live redirect was unavailable, so a later
  status change has not been established here.

Packet protection is frozen and outside ownership. RFC vectors and the quic-go
test oracle retain their notices under LICENSES/Quic-Wire-*.txt.
