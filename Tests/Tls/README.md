# TLS 1.3 SHA256 parts

Owned production modules are `Libp2pAsm/{Spec,Asm,Refinement}/Tls/`.
The independent Specs execute pure Lean functions. The runtime entries generate
ordinary typed RV64IM, lower through the existing checked SAsm/Link machinery,
and call the frozen SHA256/HMAC/HKDF implementations. There is no runtime TLS
library, Spec interpreter, host-authentication callback, or new opcode.

## Scope and integration obligations

This is the full (EC)DHE SHA256 key schedule and raw **handshake** message codecs,
not a TLS FSM or TLS record layer. Main owns message ordering, encryption levels,
certificate DER/PeerID/identity/signature verification, ECDHE point validation,
transport parameter semantics, transcript storage/reassembly, retries, scheduling,
and overall integration. TLS KeyUpdate and every TLS record envelope (including
ChangeCipherSpec) must pass `Codec.admitQuic` before handshake decoding. Byte 20
alone is ambiguous: Finished handshake type and ChangeCipherSpec content type
have the same number. The admission API requires the real envelope classification.

A successful parser result is **not** a negotiation/authentication decision.
View word 3 contains outstanding obligations (bits):

| Bit | Caller obligation |
| --- | --- |
| 0 | Validate server/certificate/ticket extension solicitation and context |
| 1 | Match selection to saved ClientHello, including exact echoed session ID |
| 2 | Verify certificate identity or CertificateVerify signature using main's crypto |
| 3 | Validate opaque QUIC transport parameters semantically |

Independently of these per-message flags, the FSM must enforce CertificateRequest
and exactly one client certificate, verify both Finished values against the
correct transcript, require negotiated ALPN `libp2p`, and reject unexpected
messages. For SH/HRR it must check offered suite/group/share, exact echoed session
ID, no second HRR, retry group not already shared, permitted CH2 changes, echoed
cookie, and transcript rewrite. CertificateRequest's advertised signature list
must constrain the client's signature; 0401 is certificate-only, never TLS1.3
CertificateVerify. Server extensions in EncryptedExtensions remain explicit views
with bit 0 set, including unknown ones; the caller must reject unsolicited ones.
Unknown ServerHello extensions are rejected outright, as RFC8446 permits only
supported_versions/key_share (plus HRR cookie) here. Receive-side ClientHello SNI
is ignored; both encoders reject ClientHello SNI emission.

No PSK/resumption/0-RTT, ticket acceptance, TLS record encryption, public-key
arithmetic, or TP semantic parser is implemented here. NewSessionTicket is checked
and exposed for discard, without feeding its contents into the key schedule.

## Status and memory contract

All entries return status in a0. Other caller-saved registers are zeroed; ra, sp,
gp, tp, and all s-registers are preserved. Input bytes and descriptors are
immutable. There is no partial output on failure.

| Status | Meaning |
| --- | --- |
| 0 | Success |
| 1 | More bytes needed for the outer handshake message |
| 2 | Malformed length/vector/grammar or invalid scalar argument |
| 3 | Unsupported handshake/context or prohibited QUIC envelope |
| 4 | Address wrap, alignment, overlap, stack underflow |
| 5 | Caller output/work capacity insufficient |
| 6 | Duplicate extension or key-share group, including unknown IDs |
| 7 | TLS/libp2p profile violation |
| 8 | Crypto callee failure |
| 9 | Caller-configured byte/operation limit exceeded |

Descriptor addresses are 8-aligned. All actually accessed external spans,
descriptor, output, workspace, constants, and reserved stack must be pairwise
disjoint and nonwrapping. Empty input spans need no mapping and may have any
pointer. Last-byte checking permits a span ending exactly at 2^64. Callers must
provide mapped/readable input/table/descriptor, writable output/work/stack, and
separation from executable code. Metadata validation checks numeric spans and
capacities; it cannot discover virtual-memory permissions. SHA constants must
be the canonical frozen table. Input/output byte buffers need no alignment
except the decoder's 512-byte output descriptor (8-aligned).

Preflight failures leave output, work and stack entirely untouched. Decoder
header truncation/limit errors additionally read at most the four header bytes.
After processing begins, all owned workspace and stack are wiped, including
nested-call returns, padding, staged outputs, and temporary secrets. The
handshake key-schedule result intentionally contains the requested intermediate
secrets; callers own their lifecycle and must wipe them after use.

## Key schedule ABI

`Asm.Tls.Schedule.derive mode`: a0 points to ten LE64 words:
`A, lenA, B, lenB, output, outputCapacity, workspace, workspaceCapacity,
sha256Table, transcriptLimit` (80 bytes).

Workspace is 1536 bytes and 8-aligned; table is 512 bytes and 8-aligned. Stack
reservation is 528 bytes. Hash/messageHash touch and wipe 304 bytes; other modes
use and wipe all 528. All successful modes wipe the entire 1536-byte workspace.

| Mode | A | B | Output |
| --- | --- | --- | --- |
| handshake | 32-byte ECDHE shared secret | Hash(CH...SH), 32 bytes | 224 bytes below |
| application | master secret, 32 | Hash(CH...server Finished), 32 | client app32, server app32 |
| finished | sender handshake traffic secret, 32 | Hash before this Finished, 32 | Finished key32, verify_data32 |
| hash | whole transcript bytes | zero length | SHA256 digest32 |
| messageHash | whole first ClientHello bytes | zero length | `fe 00 00 20` then Hash(CH1) |

Handshake output is seven consecutive 32-byte values: early secret,
early-derived secret, handshake secret, client handshake traffic secret, server
handshake traffic secret, handshake-derived secret, master secret. Absent PSK
is 32 zero octets. The two `derived` calls use Hash(empty), traffic calls use the
specified transcript digest, and `finished` uses an empty label context before
HMAC over the transcript digest. Application secrets include **server Finished**.
Client Finished includes server Finished and client Certificate/CertificateVerify.

Every transcript includes the handshake's four-byte headers, never record
headers. For HRR replace CH1 with messageHash(CH1), then append HRR, CH2, SH, ...
and call hash on those bounded caller-owned bytes. The API does not guess which
messages are in a digest and does not retain a hidden incremental transcript.

## Decoder ABI and view

`Asm.Tls.Codec.decode`: a0 points to eight LE64 words:
`input, availableBytes, output, outputCapacity, workspace, workspaceCapacity,
maximumBodyBytes, libp2pProfile` (64 bytes). Profile must be 0 or 1. Body length
always uses all 24 protocol bits; maximumBodyBytes is caller-configured.

Output is 512 bytes (64 LE64 words), workspace 16896 bytes, stack 240 bytes.
Workspace comprises the staged view and two complete 65536-bit duplicate maps.
No arbitrary maximum number of extensions, shares, signatures, or certificates
is imposed. Certificate entries and their extensions are all checked before the
strict profile enforces one certificate. A complete outer message with an inner
overrun is malformed (2), not need-more (1). Concatenated input returns only the
first message and its consumed length; repeatedly advance by consumed length.
For split messages retain bytes and call again; never assume one read is one
message. All offsets below are relative to the supplied input's first byte.

| Word(s) | Value |
| --- | --- |
| 0..3 | handshake type, consumed bytes, HRR flag, obligations |
| 4..7 | legacy version, selected/offered-1301 suite, compression, CV scheme |
| 8..11 | ticket lifetime, age_add, certificate count, share count |
| 12/13 | random offset/length |
| 14/15 | session ID |
| 16/17 | offered cipher suites (payload, excluding length prefix) |
| 18/19 | compression methods payload |
| 20/21 | complete extensions payload |
| 22/23 | supported versions payload |
| 24/25 | supported groups payload |
| 26/27 | key_share extension data (including its inner vector header) |
| 28/29, 30/31 | signature_algorithms, signature_algorithms_cert payloads |
| 32/33 | ALPN extension data (including inner vector header) |
| 34/35 | opaque QUIC TP extension data |
| 36/37 | cookie payload |
| 38/39 | request context |
| 40/41 | certificate-list payload |
| 42/43, 44/45 | first certificate bytes, its extensions payload |
| 46/47, 48/49 | CV signature, Finished verify_data |
| 50/51, 52/53 | ticket nonce, opaque ticket |
| 54/55 | selected group (SH/HRR), received ClientHello SNI flag |
| 56/57, 58/59 | X25519 share bytes, P256 uncompressed share bytes |
| 60 | signature mask: 0403=1, 0804=2, 0401=4, 0807=8 |
| 61..63 | group mask (X25519=1/P256=2), offers0304 flag, count of libp2p ALPN names |

Absent slices have offset=length=0; present empty extension data still has a
nonzero offset. `Spec.Tls.View.offer` and `.selection` provide typed views.
Structural mode (profile=0) supports RFC8448's generic TLS traces. It still
checks 0303 legacy fields, compression zero, session length <=32, SH suite1301,
exact known share lengths/P256 04 prefix, duplicate IDs, inner widths, SH0304,
valid CV schemes, and 32-byte Finished. Strict mode additionally requires
usable offers, ALPN libp2p, QUIC TP, and one certificate/empty full-handshake
request contexts. An empty ClientHello key_share vector is structurally legal
TLS (HRR); strict profile requires the extension to be present and groups to be nonempty. Point validity and
all-zero ECDH rejection are outside this codec.

## Encoders and QUIC admission

`Asm.Tls.Encode.encode`: nine LE64 descriptor words:
`body, bodyBytes, handshakeType, output, outputCapacity, workspace,
workspaceCapacity, maximumBodyBytes, libp2pProfile` (72 bytes).
Output is bodyBytes+4; workspace is `align8(bodyBytes+4)+17472`, 8-aligned;
stack reservation 352. The actual decoder validates the staged raw body/header,
then SNI emission is rejected and the full frame is committed atomically.
The workspace holds the entire staged frame, view, decoder scratch, descriptor;
every byte is wiped. Raw-body encoding is paired with the vector helper below.
Typed independent Spec constructors cover every supported message and HRR.

`Asm.Tls.Encode.vector`: seven LE64 descriptor words:
`input, bytes, width, minimumBytes, output, outputCapacity, callerLimit`
(56 bytes). Width is 1, 2, or 3. Output is width+bytes; no workspace or stack.
It checks the full width, minimum, caller limit, capacity and separation before
writing either prefix or payload. Compose nested vectors into separate caller
buffers, then call the checked body encoder.

`Asm.Tls.Codec.admitQuic`: a0=isRecord, a1=handshakeType. No memory/stack access.
Nonzero isRecord or type24 yields unsupported (3); otherwise success (0).

## Work bounds and proofs

Every variable-length loop has a checked byte or item bound: at most uint24+4
frame bytes; uint16 extension bytes and floor(bytes/4) headers; uint16 key-share
bytes and floor(bytes/5) entries; uint24 certificate bytes and floor(bytes/6)
entries; ALPN floor(bytes/2) names; uint16 offers floor(bytes/2) words. Each loop
consumes a positive minimum, except bounded copy/wipe loops which decrement a
checked counter. Duplicate maps have fixed protocol-sized bounds.

`Spec.Tls.Bounds` gives explicit conservative admission estimates:
`decode = 2000000 + 200000*frameBytes`,
`encode = decode(body+4) + 100*(workspace+body+1)`,
`vector = 1000 + 16*bytes`,
`transcript = 2000000 + 100000*(bytes/64+2)`.
These include per-certificate bitmap resets and are checked against measured
instruction counts. They are engineering bounds, **not universally proved
instruction-count bounds**. Main must admit each operation against its quantum
before entry; these synchronous leaves do not yield mid-call. Admission must
also check the estimate fits a 64-bit word, especially for long transcripts.
Byte limits and memory capacities are enforced by the RV64 entries.

Kernel proofs cover successful cursor slice bounds, remaining length,
nonwrap/disjoint-layout arithmetic, uint8/16/24 encoding roundtrips, vector
length bounds, bitmap address/index uniqueness, workspace alignment/limits,
fixed schedule labels/context construction, hash/synthetic-message sizes,
QUIC rejection rules, symbolic execution of actual cursor/header fragments, and the real status/register-wipe
prefix with saved-register and memory preservation.
They do not establish full leaf/composition refinement, a TLS FSM,
authentication, fetch/resource safety, cryptographic security, or universal CT.

## Reproduction

Requires Lean 4.33.0, Python3 with cryptography, Go 1.24.1 (test module has no
external module dependencies), riscv64-unknown-elf-{as,ld,objcopy}, and RV64
Linux-user QEMU. QEMU paths are the GNU object and directly encoded-byte object;
this does not mean qemu-system. Both execute identical checked typed bytes.

```sh
python3 Tests/Tls/go_oracle.py
python3 Tests/Tls/check.py --traces
python3 Tests/Tls/check.py --only decode --extended --label final-decode
python3 Tests/Tls/check.py --only encode --label final-encode
python3 Tests/Tls/check.py --only decode --match edge- --label edge-decode
python3 Tests/Tls/check.py --only encode --match edge- --label edge-encode
lake build Tests.Tls.ProofAudit
python3 Tests/Tls/audit.py
python3 Tests/Tls/test_audit.py
```

The audit always checks generated artifacts and kernel axioms. Worktree source
ownership is a separate optional check: pass `--frozen-baseline manifest.json`
only with a manifest for the current worktree. No implicit `/tmp` inventory from
another parallel worker is consulted; an explicitly missing/mismatched inventory
fails instead of being silently skipped.

Set `QEMU_RISCV64`/`--qemu` and `--prefix` for local tool locations. The Go oracle
uses `go` on PATH (or `TLS_TEST_GO`), selects `GOTOOLCHAIN=go1.24.1` and
asserts that version. Go may download this pinned toolchain if absent. It creates
self-signed test certificates and records ephemeral test RNG reads in ignored
artifacts to independently recover ECDHE using Python cryptography; no such
keys or runtime are used in production. Both Go peers require mutual auth and
exchange fragmented QUIC TLS data, with X25519 and HRR-to-P256 variants. It
checks all four emitted handshake/application secret events and both Finished.

RFC8448 sections 3, 5, and 6 are **TLS handshake/key-schedule vectors**, not QUIC
packet vectors. Their extracted bytes and intermediate values are in
`rfc8448.json`; attribution/license is `LICENSES/Tls-RFC.txt`. Python hashlib/hmac
independently checks all intermediates and transcript boundaries. Tests compare
independent complete register/memory snapshots, guards, staged-output failure
atomicity, wipes, every-instruction footprints, GNU bytes, and both QEMU paths.
Secret-pair diagnostics compare exact branch/access traces but are finite tests.
Native Lean model/Specs are built through Lake under `Tests/Tls/.build`; there is
no manual dependency walker. `--extended` additionally tests every distinct
truncated prefix of the published and Go endpoint messages.

## Verification results

The original worker snapshot in `results.json` records7448 cases,59 exact trace
pairs and15014 QEMU executions. The integrated rerun with the pinned Go1.24.1
oracle records **7482 cases,59 trace pairs and15082 QEMU executions** in
`Tests/Tls/.build/audit.json`. Every-prefix counts depend on the generated Go
messages. Supplemental boundary cases deliberately overlap some main fixtures.
All36 public helper/fragment theorems passed the kernel and axiom audit; only
propext, Classical.choice and Quot.sound occur (some claims require no axioms).
The worker-only frozen dependency inventory is not an assertion about unrelated
subsequent main-worktree changes. Generated artifacts remain under ignored
`.build/`; the artifact audit checks their encoded code, native/model snapshots
and exact suite counts.
