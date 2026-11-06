# QUIC v1 packet cryptography on RV64IM

Production entry points are checked typed `SAsm.Stmt` programs under
`Libp2pAsm/Asm/Crypto/Quic/`. Composition uses frozen SHA-256/HMAC/HKDF,
AES-128 and GCM machine instructions and position-independent `Link` calls.
There is no runtime Spec call, FFI, native crypto fallback or custom opcode.
Independent references live under `Spec/Crypto/Quic/`.

## Common contract

Each entry receives **a0 = immutable descriptor pointer** and returns
**a0 = status**. Descriptors contain the LE64 slots listed below, in order.
All other caller-saved registers are cleared. ra, sp, gp, tp and s0..s11 are
preserved. No output length or pointer is returned in a register.

Descriptors, workspace and SHA tables require 8-byte alignment; sp requires
16-byte alignment. Input and output byte buffers can be unaligned. Runtime
checks reject wrapping accessed spans and all pairwise overlaps between
descriptor, inputs, output, required workspace, SHA table and owned stack.
Only actually accessed prefixes participate; capacity suffixes are untouched.
Empty inputs are not dereferenced and may have arbitrary pointer values.

Mapped/readable/writable memory and separation from executable code remain caller
preconditions; entry/return instruction addresses must be valid and 4-aligned.
Output must also be readable for the masked packet commit. These
checks cannot inspect page tables. A violated mapping contract is a machine trap,
with no status/cleanup guarantee. Descriptors and inputs must remain immutable
during execution. All secret material comes from callers. The Initial salt and
Retry key/nonce are public RFC constants.

Metadata failures leave **all memory** untouched. Processed calls wipe exactly
the required workspace prefix and owned stack interval, on success and failure.
The packet routines explicitly wipe even unused parts of their owned nested
stack area. Capacity suffixes, input keys, input packets and output guards remain
unchanged. No allocation or hidden packet-size limit exists.

Common statuses: 0 success, 1 invalid length/configured limit, 2 packet number,
3 header metadata, 4 range/alignment/overlap, 5 capacity, 6 authentication,
7 insufficient header-protection sample. Lower-level statuses do not leak through
valid composed contracts except GCM's identical authentication status 6.

## Key derivation

`Quic.Kdf.derive .initial`, `.keys`, `.update` use a 56-byte descriptor:

`input, inputLength, output, outputCapacity, work, workCapacity, SHA256Table`

The caller supplies the standard 64 SHA-256 round constants in 512 LE64 bytes,
as required by the frozen hash ABI. Workspace is **1280 bytes**; owned stack is
**528 bytes** including the nested HKDF ninth-argument slot and callees.

| Mode | Input | Output layout |
| --- | --- | --- |
| initial | DCID of length 0..20 | initial secret32, client secret32, server secret32, client keys44, server keys44 |
| keys | exactly 32-byte SHA-256 TLS traffic secret | AES key16, IV12, HP key16 |
| update | exactly 32-byte current traffic secret | next secret32, next AES key16, next IV12 |

Initial uses RFC 9001 v1 salt and `client in`/`server in`. Labels have the exact
TLS `tls13 ` prefix and empty context. Packet derivation uses `quic key`,
`quic iv`, `quic hp`; update uses `quic ku` and **never derives or emits a new HP
key**. Retain the connection's existing HP key when packing updated keys44.
Minimum Initial-packet CID validation belongs to the packet parser, not this
crypto primitive. Validation order is descriptor, input length, output capacity,
workspace capacity, alignment, then range/disjointness; no key is read first.

## Packet number helpers

`Quic.nonce`: 32-byte descriptor `IV, fullPN, output, outputCapacity`.
Outputs 12 bytes: IV XOR zero-left-padded **64-bit big-endian** PN.
Rejects PN ≥ 2^62 before any IV read. No workspace or stack is used.

`Quic.reconstruct`: 40-byte descriptor
`expectedPN, truncatedPN, PNByteCount, output, outputCapacity`.
Outputs an 8-byte LE64 full PN, or status 2. Count is 1..4; truncated PN must fit.
`expectedPN = largestReceived+1`, with 0 for an empty space and **2^62 allowed**
at exhaustion. The RFC 9000 A.3 tie rules are exact. Candidates ≥ 2^62 are
rejected, never wrapped. In particular exhaustion can still accept reordered
old packets. No workspace or stack is used; capacity/range validation precedes
the final candidate-domain check. Packet-space and replay state are caller-owned.

## Protect and unprotect

`Quic.Packet.protect` / `.unprotect`: 88-byte descriptor:

`keys44, input, inputLength, pnOffset, number, output, outputCapacity,`
`work, workCapacity, configuredPacketLimit, headerLength`

For protect, input is unprotected header || plaintext; `number` is the full PN.
The explicit headerLength must equal pnOffset + the first-byte PN length and
must not exceed inputLength. The routine writes the full PN's low bytes into
its staged header, replacing the supplied PN bytes. Output is the protected
packet of **inputLength+16 bytes**.

For unprotect, input is the protected packet; `number` is expectedPN and
headerLength must be 0. The routine recovers PN length, reconstructs the full PN,
authenticates and outputs:

`LE64 fullPN || LE64 headerLength || unprotected header || plaintext`

This output always occupies **inputLength bytes**. Failed opens preserve every
output byte, including both metadata fields. Unprotected header and plaintext
are held in caller workspace; a masked commit publishes them only on tag success.
GCM compares every tag byte before decrypting, then the outer commit reads/writes
the same output addresses for good and bad tags. A failed reconstructed PN also
wipes the complete owned workspace/stack and leaves output untouched.

The HP sample is always `[pnOffset+4, pnOffset+20)`, including for 1/2/3-byte PNs.
Its existence is checked before any key/sample read. The first-byte mask is
0x0f for long headers and 0x1f for short headers. Checked v1 Initial, Handshake
and short-header layouts are supported. Complete version/type parsing, reserved
bits, CID lengths, QUIC Length field, packet spaces, replay and key-phase policy
remain the caller's responsibility; authentication does not validate those policies.

The configured packet limit applies to inputLength and must be ≤ 2^36−32,
the frozen GCM message bound. No smaller limit is hardcoded. Workspace is
**1616+inputLength bytes**, owned stack **240 bytes**. Layout: nonce `[0,12)`,
GCM descriptor `[16,112)`, AES schedule `[112,288)`, HP mask `[288,293)`,
GCM scratch `[320,1600)`, packet staging `[1600,1616+inputLength)`.
After GCM, open stages metadata in `[1584,1600)` of the already-wiped scratch.
The 96-byte GCM descriptor uses actual key, nonce, AAD, input, output, workspace
pointers and lengths in the frozen ABI's exact order; no stage overlaps a
callee's currently active scratch or input.

Validation order: descriptor, number domain, configured/input length, PN offset,
sample, output/work capacity, workspace alignment and disjoint spans, then header
metadata. Frame acquisition and secret reads occur only after those checks.

## Retry

`Quic.Retry.generate` / `.check`: 72-byte descriptor:

`ODCID, ODCIDLength, retry, retryLength, output, outputCapacity,`
`work, workCapacity, configuredPacketLimit`

Generate consumes Retry **without** tag and emits a 16-byte tag. Check consumes
Retry **with** tag and returns status only; it never dereferences output.
ODCID length is 0..20. Pseudo-packet AAD is its single-byte length, then ODCID,
then Retry-without-tag. AES-GCM uses RFC 9001's fixed public key and nonce and
empty plaintext. All 16 tag bytes are compared with XOR/OR and arithmetic;
there is no data-dependent early exit. Caller parses the actual Retry header.

Workspace is **1441+ODCIDLength+RetryWithoutTagLength**; stack is **240 bytes**.
Layout: key `[0,16)`, nonce `[16,28)`, tag `[32,48)`, GCM descriptor `[48,144)`,
GCM scratch `[160,1440)`, pseudo-packet `[1440,required)`.
Configured limit applies to supplied retryLength and must be ≤ 2^61−22 to leave
room for the maximum ODCID prefix under GCM's AAD bound. Validation checks CID,
configured/input length, short check input, output capacity (generate only),
workspace capacity, alignment and spans, before copying any payload.

## Reproduce

Use the pinned Lean/Lake toolchain, Python with `cryptography==49.0.0`, GNU
`riscv64-unknown-elf-{as,ld,objcopy}`, and RV64 Linux-user QEMU. No download,
cron execution or root Lake configuration modification is performed.

```sh
python3 Tests/QuicCrypto/check.py
python3 Tests/QuicCrypto/check.py --extra
lake --no-cache build +Tests.QuicCrypto.ProofAudit:olean
lake env lean Tests/QuicCrypto/ProofAudit.lean
python3 Tests/QuicCrypto/audit_results.py
```

Set `QEMU_RISCV64` or `--qemu /path/to/qemu-riscv64` as needed; `--only` selects
one operation. `--limit` is a diagnostic subset, not the complete suite.
The native test-only Lake package and all ELFs/snapshots/logs stay in ignored
`build/quic/`. Native compilation accelerates the independent Lean interpreter
and Spec; the emitted production instructions still contain all cryptography.

Tests independently reconcile RFC A.1 secrets/keys/labels, both complete A.2/A.3
Initial packets, their sample/mask bytes and A.4 Retry with Python
hashlib/hmac/cryptography. Model and both QEMU paths compare entire register/memory
snapshots against Spec and independently generated Python expectations. Tests
include wrong tags/headers/sample offsets, 1..4-byte PNs, high 62-bit nonces,
reordered/exhausted numbers, minimum samples, larger packets, configured/GCM
metadata bounds, overlapping/wrapping spans, capacities, guards and exact wipes.
GNU assembler bytes must equal typed `encodeProgram` bytes before either QEMU run.
The extra suite exercises updated packet keys with retained original HP keys.

The completed suite has **541 base/extra cases, 228 trace pairs, 1538 QEMU
executions**, plus separate RFC intermediate-observation reruns. Those reruns
read actual HP mask stores and ciphertext samples from the RV64 model before
wiping, for both directions and both protect/unprotect. Detailed code hashes
and per-case step counts are emitted in `verification.json`,
`extra-verification.json` and each operation's `measurements.json`.

Equal-public trace pairs compare PC and all access addresses/kinds/widths and
check the access footprint. Packet-open pairs retain HP, protected header and
thus decoded PN length while changing the packet key/IV; successful and failed
GCM authentication take identical traces. Retry pairs change ODCID/tag. These
finite diagnostics do not prove universal constant time. Changing HP can change
the decoded PN length, which controls loops and GCM AAD length, so equal entry
packet lengths alone do not ensure equal traces across different HP keys.

## Proof boundary and sources

`Refinement/Crypto/Quic/Helpers.lean` has 24 theorems proving byte-array and word
nonce injectivity across the entire accepted PN domain, 64/96-bit BE round trips,
integer/modular arithmetic, capacity and PN boundary claims, plus a
symbolic two-instruction nonce fragment and its occurrence in the actual leaf.
`ProofAudit.lean` lists theorem axioms; only Lean's standard
propext/Classical.choice/Quot.sound are permitted. There is no `sorry`,
`native_decide`, `unsafe`, new axiom or placeholder.

**Still unproved:** complete byte-memory instruction refinement for nonce/PN,
SHA/HKDF/AES/GCM and packet/Retry composition; fetch/encoding/local-call semantic
composition; universal ownership/memory safety and zeroization; all-length
termination/resource bounds; whole-program relational constant time. Tests are
evidence, not substitutes for these proofs. Hardware timing, speculation, power
leakage, nonce-reuse policy and cryptographic security are outside this model.
The probe's fuel formula is a public-length testing budget, not a universal bound.

- [RFC 9001 §§5/6, Appendix A](https://www.rfc-editor.org/rfc/rfc9001.txt)
- [RFC 9000 Appendix A.3](https://www.rfc-editor.org/rfc/rfc9000.txt)
- [RFC 8446 §7.1](https://www.rfc-editor.org/rfc/rfc8446.html#section-7.1)
- RFC code components/vectors: `LICENSES/Quic-RFC.txt`; frozen AES circuit's
  upstream license is supplied by the main-owned AES/GCM dependency.

Root exports, final transport parser/state, integration and final review are
main-owned. Existing frozen files are not changed by this suite.
