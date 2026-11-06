# Crypto reference specifications and tests

These are independent, executable, pure Lean reference specifications for later
RV64/SAsm refinement. They are **not** production cryptography, an ASM implementation,
an ASM correspondence proof, or completion of M2/M2a. Specifications import only Std
and each other. They do not invoke external crypto, FFI, processes, or IO.

## Public API

All names below are under `Libp2pAsm.Spec.Crypto`. `Bytes` abbreviates `List UInt8`.
Every byte API returns `Except Error Bytes`, with errors represented as data.

| Function | Arguments | Behavior |
| --- | --- | --- |
| `SHA256.hash` | `message : Bytes` | 32-byte SHA-256 digest |
| `SHA512.hash` | `message : Bytes` | 64-byte SHA-512 digest |
| `HMAC.sha256` | `key message : Bytes` | Full 32-byte MAC, including empty/short/block-sized/long keys |
| `HMAC.normalizeKey` | `key : Bytes` | Hash keys longer than 64 bytes, then zero-pad to 64 |
| `HKDF.extract` | `salt : Option Bytes`, `ikm : Bytes` | `none` selects 32 zero salt bytes; `some []` is explicit empty salt |
| `HKDF.expand` | `prk info : Bytes`, `length : Nat` | PRK must contain at least 32 bytes; output length 0 through 8160 |
| `HKDF.derive` | `salt : Option Bytes`, `ikm info : Bytes`, `length : Nat` | Extract followed by expand |
| `SHA256.padding`, `SHA512.padding` | `byteLength : Nat` | Padding suffix only: marker, zeros, big-endian bit length |

`SHA256.State` is `Sha2.State 32`, and `SHA512.State` is `Sha2.State 64`.
Each state has eight named `BitVec` fields `a` through `h`. `SHA256.Block` and
`SHA512.Block` are fixed `Vector UInt8 64` and `Vector UInt8 128`, respectively.
Both modules expose `initial`, `roundConstants`, `blockWords`, `schedule`, `round`,
and `compress`. Compression includes feed-forward; `round` does not.
`Sha2.State.toBytes` serializes the state in big-endian word order.

SHA-256 rejects byte lengths at or above `2^61`; SHA-512 rejects lengths at or
above `2^125`, using the full 128-bit length field. Length arithmetic is in `Nat`,
so length fields never silently wrap. `HMAC.sha256` propagates SHA-256 length
errors, including the inner 64-byte prefix. HKDF checks output length before
converting the block counter to a byte. For a valid PRK, expand with length zero
returns `[]`; a PRK shorter than 32 bytes is rejected even when length is zero.

Errors are `messageTooLong`, `invalidBlockLength`, `outputTooLong`, and
`prkTooShort`. `invalidBlockLength` protects the shared block consumer against
incomplete input; the hash APIs construct complete blocks by padding.

## Running tests

Use the repository's pinned Lean 4.33.0 toolchain. No lakefile or root test runner
change is needed for these standalone test-only targets:

```sh
lake build Tests/Crypto/Main.lean
lake env lean --run Tests/Crypto/Main.lean
```

For integration, import `Tests.Crypto` and call `Libp2pAsm.Tests.Crypto.run`.
The standalone entry point lets assertion exceptions escape. A deliberately
incorrect expected digest was checked to produce exit status 1.

The optional independent Python standard-library comparison is isolated from
both the specification and the official-vector runner:

```sh
lake build Tests/Crypto/Differential.lean
python3 Tests/Crypto/differential.py
```

## Evidence and provenance

- **SHA:** 22 published vectors: NIST empty/one-byte/boundary/LongMsg records
  plus the NIST `abc` and two-block examples for each algorithm. Boundary inputs
  cover SHA-256 lengths 54/55/56/57/63/64 and SHA-512 lengths
  110/111/112/113/127/128 bytes. LongMsg inputs are 163 and 227 bytes.
- **HMAC:** all seven RFC 4231 SHA-256 cases, plus the NIST 64-byte-key example.
  Case 5 asserts the published 16-byte prefix while checking full output length.
  Zero-padding equivalence and normalization lengths are tested separately.
- **HKDF:** RFC 5869 A.1-A.3 PRK and OKM values. Expand consumes the published PRK
  independently of extract; end-to-end derive is also tested. Tests cover absent,
  empty and explicit zero salt, short PRKs, zero output, block transitions,
  8160-byte output, and rejection of oversized requests.
- **Length boundaries:** padding suffixes are checked at `2^61-1`, `2^125-1`,
  and rejection thresholds without allocating those messages. The SHA-512 high
  length word is checked at `2^61` bytes. Incomplete compression blocks are rejected.
- **Supplemental comparison:** 709 deterministic cases against Python
  `hashlib`/`hmac`: 532 SHA cases, 120 HMAC cases, 50 HKDF expand cases, and
  7 extract cases. Five expand cases compare all 8160 bytes, including counter 255.

The implementation directly transcribes the equations and constants in
[FIPS 180-4 (August 2015)](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf),
[RFC 2104 section 2](https://www.rfc-editor.org/rfc/rfc2104.html#section-2), and
[RFC 5869 sections 2.2-2.3](https://www.rfc-editor.org/rfc/rfc5869.html#section-2).
No third-party implementation code was adapted. The existing
[fips-180-4-lean project](https://github.com/remix7531/fips-180-4-lean) was considered;
its Mathlib/Lean 4.29 dependencies and GPL license were not imported into this
Std-only Lean 4.33 specification.

SHA fixtures are selected from NIST's CAVS 11.0 byte-oriented response files,
generated 2011-03-15. The original archive is linked in the fixture modules.
The four source response files were retrieved from the pyca mirror at commit
`f05ec395898cb8aab11bc583ee3d8014d0914755` and checked against the retrieved current
file contents. Expected digests were copied from published data, never generated
by the Lean specification. NIST worked-example links are in `SHA.lean` and
`HMAC.lean`; RFC test data notices are retained in `LICENSE-RFC.txt`.

## Limits of the evidence

The reference API accepts whole byte lists, not arbitrary bit strings or a
streaming state. It materializes padding and schedules and is not intended to
establish a production resource budget, constant-time behavior, or zeroization.
Theoretical maximum message lengths were checked through padding arithmetic,
not by allocating or hashing such messages. No code-coverage percentage is claimed.

The six main hash/HMAC/HKDF functions were audited with `#print axioms` on Lean
4.33.0; their dependencies are only Lean core `propext` and `Quot.sound`.
There are no custom axioms, `sorry`, unsafe definitions, or external runtime
hooks in these modules. Executable tests remain test evidence, not a proof of
cryptographic security or equivalence to generated ASM.
