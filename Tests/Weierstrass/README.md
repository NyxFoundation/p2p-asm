# RV64IM Weierstrass cryptography

AES/GCM and shared SHA/HMAC/Link/Util are imported without changing their
contracts. This directory contains Weierstrass-specific tests.

The final integration audit passed 806 saved case executions across 56 routine
runs, 1612 QEMU executions (GNU assembly and typed encoded bytes), 50 exact
control/access trace pairs, and 18 kernel-checked lemmas. These counts include
supplemental validation runs, not 806 distinct vectors. Full model/oracle memory
and register snapshots match, including output guards and working-state wipes.
The machine-readable audit is `build/weierstrass/result.json`; formal limits
are listed separately below.

## Provenance and license

Arithmetic is a four-64-bit-limb RV64 port of HACL* `bn_mul4`,
`mont_reduction`, `bn_add_mod4`, `bn_sub_mod4` and fiat-crypto carry/masked-select
idioms. Montgomery reduction is generalized with `-m^-1 mod 2^64` for the two
field primes and two scalar orders. All four constants are kernel checked.

- HACL*: `f557259007db9933442dde10aa995c1b00bd3446`,
  [`dist/gcc-compatible/Hacl_P256.c`](https://github.com/hacl-star/hacl-star/blob/f557259007db9933442dde10aa995c1b00bd3446/dist/gcc-compatible/Hacl_P256.c),
  [`dist/gcc-compatible/Hacl_K256_ECDSA.c`](https://github.com/hacl-star/hacl-star/blob/f557259007db9933442dde10aa995c1b00bd3446/dist/gcc-compatible/Hacl_K256_ECDSA.c).
  Actual source MIT notice: `LICENSES/hacl-weierstrass.txt`. Point additions port
  the complete homogeneous formulas; the K256 source uses five52-bit limbs,
  translated here into canonical four64-bit Montgomery fields. Its weak
  normalization operations are unnecessary because every field result here is
  canonical. This translation does not inherit the upstream verification proofs.
- fiat-crypto: `1e721c6f18c43b90922e7bc57fd64848e5cff2be`,
  [`fiat-c/src/p256_64.c`](https://github.com/mit-plv/fiat-crypto/blob/1e721c6f18c43b90922e7bc57fd64848e5cff2be/fiat-c/src/p256_64.c).
  Actual MIT license and author list: `LICENSES/fiat-crypto-weierstrass*.txt`.
- Parameters: [Standards for Efficient Cryptography 2 (SEC2), v2](https://www.secg.org/sec2-v2.pdf),
  sections2.4.1 and2.4.2. Point encodings are SEC1 compressed/uncompressed.
- Nonce construction and published P256 vectors:
  [RFC6979 sections3.2 andA.2.5](https://www.rfc-editor.org/rfc/rfc6979).
- Independent negative corpus: C2SP/Wycheproof
  `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`. Selected records retain tcId,
  comment, flags and upstream full-file SHA256 in `wycheproof-*.json`.
  Actual Apache2.0 license: `LICENSES/wycheproof-weierstrass.txt`.
- NIST CAVS11.0 ECDH primitive tests, P256 EC/SHA256 COUNT2 and4, retained in
  `nist-ecdh.json`. [Official CAVP source](https://csrc.nist.gov/Projects/Cryptographic-Algorithm-Validation-Program/Key-Management),
  immutable [pyca mirror](https://github.com/pyca/cryptography/blob/9f119db1beba2834af325cc631b3d787b895943d/vectors/cryptography_vectors/asymmetric/ECDH/KASValidityTest_ECCStaticUnified_NOKC_ZZOnly_init.fax).

## Arithmetic milestone

`Limbs.lean` implements actual MUL/MULHU, carry/borrow, full512-bit product,
four Montgomery cancellation rounds and branchless conditional subtraction.
Canonical inputs are mandatory private-leaf preconditions. `Field.lean` adds
fixed public-exponent inversion. Private arithmetic accepts zero; inversion
maps zero to zero. Public key/scalar APIs enforce their separate domain.
Each operation preserves all s-registers, ra, sp, gp, tp and clears caller-saved
temporaries. A limb leaf owns/wipes112 stack bytes. Inversion owns/wipes352 bytes
including its leaf. Aliasing is supported for aligned internal limb operands.
External BE encoding/decoding uses byte loads/stores and permits unaligned data.

Run `python3 Tests/Weierstrass/check.py --kinds mul add sub qmul qadd qsub inv qinv`.
This milestone passed208 cases,416 QEMU executions and24 exact trace comparisons.
The entire memory/register snapshot is compared with an independent Python
integer oracle, including guard bytes and exact stack/workspace wipes. GNU
assembled and Lean-encoded instruction bytes match for every routine.

`Refinement/Crypto/Weierstrass/Primitives.lean` proves carry bounds/reconstruction,
wide multiply-add bounds/splitting, single-subtraction reduction, mask selection,
encoding lengths, generator curve membership and all four Montgomery inverses.
The11 lemmas use only the standard Lean axioms propext/Quot.sound; the concrete
parameter lemmas use no axioms. No sorry, new axioms, native_decide or unsafe code.

## Formal boundary

The independent natural-number affine specifications are not runtime fallbacks.
Runtime contains only typed RV64IM instructions and linked typed local calls.
Host compilation and cryptography49.0.0 are test machinery only.

The following remain separate formal proof gaps:

1. Full arithmetic, projective point, RFC6979 and ECDSA function refinement to the
   independent specs, including composition of local calls.
2. Instruction-fetch/encoding correspondence for these full linked programs.
3. Arbitrary-memory representation, nonwrapping addresses, frame preservation,
   error atomicity and exact zeroization for every admissible initial state.
4. Universal termination and a proved public-parameter fuel bound.
5. Relational constant-time/noninterference for all equal-public-input executions.
6. Curve primality/cardinality and completeness of the translated projective
   formulas. SEC2 parameters and upstream provenance do not replace these proofs.

Finite tests and primitive lemmas establish none of those full theorems, nor
cryptographic security or microarchitectural timing guarantees.

## Public ABI

`publicKey c`, `ecdh c`, `sign c compact`, and `verify c compact lowS` are in
namespace `Libp2pAsm.Asm.Crypto.Weierstrass`. Import
`Libp2pAsm.Asm.Crypto.Weierstrass.Ecdsa` for all APIs, or `.Keys` for keys/ECDH.
They return `Except String SAsm.Stmt`: linking errors occur during generation.
The RV64 entry uses a0=104-byte descriptor pointer, and returns a0=status.
All other caller-saved registers are zero. All s-registers, ra/sp/gp/tp survive.

| Descriptor byte offset | Value (LE64) |
| --- | --- |
| 0,8 | Secret scalar pointer, length (exactly32) |
| 16,24 | Public peer SEC1 pointer, length |
| 32,40 | SHA256 digest pointer, length (exactly32) |
| 48,56 | Signature pointer, length |
| 64,72 | Output pointer, capacity |
| 80,88 | Workspace pointer, capacity (at least2064) |
| 96 | Immutable SHA256 standard constants,64 LE64 words; signing only |

Unused inputs are not read. Verification ignores secret fields and requires
zero output bytes. Public-key derivation ignores peer/digest/signature/constants.
ECDH ignores digest/signature/constants. Signing ignores peer/signature.
The descriptor, workspace and SHA table must be8-aligned; sp must be16-aligned.
External scalar, peer, digest, signature and output bytes may be unaligned.
All accessed last-byte addresses and stack subtraction are checked for wrap.
The caller must own mapped, mutually disjoint descriptor/input/output/work/stack/
table/code ranges; these mapping/ownership conditions cannot be checked by RV64
without a memory-management interface. Output is readable and writable because
the failure-preserving commit reads its previous bytes. Claimed capacity beyond
the2064-byte owned prefix is untouched. At least1440 stack bytes below sp are
required; each actually used frame is wiped, including padding, before return.

| Operation | Result and required output capacity |
| --- | --- |
| publicKey P256 |65-byte uncompressed SEC1 `04 || x32 || y32` |
| publicKey K256 |33-byte compressed SEC1 `02/03 || x32` |
| ecdh P256 (also K256) |32-byte shared affine x, big endian |
| sign compact=true |64 bytes `r32 || s32`, both big endian |
| sign compact=false |80-byte record: LE64 length, then DER padded with zeros to72 bytes |
| verify | No output; status0 means valid |

For TLS/libp2p, transmit only record bytes `[8,8+length)` from a DER signing
result. The record header and zero padding are an ABI envelope, not DER.
Verification consumes the exact raw DER length, or exactly64 compact bytes.
It rejects all overlong, signed-negative, empty, zero, out-of-range or trailing
encodings. Default verification accepts high-S (ordinary ECDSA compatibility);
`lowS=true` rejects s>n/2. K256 signing always canonicalizes low-S. P256 signing
retains RFC6979's original s. P256 peers must be uncompressed65-byte keyshares;
K256 peers must be compressed33-byte keys. Infinity, noncanonical coordinates,
non-residue compressed x and off-curve points are rejected. Both cofactor-one
groups require no additional subgroup multiplication after finite curve checks.

| Status | Meaning |
| --- | --- |
| 0 | Success |
| 1 | Wrong public input length |
| 4 | Pointer/stack wrap or required alignment violation |
| 5 | Output/work capacity too small |
| 6 | Malformed/out-of-range signature or failed verification |
| 8 | Secret scalar outside1..n-1 |
| 9 | Invalid peer point |
| 10 | RFC6979 candidate outside1..n-1 or zero r/s |

Public metadata validation completes before any private access or write. Public
peer validation completes before ECDH reads the secret. Such early public errors
leave untouched output and, before beginWork, also stack/workspace. All later
paths wipe owned working state. Invalid secret scalars are masked internally to1
and follow the full fixed schedule; the output commit stores previous bytes back
unchanged. This is byte-for-byte error atomicity, not concurrency/transaction
atomicity. No signature, shared secret or public key is partially returned.

## Workspace and secrecy

Root workspace offsets are exact: d[0,32), z[32,64), r[64,96), s[96,128),
k[128,160), k^-1[160,192), three projective points[192,480), field temps[480,544),
ordinary1[544,576), fieldR²[576,608), orderR²[608,640), scalar temps[640,704),
output staging[704,784), padding[784,800), RFC K[800,832), V[832,864),
seed d[864,896), seed z[896,928), HMAC message[928,1025), padding[1025,1088),
HMAC workspace[1088,2049), padding[2049,2064). The entire prefix is wiped.
DER encoding reuses seed storage only after nonce generation. HMAC owns at most
961 bytes here, according to the shared HMAC contract.

Point add's own stack is784 bytes plus112 nested field bytes; scalar multiply
adds432 bytes, so root112+multiply432+add784+field112=1440. Inversion is352;
affine conversion is624; HMAC is288. The maximum stack check covers all paths.
Secret scalars/nonces/points never select branches or memory indices. Scalar
multiplication performs256 complete doubles and256 complete adds, selecting
results with masks. Complete HACL* homogeneous formulas include infinity,
doubling and inverse points. Inversion exponents are public generation constants.
DER signing uses a fixed72x64 scan: signature-dependent widths affect arithmetic
masks only. Public parsing/verification may branch on signature/point bytes;
it is not claimed to hide those public values.

RFC6979 uses actual typed RV64 HMAC-SHA256 with no host/random fallback. The
signer has a one-candidate budget and explicitly returns10 on rejection, rather
than reducing, biasing or reusing a rejected candidate. The same key/digest then
deterministically returns the same error; callers must propagate it. No signature
is emitted. The pure spec additionally defines RFC6979's rejection continuation,
but the runtime deliberately returns this documented error instead of continuing.
Test-only fragments inject nonce0/n/max and r/s=0 into the exact production
validation/status/commit path; the production signer exposes no nonce injection.

## Reproduction

Install the pinned test-only requirement, then run from the repository root:

```sh
python3 Tests/Weierstrass/check.py
```

The runner compiles the Lean model and pure specs with the Lake-selected toolchain
into ignored build artifacts; it does not compile any crypto into the RV64 code.
GNU tools default to `riscv64-unknown-elf-`; override with `--prefix`.
`--qemu` or `QEMU_RISCV64` selects QEMU; the default is `qemu-riscv64` on PATH. Every runtime routine is exported both as typed
instruction bytes and GNU assembly. Both ELF paths must match the same full
model/oracle snapshot. `--kinds` restricts routines; `--curves` restricts curves.
`--artifact-tag` isolates supplemental runs in ignored artifact directories.

For the exact saved integration report, the supplemental runs are:

```sh
python3 Tests/Weierstrass/check.py --kinds public ecdh sign verify --public-errors --artifact-tag=-strict-rejects
python3 Tests/Weierstrass/check.py --kinds verifyzero --artifact-tag=-unaligned
python3 Tests/Weierstrass/check.py --kinds public ecdh --limit 2 --artifact-tag=-trace
python3 Tests/Weierstrass/report.py
```

`report.py` rechecks every saved snapshot and GNU byte comparison and writes
`build/weierstrass/result.json`. `ProofAudit.lean` audits all18 primitive/spec
theorems against standard Lean axioms only. `Encoding.lean` adds universal
SEC1 lengths, compact domain/length, scalar range, low-S domain and accepted-DER
canonical re-encoding lemmas to the11 arithmetic milestone lemmas.
There is no claimed source coverage percentage. Test cases cover success,
public validation, secret domain failures, rare nonce/r/s failures, SEC1/DER
canonicality, ECDSA malleability policy and complete point exceptions.
PC/access comparisons are exact lockstep comparisons with bounded host memory;
they include different valid secret scalars at identical public parameters.
