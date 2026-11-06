# RSA public verification on typed RV64IM

This directory owns RSA only. Shared SHA, HMAC, Link, Util, AES, GCM and
Weierstrass files are imported without modification. No RSA key generation,
private signing, decryption or libp2p RSA host identity support is provided.
Local TLS private keys remain Ed25519/P256. Certificate DER, key OIDs, chain
validation and TLS handshake context selection belong to the integrating caller.

The saved final audit passed **241 case executions**, **482 QEMU executions**
(GNU assembly and typed bytes), and **24 kernel-checked helper lemmas**. These
are execution counts, including deliberate repeated cases, not distinct vectors.
`build/rsa/result.json` records each case, actual key size, measured instructions,
estimator, snapshot hash and implementation hashes. Proof limits are below.

## Public API and profile

`Asm.Crypto.RSA.rsaPkcs1Sha256` and `rsaPssRsaeSha256` produce checked typed
`Rv64.SAsm.Stmt` programs. Lower and encode them through the existing RV64 pipeline.
The only runtime cryptography is ordinary RV64IM instructions: variable-length
big integers, Montgomery exponentiation, SHA256 and MGF1. No runtime Spec call,
FFI, host primitive, external crypto or success stub is present.

The PKCS1 entry verifies certificate signatures only; TLS 1.3 CertificateVerify
must use PSS. For PSS the caller must enforce the rsaEncryption certificate-key
OID appropriate to `rsa_pss_rsae_sha256`. The entry receives the already computed
32-byte SHA256 digest. For CertificateVerify this is the hash of the RFC 8446
context-prefixed signature input, not merely the transcript hash.

Mathematical input validation requires minimal unsigned BE `n,e`, odd `n >= 5`,
odd `3 <= e < n`. Primality/factorization is not checked for a public key.
TLS policy additionally requires at least 2048 significant modulus bits; the
caller can raise this threshold. A weak, otherwise well-formed key returns 6.
Passing a configured minimum below 2048 is a configuration/resource error (5).
This minimum is a local TLS profile policy, not a claim that RFC 8017 forbids
all smaller mathematical RSA moduli.

`signature.length` must equal the modulus byte length and `OS2IP(signature)<n`.
Oversized signature integers are rejected, never reduced modulo n. `e` is
processed in full, with no fixed 65537 assumption or truncation to a machine word.
2048/3072/4096-bit and non-byte-aligned moduli follow the same dynamic code.

PKCS1 accepts exactly `00 01 FF...FF 00` followed by the minimal 19-byte SHA256
DigestInfo prefix (including NULL parameters) and the 32-byte digest. Padding
contains at least eight FF bytes. BER, omitted NULL, searching for a digest,
trailing data and alternative encodings are not accepted.

PSS uses `emBits=modBits-1`, `emLen=ceil(emBits/8)`, SHA256, MGF1-SHA256 with
BE32 counters, salt length 32 and trailer BC. If `emLen=k-1`, the extra leading
recovered byte must be zero. Nonzero unused high bits, any PS/delimiter/trailer
error, other salt lengths, or any H mismatch fail verification.

## Raw ABI

Standard RV64 entry: `a0` points to this **128-byte, eight-aligned** descriptor.
All fields are unsigned little-endian 64-bit values. There is no output buffer.

| Offset | Field |
| --- | --- |
| 0, 8 | modulus pointer, byte length k |
| 16, 24 | exponent pointer, byte length E |
| 32, 40 | signature pointer, byte length |
| 48, 56 | digest pointer, byte length (exactly 32) |
| 64, 72 | scratch pointer, capacity in bytes |
| 80 | immutable SHA256 table pointer (512 bytes) |
| 88 | configured maximum modulus byte length |
| 96 | configured maximum exponent byte length |
| 104 | configured minimum significant modulus bits (>=2048) |
| 112 | maximum permitted instruction estimator value |
| 120 | available stack capacity below entry sp, bytes |

The SHA table contains the standard 64 SHA256 round constants in order, each
zero-extended into an LE64 slot. Correct constants are a caller precondition;
the routine checks its range/alignment, not its values. Inputs may be unaligned.
Scratch and table must be eight-aligned; entry `sp` must be sixteen-aligned.

The caller must map the descriptor and each accepted input/table range readable,
and the exact scratch/stack extents readable+writable. They must stay stable
throughout execution, without concurrent mutation. Mapping, read/execute code,
valid return PC and exclusion of code from writable regions are preconditions.
The routine cannot establish OS mapping permissions by checking integer pointers.

Preflight validates metadata, length/configuration limits, estimator, capacities,
pointer nonwrapping ranges and alignment before any large input access or write.
The descriptor itself must be mapped before its fields can be inspected. Only
accepted extents, not excess declared capacities, are checked/accessed. A range
ending exactly at 2^64 is allowed. A zero key length is rejected before access.

Preflight also checks scratch/stack disjointness from each other, descriptor,
all inputs and table. Read-only input ranges may overlap each other. No input,
descriptor, table, code or bytes outside the exact scratch/stack extents are
written. Invalid mappings or concurrent mutation violate the ABI; traps then
carry no cleanup guarantee.

## Workspace, stack and status

Let `L=ceil(k/4)` and `B=8L`. The required scratch is **56L+896 bytes** exactly;
`Asm.Crypto.RSA.workspaceBytes` computes it using unbounded generation-time Nat.
Each radix-2^32 limb occupies one zero-extended eight-byte slot, least significant
limb first. All buffers use caller storage; no heap or variable stack allocation.

| Scratch offset | Size | Use |
| --- | --- | --- |
| 0 | B | modulus |
| B | B | signature base, later recovered BE encoded message |
| 2B | B | exponentiation accumulator |
| 3B | B | R squared, later integer one |
| 4B | 2B | full product/Montgomery reduction |
| 6B | B | subtraction temporary |
| 7B | 704 | SHA256 workspace |
| 7B+704 | 72 | PSS hash input: zero prefix/digest/salt |
| 7B+776 | 36 | MGF1 seed and BE32 counter |
| 7B+812 | 4 | padding |
| 7B+816 | 32 | SHA256 output |
| 7B+848 | 8 | significant modulus bit length |
| 7B+856 | 8 | negative Montgomery inverse |
| 7B+864 | 8 | public exponent bit mask |
| 7B+872 | 24 | reserved, initialized and wiped |

The required stack is **288 bytes** below entry sp: root save frame 112 plus
maximum child SHA stack 176 (or Montgomery/doubling frame 112). Scratch is
initialized before use. Scratch and the entire 288-byte reservation are wiped on every content return,
including malformed key, weak policy, bad signature and success. All capacity
bytes beyond these exact extents remain unchanged. Early metadata/preflight
returns perform no writes to scratch or stack.

Return `a0` is the sole result; there is no returned key material or recovered EM.
`ra,sp,gp,tp,s0..s11` are restored exactly. `a1..a7,t0..t6` are zeroed on every
normal return. The return address is never treated as a scratch temporary.

| a0 | Meaning |
| --- | --- |
| 0 | valid signature |
| 1 | malformed public key (encoding, range, parity or exponent) |
| 2 | malformed/invalid signature, including length, representative and EMSA |
| 3 | digest length is not 32 |
| 4 | pointer range, alignment or overlap error |
| 5 | capacity, size/configuration limit or operation budget failure |
| 6 | mathematically well-formed key below configured TLS strength |

Validation order is descriptor/stack metadata, lengths and configured limits,
resource estimator, memory extents/overlaps, key contents, policy, signature
representative, exponentiation, then EMSA. The first failure wins. The API does
not promise to diagnose every later invalid field after an earlier error.

The inline `decode/encode/lessBE/normalize` builders and Montgomery/doubling
leaves are internal composition helpers, not checked public interfaces.
Montgomery's `a0..a7` are out, a, b, n, L, negative low-limb inverse, product,
subtraction temporary. Doubling's `a0..a3` are x, n, L, subtraction temporary.
Require 1<=L<=16384, aligned zero-extended slots, odd 1<n<2^(32L), canonical
a,b,x<n, correct inverse, valid mappings and disjoint operands/scratch/stack.
Montgomery out may equal a or b exactly; partial overlap is forbidden. a and b
may be identical for squaring. Doubling changes x in place. Each leaf uses and
wipes 112 stack bytes, restores the preserved registers, clears caller temps,
returns a0=0 and leaves its arithmetic scratch for the enclosing root to wipe.
Inline helpers have no independent return/cleanup contract; they execute only
inside an owned root context. Violating their preconditions is outside the ABI.

## Public timing and resource estimate

All RSA inputs, key/exponent contents and metadata, digests, signatures, validation
results and branch decisions are **public**. Exponentiation is intentionally
variable-time; it performs one square per exponent bit and a multiply on set
bits. EMSA and key checks may return early. This is not a secret-input constant
time implementation, and must never be used for RSA private exponents.

`workBound(k,E)` is a conservative deterministic executed-instruction estimator:

```text
64*(L+1)^2*(16*E+4) + 4096*L^2
  + 50000*(ceil(k/32)+2) + 1000*k + 100000
```

The raw routine calculates this exact expression before reading key/signature
contents and returns 5 if it exceeds the supplied budget. Both actual lengths
have an arithmetic ceiling of 65536 bytes in addition to caller limits, ensuring
all estimator/workspace calculations fit 64 bits. This ceiling is an explicit
resource policy, not silent input truncation. Integration should set much tighter
modulus/exponent limits and budgets suitable for its workload. The estimator is
an instruction count, not elapsed time or a hardware cycle estimate.

## Provenance

- Independent Nat/EMSA specs: [RFC 8017](https://www.rfc-editor.org/rfc/rfc8017)
  §§4,5.2.2,9.1.2,9.2,B.2.1 and [RFC 8446](https://www.rfc-editor.org/rfc/rfc8446)
  §4.2.3. RFC code-component notice: `LICENSES/rfc-rsa.txt`.
- Arithmetic inspected and pinned to HACL* commit
  `f557259007db9933442dde10aa995c1b00bd3446`,
  [`dist/portable-gcc-compatible/Hacl_Bignum.c`](https://github.com/hacl-star/hacl-star/blob/f557259007db9933442dde10aa995c1b00bd3446/dist/portable-gcc-compatible/Hacl_Bignum.c)
  and `internal/Hacl_Bignum_Base.h`. Ports its unsigned-32 multiply-add,
  full-product Montgomery cancellation/carry, conditional subtraction and R2
  doubling precomputation. Uses schoolbook multiplication, a bitwise public
  exponent loop and eight-byte zero-extended slots instead of its C representation,
  Karatsuba/window optimizations and allocation. Upstream proofs do not transfer
  to this translation. The source MIT notice is `LICENSES/hacl-rsa.txt`.
- Wycheproof: commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`; selected records
  retain original tcId/comments/flags/result and complete source-file SHA256 in
  `wycheproof-*.json`. Missing-NULL `acceptable` case is explicitly rejected by
  this profile. Apache 2.0 notice: `LICENSES/wycheproof-rsa.txt`.
- NIST CAVS 10.1 SHA256, 2048/3072/4096-bit public records in `nist.json`, from
  the official RSA signature-generation response files, pinned via pyca mirror
  commit `9f119db1beba2834af325cc631b3d787b895943d` and source-file SHA256.
  Its PSS records have zero-length salt and are deliberately rejected by this TLS
  profile. PKCS1 records are accepted. The public exponent is 4097. The mirror's
  BSD and Apache license notices are preserved in `LICENSES/pyca-rsa-*.txt`.
- [RFC 8448](https://www.rfc-editor.org/rfc/rfc8448.txt) section 3 public certificate
  and CertificateVerify vectors are retained in `rfc8448.json`, including the
  transcript messages and source SHA256. cryptography independently verifies
  both signatures. These historical RSA1024 examples are rejected with policy
  status 6 by the public API; the profile is not weakened to accept them.
- `generated-test-keys.json` contains **publicly disclosed TEST-ONLY** RSA private
  numbers generated by cryptography 49.0.0, never production credentials. The
  larger exponent case reuses a generated modulus with a legal 66-bit exponent.
  Odd-size test keys combine backend-generated primes of the needed unequal
  sizes, because backend key generation can round odd requested sizes down.
  Every loaded/generated test key asserts its actual modulus bit length.

## Reproduction and evidence

Install `Tests/RSA/requirements.txt`, Lean from `lean-toolchain`, GNU RV64IM
binutils and QEMU user-mode. Run:

```sh
python3 Tests/RSA/check.py
python3 Tests/RSA/report.py
lake build +Tests.RSA.ProofAudit:olean
lake env lean Tests/RSA/ProofAudit.lean
```

Portable defaults are `qemu-riscv64` and `riscv64-unknown-elf-` on PATH;
override `QEMU_RISCV64` and `RISCV_PREFIX` or CLI options. No home path is embedded
in the scripts. `--group positive|emsa|errors|official|supplement` selects a subgroup;
RFC 8448's weak-key profile cases are in `supplement`. The default runs all ten
scheme/group combinations and produces the directories audited by `report.py`.

The native Lean probe is built by a generated test-only Lake package depending
on this repository. Lake computes the complete native dependency graph and
rebuilds transitive dependencies; there is no manual import/object closure cache.
Tests execute the typed instruction fetch/execute model with per-access ownership
checks, compare the independent Nat spec/Python pow/cryptography oracle, verify
all input bytes and guards, all 32 registers, exact workspace/stack wipes, and
check the estimator against measured instruction counts. GNU assembly bytes must
equal typed encoder bytes. Both GNU-assembled and typed-byte ELF paths are run
through QEMU and must match the complete model/oracle snapshot.
On preflight rejection, the access checker permits descriptor reads only and
forbids all writes. `report.py` rechecks saved model/native snapshots and actual
modulus/exponent sizes before creating `build/rsa/result.json`.

## Proof boundary

Kernel-checked lemmas cover BE integer range/append/length, mathematical key
domain, rejection of unreduced signatures, exact PKCS1 encoding/minimum padding,
PSS EM length and unused-bit arithmetic, dynamic slot/workspace arithmetic,
workspace alignment and estimator nonoverflow under the size ceiling,
32-bit multiply-add width/carry, limb reconstruction, borrow, single subtraction,
Montgomery low-limb cancellation and the Nat modexp output range.

No `sorry`, `native_decide`, `unsafe`, new axiom or placeholder is used. The audit
allows only Lean's standard `propext`, `Quot.sound`, `Classical.choice` dependencies.
These helper proofs do **not** prove the full assembly routines refine Nat RSA,
SHA or EMSA. Whole-function memory/register/cleanup correctness, linked instruction
fetch correspondence, global resource safety, loop termination and the complete
instruction-bound theorem remain open. Runtime checked bounds and differential
executions are evidence, not substitutes for those missing proofs. HACL*'s proof
claims apply to its upstream implementation, not automatically to this RV64 port.
