# Curve25519 RV64IM implementation and tests

This directory tests independent integer Specs and real typed RV64IM routines for
X25519, Ed25519 public-key derivation, deterministic signing, and strict verification.
Production callers supply their own secret/seed bytes. There is no random generator,
fixed private key, FFI, crypto syscall, external C/F* invocation, or runtime Spec call.
All tests and generated artifacts belong to this worktree; root exports/configuration
and the existing SHA/HMAC/HKDF/Link sources are unchanged after the label fix.

## Entry points and ownership

`Asm.Crypto.Curve25519.X25519.{raw,sharedSecret,publicKey}`,
`Ed25519.{publicKey,sign}`, and `Verify.verify` return `Except String SAsm.Stmt`.
Generation rejects invalid call relocation/branch bounds; runtime returns a0=status.
All other caller-saved registers are cleared. ra, sp, gp, tp and s0..s11 are preserved.
The output never aliases an input or owned scratch/stack; overlapping read-only
inputs are allowed. Runtime checks enforce output/work/stack disjointness, aligned
work/sp, capacities and nonwrapping accessed ranges. Mapping, access permissions
and separation from the executable code remain caller preconditions.

| Operation | a0..a7, in order | Workspace | Owned stack |
| --- | --- | ---: | ---: |
| X public key | secret,32,out,outCapacity,work,workCapacity | 896 | 272 |
| X raw/shared | secret,32,peer,32,out,outCapacity,work,workCapacity | 896 | 272 |
| Ed public key | seed,32,out,outCapacity,work,workCapacity | 4160 | 384 |
| Ed sign | seed,32,message,messageLen,out,outCapacity,work,workCapacity | messageLen+4160 | 384 |
| Ed verify | key,32,message,messageLen,signature,64,work,workCapacity | messageLen+4160 | 384 |

Key/shared outputs are 32 bytes; signatures are 64 bytes; verification has no
output buffer. Inputs and outputs permit byte alignment. Work is 8-aligned and
entry sp is 16-aligned. Capacity suffixes and all input bytes are untouched. Empty
messages are legal and their pointers are never dereferenced. Ed message lengths
must satisfy `messageLen < 2^64-4160`, exactly to keep the required workspace size
representable; there is no separate small message limit. The backing memory must
exist. This ABI cannot represent inputs requiring more than the address space.

Public metadata errors precede all memory reads and writes. Successful calls wipe
the exact required workspace and used stack. X shared-secret rejection uses 160
stack bytes and wipes all 896 workspace bytes, with no secret input read. Ed content
rejections wipe all required workspace and 384 stack bytes. Ed setup also initializes
the lower 272 stack bytes before nested calls so content failures have a uniform
owned frame. Output is committed only after the operation succeeds. Memory traps
from violated mapping/permission preconditions do not constitute cleaned-up returns.

| Status | Meaning |
| ---: | --- |
| 0 | success |
| 1 | Ed workspace length arithmetic overflow |
| 4 | wrapping range, alignment or forbidden overlap |
| 5 | insufficient output/work capacity |
| 8 | wrong secret/key/peer/signature length |
| 9 | TLS X25519 all-zero shared-secret peer |
| 10 | Ed noncanonical scalar/point or invalid point |
| 11 | Ed identity, small-order or mixed-order A/R |
| 12 | Ed signature equation failed |

## Algorithms and workspace

`Spec/Crypto/Curve25519` uses unbounded `Nat` modular arithmetic modulo
`p=2^255-19` and `l=2^252+27742317777372353535851937790883648493`. It has no machine
registers, limb memory layout or assembly imports. Extended Edwards coordinates
avoid an inversion per group addition; encoding and recovery use modular powers.

`Field.lean` uses five canonical 51-bit limbs. Its 25-product cyclic convolution
folds terms of degree >=5 with 19. MUL/MULHU and SLTU explicitly maintain 128-bit
accumulators, carry propagation and borrow masks. Each column is below
`95*2^102+2^58 < 2^109`; carries are below `2^58`, and the final 19-fold fits a
64-bit word. Three carry passes and a masked conditional subtraction canonicalize
each operation. Multiplication's 48-byte temporary frame is actually wiped.
Inputs to private limb operations must meet their documented canonical contracts.

`Scalar.lean` uses four 64-bit limbs, binary modular reduction (256/512 steps),
and fixed 256-step masked double-and-add for `(k*a+r) mod l`. `Point.lean` uses
complete extended-coordinate addition, a 256-step scalar loop, and masked swaps.
The generic modular power performs both square and multiply at every one of 256
bits. This favors simple bounded control flow over optimized addition chains or
precomputed windows. No secret-indexed tables, branches or memory addresses exist
in keygen/sign/X scalar processing. These are instruction-model observations,
not microarchitectural timing or universal noninterference proofs.

X workspace: pruned scalar [0,32), reserved [32,64), u and ladder field values
[64,704), power scratch [704,784), exponent [784,816), padding [816,824), a24
[824,864), padding [864,896). It masks bit 255 of u and reduces noncanonical
encodings, as RFC 7748 requires. Raw X25519 returns zero for low-order input.
TLS `sharedSecret` checks the public peer by three projective doubles before
reading the secret. The projective infinity test rejects the low-order subgroup
on the curve and twist, which gives all-zero clamped X25519 results. The general
algebraic equivalence of this public test and the Spec's zero-result test is a
remaining proof obligation; published low-order vectors exercise both.

Ed workspace: SHA-512 constants [0,640), existing whole-message SHA scratch
[640,1600), expanded seed [1600,1664), reduced a/r/k [1664,1760), encoded A
[1760,1792), staged R/S [1792,1856), digest [1856,1920), base/P/Q points
[1920,2400), point/power scratch [2400,3080), decoding scratch [3080,3592),
subgroup-order bytes [3600,3632), group-check result [3680,3840), padding to 4096,
then checked message concatenation [4096,4160+messageLen). Constants are written
as numeric standard values. Every SHA operation calls the frozen
`Asm.Crypto.Whole.body .sha512` through the existing typed `Link` module.

## Strict verification policy

This is pure Ed25519, not Ed25519ctx/ph. Key and R must have canonical y<p, valid
square roots, and no sign bit on zero x. S must be <l, without reduction-based
acceptance. Both A and R must be nonidentity members of the prime-order subgroup:
`[l]A=[l]R=identity`. Verification then checks the uncofactored equation
`[S]B=R+[H(R||A||M)]A`. All decoder/verification branches depend only on public
key/signature/message bytes. This deliberately rejects cofactored-equation-only
signatures, small-order points and mixed-order points. It is a documented strict
acceptance policy for integration; it is not a claim that all libp2p libraries
or every TLS implementation has identical acceptance behavior.

## Pinned provenance and licenses

`provenance.json` records exact Git commits, Git blob IDs and source SHA-256 hashes.
The inspected HACL* portable C files are pinned at
[f557259007db9933442dde10aa995c1b00bd3446](https://github.com/hacl-star/hacl-star/tree/f557259007db9933442dde10aa995c1b00bd3446/dist/portable-gcc-compatible):
`internal/Hacl_Bignum25519_51.h`, `Hacl_Curve25519_51.c`, and `Hacl_Ed25519.c`.
Their cyclic multiplication/carry scheme, Montgomery formulas and complete Edwards
addition informed this RV64 port. The port canonicalizes more frequently, uses 2p
subtraction bias for canonical inputs instead of HACL's loose-limb 8p bias, uses
fixed generic powers, and uses binary scalar reduction instead of HACL's scalar
implementation. HACL* verification does not transfer automatically to this port.
The MIT attribution is retained in `LICENSES/Curve25519-HACL-star.txt`. Upstream
source snapshots used during inspection live only under ignored build artifacts.

Normative equations, pruning, encoding and published vectors are from immutable
[RFC 7748](https://www.rfc-editor.org/rfc/rfc7748.txt) and
[RFC 8032](https://www.rfc-editor.org/rfc/rfc8032.txt); their code-component notice
is in `LICENSES/Curve25519-RFC.txt`. Selected Wycheproof vectors are pinned to
[5722833ca004983abd1a91bcb6c24596d50ac0f9](https://github.com/C2SP/wycheproof/tree/5722833ca004983abd1a91bcb6c24596d50ac0f9/testvectors_v1).
`wycheproof-selected.json` retains original fields and IDs, with a SHA-256 content
pin. Cases: X25519 1/2/72/73, Ed25519 1/10/63/85/151. The Apache-2.0 notice is in
`LICENSES/Curve25519-Wycheproof.txt`. This is a selected subset, not the full corpus.
The independent test oracle is `cryptography==49.0.0` (`requirements.txt`), using
its OpenSSL implementation. Pseudorandom test fixtures have fixed test-only seeds.

## Reproduce checks

Run from the repository root with Lake, Python plus the pinned test dependency,
GNU `riscv64-unknown-elf-*`, and QEMU available:

```sh
python3 Tests/Curve25519/check.py --jobs 3
python3 Tests/Curve25519/adversarial.py
python3 Tests/Curve25519/iterate.py
python3 Tests/Curve25519/audit_results.py
```

QEMU defaults to PATH `qemu-riscv64`, with `QEMU_RISCV64` or `--qemu` overrides.
GNU prefix can be set using `--prefix`. `--only` selects an operation; `--limit`
is a diagnostic subset, not the full suite. The runner generates a separate Lake
package exclusively under ignored `build/curve25519/native/`, with `srcDir` pointing
at this repository and native artifacts under `build/curve25519/lake/`. Lake owns
the import graph and compilation. This needs no root configuration/export edits.
Root `.lake/build/` is also used for the proof and small field-unit checks.

Every API fixture compares independent Spec output (or semantic rejection),
actual lowered `Instr` execution, an independently constructed Python snapshot,
GNU assembler bytes, GNU/QEMU, and raw-encoded/QEMU. Snapshots include all 32
registers, complete mapped regions, output guards, read-only inputs, exact owned
workspace/stack wipes, and untouched capacity suffixes. Finite paired traces compare
PC, access kind, width and address while varying secret bytes with the same public
inputs. They also enforce exact accessed payload bounds. Verification has no secret
input; its metadata-error trace pairs repeat identical public inputs.

Vectors include RFC key pairs and DH agreement, the first two RFC ladder recurrence
steps, noncanonical u, low-order curve/twist peers, SHA message boundaries through
4097 bytes, canonicality, negative zero, S+l, identity, torsion, mixed-order points,
wrong messages, and resource/range/alignment/overlap rejections. `iterate.py` checks
the RFC 1000-iteration result with independent Spec, cryptography and both QEMU
paths plus output/work/stack guards. The 1000-step recurrence is not repeated in
the lowered interpreter; only its first two steps are tested there. No million-step
claim is made. Machine-readable per-operation results and code hashes are written
to `build/curve25519/*verification.json`.

The completed suite has 151 main API cases and 45 additional ABI/point rejection
cases: 196 independent Spec/lowered-execution/snapshot comparisons, 113 finite
trace pairs, and 392 QEMU executions. The separate 1000-iteration test adds two
QEMU executions. The field unit probe checks 135 operand/operation combinations;
the arithmetic proof audit checks 15 lemmas. Every check passed. The final artifact
audit regenerates all fixtures, compares their exact input/expected snapshots with
the executed fixtures, checks model pass records, and reconciles both native
snapshots and GNU/encoded instruction bytes. This reconciliation is useful when
operations were run separately; it does not replace rerunning affected execution
tests after production changes.

| Operation | Main cases | Additional cases | Trace pairs | Typed instructions |
| --- | ---: | ---: | ---: | ---: |
| X public key | 15 | 7 | 17 | 2498 |
| X raw | 33 | 8 | 21 | 2593 |
| X shared secret | 33 | 8 | 29 | 2968 |
| Ed public key | 12 | 7 | 15 | 7249 |
| Ed sign | 21 | 8 | 18 | 7541 |
| Ed verify | 37 | 7 | 13 | 8574 |

## Formal boundary

Fifteen kernel-checked universal arithmetic lemmas cover radix/word splitting,
carry preservation, reduction congruence, one-subtraction canonicalization, product
and carry bounds, subtraction bias, scalar-step/addition bounds, pruning and
workspace arithmetic. `ProofAudit.lean` checks their axioms against only Lean's
standard propext/Classical.choice/Quot.sound. No sorry, native_decide, unsafe
implementation, new axiom or placeholder is used.

Still unproved: complete field/normalizer/scalar instruction refinement; maintained
limb bounds for all reachable states; projective group/ladder correctness; point
recovery/subgroup policy refinement; whole X25519/Ed25519 and inherited SHA-512
refinement; arbitrary-memory resource, nonwrapping, error-atomicity, preservation,
termination and zeroization theorems; and universal relational constant-time proofs.
The current tests are finite functional and trace evidence, not these theorems or
cryptographic-security proofs. Main owns integration, final completion and review.
