# X.509 certificate structure

`Asm.Identity.X509.certificate` parses a single libp2p-profile v3 certificate
using ordinary RV64IM instructions. It is **not authentication**: self-signature,
host-key signature, curve/key validity, expected Peer ID, current-time validity,
TLS CertificateVerify and Finished must be checked by the authentication/FSM
layers. No host ASN.1 or crypto function is called.

## Reproduce

Lean4.33.0, Python3 with `requirements.txt`, GNU RISC-V binutils and Linux-user
QEMU are required. Executables resolve through PATH; `QEMU_RISCV64`,
`RISCV_PREFIX`, `--qemu`, and `--prefix` override tool locations.

```sh
python3 -m pip install -r Tests/Certificate/requirements.txt
python3 Tests/Certificate/check.py --help
python3 Tests/Certificate/check.py
lake exe libp2p-asm-codegen asm x509-parse
```

The independent Python parser and datetime checks, pure Lean specification and
every fetched RV64 instruction agree on1067 fixtures. All32 registers and every
mapped byte are compared, including output sentinels, immutable inputs,
workspace/stack wipes and guards. Each memory access is checked against its
owned span. GNU-produced bytes equal directly encoded bytes; both paths pass
2134 QEMU executions. Maximum observed execution is158997 instructions.
The model records6732 distinct executed instruction positions out of7916
(85.04% of this linked parser image, including its helpers). This is instruction
coverage, not Lean source/branch coverage or a repository-wide percentage.
These are finite tests, not full refinement, resource, relocation or CT proofs.

Fixtures include real test-only certificates independently signed by
cryptography49.0.0 with Ed25519, P-256, RSA-PKCS1/SHA256 and RSA-PSS/SHA256,
plus clearly synthetic **structural** certificates whose signatures need not
verify. Tests cover every base-certificate prefix and single-byte mutation,
known algorithms, signed time boundaries, malformed/minimal INTEGER and OID,
UTF8/Numeric/Printable/IA5/BMP/Universal strings, DER SET OF ordering, duplicate
and unknown critical extensions, KU/EKU/basic constraints, aliases, alignment,
capacity, u64 length/pointer limits and operation-budget exhaustion.
Artifacts and the Lake-managed native probe are under ignored `build/certificate/`.

## Raw internal ABI

a0 points to64 immutable bytes: eight little-endian u64 words:

| Word | Meaning |
| --- | --- |
| 0,1 | certificate input base, available length |
| 2,3 | output base, capacity (at least168) |
| 4,5 | workspace base, capacity (at least512+4*inputLength) |
| 6 | caller certificate byte limit, nonzero |
| 7 | public parser-operation budget, nonzero |

Input length must be less than2^61 before workspace multiplication. Descriptor
and workspace are8-aligned; output/input may be unaligned. Exactly144 bytes
below16-aligned sp are owned. The admitted input,168-byte output, used workspace,
descriptor and stack spans must be pairwise disjoint and last-byte nonwrapping.
Only used prefixes, not excess declared capacity, are accessed. Empty input
need not be mapped and may have any pointer.

The caller must actually map readable input/descriptor and writable
output/work/stack, keep executable code separate and maintain the input loan
until return. Numeric checks cannot establish mapping, permission or lifetime.
No untrusted wire integer may be supplied as a raw pointer.

a0 returns status; all other caller-saved registers are zero. ra, sp, gp, tp and
s0..s11 are preserved. Preflight failures do not write memory. Every processed
exit wipes the entire used workspace and all144 stack bytes. Only success
publishes output; failures leave all output bytes unchanged.

| Status | Meaning |
| --- | --- |
| 0 | structure parsed; not an authentication decision |
| 1 | truncated DER input |
| 2 | input length outside the arithmetic domain |
| 4 | numeric range, alignment, overlap or stack violation |
| 5 | output/work capacity insufficient |
| 6 | malformed supported ASN.1/value structure |
| 8 | unsupported/mismatched signature or subject-key algorithm |
| 9 | duplicate extension OID, including unknown OIDs |
| 10 | unrecognized critical extension |
| 11 | missing libp2p signed-key extension |
| 12 | configured byte/operation limit exceeded |

Output is21 LE64 words:

| Words | Meaning |
| --- | --- |
| 0–1 | full raw TBS view |
| 2–3 | full raw SubjectPublicKeyInfo view |
| 4 | subject key kind: Ed25519=1, P-256=2, RSA=3 |
| 5–6 | BIT STRING key bytes, excluding unused-bits byte |
| 7–8,9–10 | unsigned RSA modulus/exponent views (zero pairs for other keys) |
| 11 | certificate signature kind: Ed25519=1, ECDSA/SHA256=2, PKCS1/SHA256=3, PSS/SHA256=4 |
| 12–13 | certificate signature bytes, excluding unused-bits byte |
| 14,15 | signed two's-complement64-bit NotBefore/NotAfter seconds |
| 16–17,18–19 | libp2p host public-key protobuf / host signature views |
| 20 | KU/EKU mask: server=1, client=2; absent KU/EKU permits both |

Views are source-relative `(offset,length)`, never pointers or copied data.
They expire with the source loan. Unknown noncritical extension values remain
opaque. Low-tag definite/minimal DER headers and supported typed fields are
checked; no generic recursive ASN.1 validator or DNS/PKI chain verifier is claimed.
Deprecated unique IDs and extra certificate/TBS/SPKI fields are rejected.

## Work and bounds

Private work[0,168) stages output;[168,480) holds parser context;[480,488)
holds the root frame pointer;[512,512+4*n) stores prior OID views.
Each table insertion checks its bound; generation-free OID comparisons use
only already parsed source views. Private helpers have at most two16-byte
frames. Their terminal errors jump through a position-independent code address
kept in s0 to one root cleanup, avoiding out-of-range conditional branches.

Every node parse, algorithm/time dispatch, OID/string unit and duplicate/sort
comparison consumes a public operation credit. Wipes are bounded by input
length, independently of credits. The current conservative **engineering**
admission ceiling is `20000+50*n+5000*budget` instructions, checked in fixtures
but not yet universally proved. Callers must admit an adequate finite charge
before executing; do not equate a byte cap with an instruction quantum.
No secret values are present in this structural parser.
