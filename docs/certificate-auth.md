---
title: Internal certificate authentication and issuance
last_updated: 2026-11-07
tags:
  - certificate-authentication
  - libp2p
  - tls
  - rv64
---

# Internal certificate authentication and issuance

These routines execute the frozen ASN.1, public-key, time, hash and signature
implementations as RV64 instructions. There is no host authentication Boolean,
preverified certificate input, external ASN.1/crypto runtime, or trust callback.
The pure Spec composes independent mathematical crypto implementations.

`Asm.Identity.Certificate.authenticate` authenticates exactly one raw v3 DER
certificate. It checks the parsed usage mask for the remote role, exact inclusive
nanosecond validity, self-signature over the exact received TBS, the identity
extension signature over the 21-byte `libp2p-tls-handshake:` prefix and exact raw
DER SPKI, and canonical inline Peer ID. Ed25519 or secp256k1 host identities are
supported independently of Ed25519, P-256 or rsaEncryption certificate subjects.
Certificate signatures support Ed25519, ECDSA/P-256/SHA256, RSA-PKCS1/SHA256 and
RSA-PSS/SHA256. PSS parameter grammar is enforced by the frozen X509 algorithm
parser. Unsupported critical extensions and duplicate extensions are rejected
there. No ASN.1 result is treated as cryptographic evidence.

Authentication returns an **internal** identity record. The caller must keep the
certificate immutable while using its subject-key views. Application publication
still requires the caller's complete TLS Finished/authentication gate.

## Calling convention and mapped ownership

All descriptor fields are LE64, including signed seconds/nanoseconds represented
as two's-complement words. Descriptors and work are 8-aligned; initial SP is
16-aligned. Every descriptor and accessed input, output, work and stack span must
have a valid, live mapping with the required permissions and be separated from
executable code. Inputs must remain immutable for the whole operation, including
continuations. Numeric nonwrap/alignment/disjointness checks **do not establish
mapping, lifetime or permissions**. An unmapped span violates the calling
contract; a machine fault is not an ordinary authenticated error return.

Preflight rejects invalid lengths/capacities/wrap/alignment/aliasing before writes.
The supplied spans are pairwise disjoint, including descriptor and reserved stack.
Issuance checks the entire advertised DER output capacity for disjointness; other
outputs check their exact fixed extents. Unaligned byte inputs/outputs are allowed.
Once work is owned, every ordinary success/error return wipes all required work
and the complete 1552-byte reserved stack extent. Preflight errors leave work and
stack unchanged. Output sentinels remain unchanged on every error.

All callee-saved registers, RA, SP, GP and TP are preserved. Caller-saved registers
are cleared except status in a0 and, for issuance only, successful DER length in
a1. Errors clear a1. Inputs are never wiped by these routines: callers own their
lifetime and must wipe source entropy/secrets when no longer needed.

## Incoming authentication descriptor

The descriptor occupies 192 bytes. Role 1 means the remote server, role 2 the
remote client. A dialer must supply a nonempty expected Peer ID for role 1; a
listener can use an empty expectation for role 2. A supplied expectation is
always compared to the authenticated canonical Peer ID, never to the received
protobuf encoding. Unknown/reordered/repeated/nonminimal protobuf fields follow
the frozen protobuf decoder; Peer ID construction re-encodes the parsed key.

| Offset | Field |
| --- | --- |
| 0 / 8 | Raw DER pointer / length |
| 16 | Certificate count, exactly 1 |
| 24 | Remote role, exactly 1 or 2 |
| 32 | Current UTC nanoseconds, signed64 |
| 40 / 48 | Expected canonical binary Peer ID pointer / length |
| 56 / 64 | Output record pointer / capacity, at least 192 |
| 72 / 80 | Work pointer / capacity |
| 88 | Caller certificate byte budget |
| 96 | Caller instruction reservation budget |
| 104 | Caller host protobuf byte budget |
| 112 / 120 | Caller RSA modulus / exponent byte limits |
| 128 | Caller minimum RSA strength in bits, frozen RSA requires at least 2048 |
| 136 | Caller available stack capacity, at least 1552 |
| 144–191 | Unused by authentication |

Required work is `8192 + 16*rawLength`. Raw length must be below `2^56` to
establish nonwrapping workspace arithmetic before any narrowing or access. This
is an arithmetic domain, not a replacement certificate resource policy. Actual
certificate/host/RSA byte and operation budgets must be supplied from `Limits`.
There are no new local policy defaults. The existing RSA ABI's arithmetic domain
and caller limits are preserved unchanged.

The frozen parser takes a separate internal 64-byte descriptor and produces
168 staged bytes (21 words): TBS offset/length at 0/8, SPKI 16/24, subject kind
32, subject bytes 40/48, modulus 56/64, exponent 72/80, signature kind 88,
signature 96/104, NotBefore/NotAfter seconds 112/120, host protobuf 128/136,
host signature 144/152, role usage mask 160. Those structural views stay inside
owned work until authentication completes.

The successful external 192-byte internal identity record is zero padded:

| Offset | Field |
| --- | --- |
| 0 / 8 / 16 | Host kind / raw host key length / canonical Peer ID length |
| 24 | Certificate subject kind: Ed=1, P256=2, RSA=3 |
| 32 / 40 | Verified subject-key offset / length in retained certificate |
| 48 / 56 | Verified RSA modulus offset / length, zero for non-RSA |
| 64 / 72 | Verified RSA exponent offset / length, zero for non-RSA |
| 80 / 88 | Retained certificate length / self-signature kind |
| 96–135 | Raw authenticated host key, 32/33 bytes then zeros |
| 136–175 | Canonical binary Peer ID, 38/39 bytes then zeros |
| 176–191 | Zeros |

## CertificateVerify

`verifyCV` uses the incoming descriptor's certificate, role, work, budgets and
stack fields. Additional fields are transcript SHA256 pointer/length at144/152,
signature pointer/length at160/168 and TLS SignatureScheme at176. Expected peer
and output fields are unused. It reparses the raw certificate, binds the scheme
to its actual subject key, and verifies the signature over exactly 130 bytes:
64 spaces, the 33-byte role context, a zero separator, and the 32-byte transcript
digest. Only Ed25519 `0807`, P-256/SHA256 `0403` and rsa_pss_rsae_sha256 `0804`
are accepted. A PKCS1-signed RSA certificate can use PSS CertificateVerify;
PKCS1 CertificateVerify and PSS-restricted subject OIDs are not accepted.

`signCV` uses seed pointer/length at0/8, role24, signature output56/cap64,
work72/cap80, instruction budget96, stack capacity136 and transcript144/152.
Seed and transcript lengths must both be32; output is64 bytes. Required work is
8704 bytes (`8192+16*32`), stack1552. Other fields are unused. It signs using the
actual frozen Ed25519 routine. The caller supplies the owned ephemeral seed
returned by issuance, not the persistent host private key.

These are possession checks/signing helpers. They do not advance a handshake,
choose transcript checkpoints, validate ALPN, verify Finished or publish peers.

## Issuance

`Asm.Identity.Certificate.Issue.issue` uses a distinct 192-byte descriptor:

| Offset | Field |
| --- | --- |
| 0 / 8 / 16 | Persistent host secret pointer / length32 / host kind1 or2 |
| 32 / 40 | NotBefore / NotAfter signed64 Unix seconds |
| 48 / 56 | Fresh per-connection entropy pointer / length32 |
| 64 / 72 | Real DER output pointer / capacity |
| 80 / 88 | Owned ephemeral seed output pointer / capacity at least32 |
| 96 / 104 | Work pointer / capacity at least16384 |
| 112 / 120 | Caller instruction budget / stack capacity at least1552 |
| 128 / 136 | Canonical Peer ID record pointer / capacity at least48 |

The Peer ID record is an LE64 length followed by40 bytes, padded with zeros.
Success returns the DER length in a1. DER, seed and Peer ID outputs commit only
after all checks, including the final exact DER capacity check. There is no
partially published certificate or seed on error.

Both times are encoded with actual `Time.encode`; order is checked before key
operations. The certificate contains v3, serial1, issuer/subject CN `libp2p`, an
ephemeral Ed25519 SPKI, a critical libp2p signed-key extension, critical digital
signature KeyUsage and both server/client EKUs. Fixed construction buffer extents
follow from these bounded representations; caller capacity and budget remain
explicit. Minimal DER headers use the frozen `Codec.Der.encodeHeader`.

The caller obtains entropy through a completion-reserved host entropy request.
Freshness, cryptographic entropy and per-connection nonreuse are ownership/source
obligations; no predicate over arbitrary32 bytes can establish them. There is no
fixed production seed, random fallback, persistent TLS key or internal RNG. All
32-byte values are valid Ed25519 seed encodings, including all-zero values; that
does not attest their entropy. The caller must wipe the returned secret and its
source entropy at handshake completion or abort.

## Public validation and declassification

ASN.1, protobuf, lengths, roles, timestamps, algorithms, public points, received
signatures and transcript digests are public. Verification may branch/address on
them. Signing reuses the frozen fixed-iteration secret arithmetic, mask selection
and fixed-access DER encoder. There are no new branches or memory indices based
on legal secret scalar/seed bytes. Derived public keys, completed signatures and
their DER lengths become public before certificate assembly; ASN.1 construction
may branch on those explicitly declassified values. Status is also public.

Frozen secp256k1 signing uses the documented one-candidate RFC6979 policy. Invalid
secret scalars, rejected nonce candidates or zero signature scalars propagate a
signing error with no output. There is no retry, reduction, biased nonce or other
fallback. Strict Ed25519 verification rejects noncanonical/non-prime-subgroup
points and scalars; ECDSA parsing enforces canonical DER but allows high-S for
libp2p interoperability. No whole-operation or microarchitectural CT proof is
claimed by this composition.

## Resource reservations and continuation

Caller instruction budgets are debited using conservative, public estimates;
all debit multiplication/remaining-budget arithmetic is checked. Parsing reserves
`1000000 + 4096*n + 128*n*n`, also covering outer setup/cleanup. Host protobuf
decoding reserves `100000 + 1024*protobufLength`. Ed verification reserves
`16000000 + 1024*messageLength`; EC verification reserves32000000 plus hash cost
`100000 + 1024*messageLength`. RSA uses the frozen `RSA.workBound` plus hash cost.
CV signing reserves14000000. Ed-host issuance reserves37000000; K256-host
issuance reserves51000000. These estimates are not universal cost proofs.

The core quantum remains `2^24`. Auth Ed/Ed measured22,765,419 instructions;
Ed-host issuance measured17,608,356. A single K256 verification and large RSA
operation can also exceed a quantum. Main must preserve PC, all machine registers,
owned work/stack and input immutability across cooperative continuation; it must
not truncate accepted algorithms or increase the quantum to hide this requirement.
There is no resumable host-trust shortcut. Runtime scheduling and cancellation
ownership remain main's scope. The test interpreter executes actual fetches and
records per-case instruction counts, including full routines beyond one quantum.

## Verification and provenance

`Tests/CertificateAuth/build.py` creates an ignored isolated Lake package under
`build/certificate-auth/`; root exports, Lake files and frozen sources remain
unchanged. `check.py --matrix --native --qemu PATH` runs the independent
cryptography49/OpenSSL oracle, pure Lean Spec, full fetched RV64 memory/register
snapshots, per-access footprints, GNU encoder equality and both native QEMU paths.
`live.py --qemu PATH` issues real certificates in ASM and exchanges real TLS1.3
handshakes with Go libp2p. The ASM endpoint's `crypto.Signer` and certificate
callback run the actual model and both native paths. Captured counterpart CV
messages/signatures are independently checked by ASM. Go owns this test transport;
it is not an implementation of the main-owned ASM TLS state machine.

`Tests.CertificateAuth.ProofAudit` automatically checks transitive axioms of the
new certificate lemmas against the standard Lean logical axioms. Theorems cover
CV role separation/transcript injectivity, scheme binding, canonical Peer ID,
exact validity boundaries, DER grammar and an actual usage-mask instruction leaf.
Whole-ASM crypto/composition refinement, full memory/termination/resource bounds,
entropy provenance and relational CT remain unproved. Tests are finite evidence.

Inspected references: go-libp2p v0.51.0 (`03349944847387886bf06b65993b2a03c1e6d12d`),
MIT; rust-libp2p-tls0.7.0 (Cargo checksum
`01dc85ad2bbc3506502f430a00dd913ec87f31e1894291cb9b923168babb6485`), MIT.
Exact source SHA256 values and retained notices are in
`Tests/CertificateAuth/provenance.json` and `LICENSES/CertificateAuth.txt`.
External crypto/x509/libp2p dependencies occur only in tests.

Protocol references: [libp2p TLS r0](https://github.com/libp2p/specs/blob/master/tls/tls.md),
[RFC8446 §4.4.3](https://www.rfc-editor.org/rfc/rfc8446.html#section-4.4.3),
[RFC5280](https://www.rfc-editor.org/rfc/rfc5280.html),
[RFC8017](https://www.rfc-editor.org/rfc/rfc8017.html) and
[RFC4055](https://www.rfc-editor.org/rfc/rfc4055.html).
