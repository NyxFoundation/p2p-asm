# X.509 AlgorithmIdentifier recognition

`Asm.Identity.X509.Algorithm.signature` and `.publicKey` take a0=complete
AlgorithmIdentifier DER, a1=length. They return a0=status and a1=kind:

| Entry | Kind1 | Kind2 | Kind3 | Kind4 |
| --- | --- | --- | --- | --- |
| signature | Ed25519 | ECDSA/P256/SHA256 | RSA PKCS1/SHA256 | RSA PSS/SHA256 |
| publicKey | Ed25519 | named-curve P256 | rsaEncryption | — |

Status0=recognized, 4=wrapping span, 8=unsupported or malformed. Failures
clear a1. No signature, curve point, modulus strength or trust is verified.
PSS-restricted public-key OIDs are not accepted as rsaEncryption.
PKCS1 is for certificate signatures, not TLS1.3 CertificateVerify.

Ed25519 and ECDSA signature parameters are absent. P256 SPKI explicitly uses
its named-curve OID. RSA PKCS1 and rsaEncryption accept NULL or absent parameters.
PSS requires SHA256, MGF1-SHA256 and salt32; hash parameters may be NULL or absent.
RFC4055 §3.1 requires recognizing both absent and explicit trailerField1.
SHA1/salt20 defaults, other fields/values, trailing nodes and nonminimal lengths
are rejected. ASN.1 defaults are not silently substituted for this TLS profile.

The pure Spec structurally parses nested ASN.1. The ASM independently compares
the supported finite grammar using real RV64 LBU/XORI/OR instructions. It does
not interpret the Spec or call host ASN.1. All input is public metadata.
No stack or writes; preserved registers and unused caller temporaries follow
the standard leaf ABI. Reads remain inside the supplied range. Byte alignment
is unrestricted. Mapping, lifetime, return/code validity and code separation
are caller preconditions; pointer validation alone does not establish mapping.

```sh
lake exe libp2p-asm-tests
python3 Tests/CertificateAlgorithms/check.py
```

1251 signature and173 public-key cases passed: all supported forms, every
prefix, every single-byte mutation, trailing nodes, seeded noise, unaligned
input and wrapping spans. Python OID/ASN.1 generation, structural Lean Spec,
actual instruction execution, GNU bytes and both QEMU paths agree. Complete
snapshots and read-only footprints are checked. The5000-instruction probe fuel
is not a universal refinement/resource theorem.

Sources: RFC4055 §§3/5, RFC5480 §2.1.1, RFC5758 §3.2, RFC8410 §3.
The surrounding certificate parser and cryptographic authentication remain
separate integration obligations.
