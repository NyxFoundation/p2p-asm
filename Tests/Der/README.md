# DER TLV header implementation

`Spec/Codec/Der.lean` independently specifies definite, minimally encoded
low-tag-number TLV headers. The corresponding `Asm/Codec/Der.lean` emits only
ordinary RV64IM instructions. This is a certificate-profile header codec, not
validation of INTEGERs, OIDs, dates, BIT STRINGs, nesting, names or certificates.

Rules follow X.690 sections 8.1.2, 8.1.3 and 10.1. The Go standard library's
`encoding/asn1.parseTagAndLength` was inspected as an implementation comparison;
no Go code is copied or invoked by the production routine. Go ASN.1 is an
independent test-only oracle. High-tag-number form and universal end-of-contents
are rejected; context-specific tag zero is supported. Unknown non-critical X.509
extension contents can stay opaque, without imposing these tag restrictions on
their internal data.

## ABI

- `decode`: a0=input pointer, a1=available bytes. Success returns a0=0,
  a1=identifier byte, a2=header length, a3=content length, a4=total consumed.
  At most ten header bytes are read, but the entire declared content must exist.
  Trailing bytes are left for the caller. All four outputs are zero on failure.
- `encodeHeader`: a0=identifier byte, a1=content length, a2=output pointer,
  a3=capacity. Success returns a0=0, a1=header bytes written (2..10).
  This writes the header only, not content. All 64-bit content lengths are
  representable; allocating the full TLV and checking its total is the caller's job.
- Both preserve ra/sp/gp/tp/s-registers and clear all other caller-saved registers.
  No stack or workspace is used. Byte buffers need no alignment.
- Status: 1=truncated; 2=unrepresentable length; 3=non-minimal;
  4=wrapping range; 5=insufficient output capacity; 6=unsupported identifier;
  7=indefinite length; 8=reserved length octet 0xff.
- Range/capacity/tag rejection in the encoder makes no memory access.
  The decoder checks its whole available range before its first read.
  Ownership, mapping, permissions and code/data separation are caller preconditions.
  Decoder inputs are read-only; encoder failures leave output unchanged.

The four canonical varint routines retain their different ABIs and semantics.
In particular, DER length fields are not QUIC varints or unsigned LEB128.

## Verification

```sh
lake exe libp2p-asm-tests
python3 Tests/Der/check.py
lake build Tests.Axioms
```

Requirements: Lake, Python, Go, GNU riscv64-unknown-elf tools, QEMU.
`QEMU_RISCV64`/`--qemu` and `--prefix` override tool locations.
The native model is compiled by Lake, with no manual dependency list.

The suite checks 400 decoder and 144 encoder cases against independent Python,
Spec, actual instruction fetch/execution, complete register/memory snapshots,
strict access footprints, GNU bytes and both GNU/encoded QEMU executables.
Go ASN.1 independently checks 383 applicable decoder cases. Cases include every
identifier byte, minimality, truncation, lengths through 2^64-1, wrap and capacity
errors, nonzero initial registers and unaligned buffers.

Three kernel-checked Spec lemmas establish success consumption bounds, explicit
length overflow rejection and the distinction between context-specific zero and
end-of-contents. The global axiom audit includes their transitive dependencies.
Full ASM/Spec correspondence, arbitrary-memory frame and instruction bounds remain
separate proof obligations; these finite execution tests are not those theorems.
