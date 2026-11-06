# Public-key protobuf and Peer ID codecs

The initial identity types are Ed25519 (1, 32 raw bytes) and secp256k1
(2, 33 compressed bytes). These codecs do not validate curve points or authenticate
signatures. Those are separate obligations before publishing an authenticated peer.

The normative source is [libp2p peer IDs at the design pin](https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/peer-ids/peer-ids.md).
Outbound protobuf is deterministic: minimal varints, Type then Data, both fields,
no extras. Peer IDs always hash this **canonical** encoding, not the potentially
noncanonical received message. Both serialized keys fit the <=42-byte identity
multihash rule, so no SHA256 is used for these two identity types.

## Routines

- `Asm.Codec.ProtobufVarint.decode`: a0=input, a1=available; returns a0=status,
  a1=uint64, a2=consumed. This accepts non-minimal protobuf forms, unlike the
  canonical 63-bit multiformats codec. At most ten bytes; tenth byte is 0 or 1.
  No stack or writes. Range is checked before reading.
- `Asm.Identity.PublicKey.decode`: a0=input, a1=length, a2=workspace, a3=capacity.
  Returns a0=status, a1=kind, a2=key data offset, a3=key data length.
  Requires length<2^61, work capacity>=8*length, 8-aligned work and 16-aligned sp.
  Owns exactly 8*length work bytes and 112 stack bytes below sp.
- `Asm.Identity.PublicKey.peerId`: a0=kind, a1=raw key, a2=key length,
  a3=output, a4=capacity. Returns a0=status, a1=written (38 or 39).
  No stack/workspace. Validates before any access; failure leaves output unchanged.

All preserve ra/sp/gp/tp/s-registers, clearing caller-saved registers except the
documented results. Failure clears results. PublicKey parsing wipes the whole
required workspace and saved frame on all content returns; metadata errors
touch no memory. Input, workspace, output and stack spans must not overlap where
applicable, and runtime checks enforce this. Mapping, lifetime, permissions and
separation from executable code remain caller preconditions. Byte inputs/outputs
may be unaligned. Work and output capacity suffixes remain untouched.

The receiving parser permits protobuf field reordering, repeated singular fields
(last correctly typed value wins), non-minimal varints and unknown fields,
including properly nested groups. Mismatched wire types on a known field are
treated as unknown, matching Go protobuf. It checks group matching and uint29
field numbers, and rejects wire types6/7 and field0. Kind must be exactly the
uint64 value1/2: it does not truncate an oversized enum to32 bits. Receiving
tolerance does not change the mandatory canonical encoding used for output/IDs.

Status: 0=success, 1=truncated, 2=integer/work-size overflow, 4=range/alignment/
overlap, 5=capacity, 6=wire/group/field error, 7=missing required fields,
8=unsupported key type, 9=wrong key length. Varint uses only0/1/2/4.
Empty PublicKey input returns7 without inspecting any pointer.

## Verification

```sh
lake exe libp2p-asm-tests
python3 Tests/Identity/check.py
```

Requires Lake, Python, Go, GNU RV64 tools and QEMU. `--qemu`/`QEMU_RISCV64` and
`--prefix` select tools. Go runs against the pinned module in
`tests/interop/go/`; it is only a test oracle, never the production parser.

187 independent Spec/Python/lowered-instruction/GNU/two-QEMU cases passed:
35 varints, 129 protobuf keys, 23 Peer IDs. Full snapshots cover all registers,
input/guard/unused memory, exact frame/work wipes and zero-access metadata
failures. Trace footprints reject accesses outside declared spans. The
go-libp2p/protobuf oracle additionally agrees on125 cases and canonical Peer IDs.
Tests include published public keys, all prefixes, full uint64 varints, alternate
field order, repeats, nested groups through256 levels, fixed/length-delimited
unknown fields, hostile lengths/tags, overflow, overlap and alignment failures.

Universal actual-instruction, ownership, termination and parser-view correctness
proofs are separate ongoing work, not implied by these finite test results.
