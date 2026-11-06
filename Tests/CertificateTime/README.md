# X.509 time codec on RV64IM

`Asm.Identity.Time.decode` takes a0=ASN.1 tag (23/24), a1=body pointer,
a2=body length. It returns a0=status, a1=two's-complement Unix seconds.
`encode` takes a0=Unix seconds, a1=output pointer, a2=capacity; it returns
a0=status, a1=written. It emits a complete DER time TLV: UTCTime for
1950..2049 (15 bytes), GeneralizedTime otherwise (17 bytes).

Both use Gregorian years1..9999 and UTC seconds. UTC years00..49 denote
2000..2049; 50..99 denote1950..1999. Decoding accepts either tag with its exact
13/15-byte body. Seconds and uppercase Z are mandatory. Fractions, offsets,
leap-second spelling, year0000 and invalid calendar dates are rejected,
not normalized. No clock trust or certificate authentication is implied.

Status0=success, 1=wrong body length, 4=address range, 5=output capacity,
6=tag/syntax/calendar/time range. Failures clear a1; the first validation
error wins. Encoding checks time domain, then capacity, then pointer range.
Decoding checks tag, length, range, then contents.

No stack/workspace is used. Decode only reads body bytes; encode only writes
its exact result. Metadata failures access no memory; encode failures write
nothing. ra/sp/gp/tp/s0..s11 are preserved and other caller-saved registers
are zero. Inputs/outputs may be unaligned. Mapping, permissions, stability,
return/code validity and code/data separation are caller preconditions.
A byte span ending exactly at2^64 is supported in the machine model.

## Exact validity comparison

`Asm.Identity.Time.validity` takes signed64 a0=NotBefore seconds,
a1=NotAfter seconds, a2=current UTC nanoseconds. It compares inclusive bounds
using signed128 products, without overflowing distant certificate dates or
rounding fractional seconds. Status0=inside, 6=inverted interval, 7=not yet,
8=expired; all other caller temporaries/results are zero. It accesses no memory
or stack. A timestamp one nanosecond past NotAfter is expired. Clock trust must
already have been established by the core's Clock state.

## Verification

```sh
lake exe libp2p-asm-tests
python3 Tests/CertificateTime/check.py
```

Requires pinned Lean/Lake, Python, GNU RV64 tools and QEMU.
`QEMU_RISCV64`/`--qemu` and `--prefix` select executables.
297 decode,229 encode and700 validity cases compare independent Python datetime/Int, pure
Lean Spec, every actual machine instruction and both GNU/direct-byte QEMU
executables. Full snapshots and access traces check untouched memory,
saved registers, zero caller temporaries and exact read/write bounds.
Cases include century/leap-year boundaries, all prefixes, malformed digits,
invalid fields, signed limits, capacity, unaligned and wrapping pointers.
Two additional model-only checks exercise valid spans ending at2^64, which
are not mapped by Linux-user QEMU.

The Spec encoder reuses `Std.Time.PlainDate.ofEpochDay`; the ASM independently
uses bounded binary searches for year/month. The decoder uses civil-calendar
arithmetic, cross-checked by Python. No host date routine appears in runtime
instructions. The probe's5000-instruction fuel is a test budget, not a
universal bound/refinement theorem. Those proofs remain separate work.
Normative profile: RFC5280 §4.1.2.5; wall-clock trust is handled by the core.
