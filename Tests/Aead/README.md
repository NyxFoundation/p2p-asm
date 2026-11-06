# AES-128 and AES-128-GCM RV64IM tests

The production entry points are typed `SAsm.Stmt` values in
`Libp2pAsm/Asm/Crypto/AES/Api.lean` and `Libp2pAsm/Asm/Crypto/GCM/Api.lean`.
They lower to ordinary RV64IM instructions and never invoke the reference
specifications, a crypto library, FFI, custom opcodes, or secret-indexed tables.
The independent pure specifications are in `Spec/Crypto/{AES,GCM}/Basic.lean`.
The code generator exports AES expansion/block/header protection and GCM operations.

## Run

Lean 4.33.0 and Lake are pinned by the repository. Install test-only
`cryptography==49.0.0` from `Tests/Aead/requirements.txt` in your test environment.
GNU `riscv64-unknown-elf-{as,ld,objcopy}` and QEMU's RV64 Linux-user emulator must
be available. The default emulator is `qemu-riscv64`; override it with
`QEMU_RISCV64` or `--qemu`. No tool downloads or cron jobs are performed.

```sh
python3 Tests/Aead/check.py
lake build Tests.Aead.ProofAudit
lake env lean Tests/Aead/ProofAudit.lean
```

For a non-default emulator path:

```sh
QEMU_RISCV64=/path/to/qemu-riscv64 python3 Tests/Aead/check.py
```

Artifacts stay under ignored `build/aead/` and Lake's `.lake/`. `--kinds` limits
routines; `--native-only` reuses model snapshots after checking the fixtures are
identical. This is test orchestration, not an alternate production runtime.

## Contracts

All interfaces are leaf routines. They preserve `ra`, `sp`, `gp`, `tp` and all
`s` registers; every other caller-saved register is zero at return except
`a0`, which contains the status. Input and output lengths are public. All
buffer ranges must be valid, disjoint, nonwrapping and separate from code;
the caller owns the designated stack area. Byte buffers can be unaligned;
workspace and GCM descriptor require 8-byte alignment, `sp` 16-byte alignment.
Memory mapping, overlap and pointer validity are preconditions, not runtime
checks. No state is allocated implicitly or retained between calls.

| Entry point | Arguments | Output / scratch |
| --- | --- | --- |
| `AES.expand` | a0 key, a1 key length, a2 output, a3 capacity, a4 workspace, a5 workspace capacity | 176-byte schedule; 1024-byte workspace; no frame |
| `AES.encrypt` | a0 schedule, a1 block, a2 block length, a3 output, a4 capacity, a5 workspace, a6 workspace capacity | 16 bytes; 1024-byte workspace; 16-byte frame |
| `AES.headerProtection` | same as encrypt | first 5 bytes of AES(sample); same scratch |
| `GCM.update` | a0 GHASH accumulator, a1 H, a2 block; each 16 bytes | accumulator updated; no workspace/frame |
| `GCM.seal` / `GCM.open` | a0 immutable descriptor below | variable prefix; 1280-byte workspace; 128-byte frame |

The GCM descriptor consists of twelve LE64 slots in this order: key pointer,
key length, nonce pointer, nonce length, AAD pointer, AAD length, input pointer,
input length, output pointer, output capacity, workspace pointer, workspace
capacity. Pointers are machine addresses. Length fields inside GCM blocks and
counter values are big endian. The profile requires key length 16, nonce length
12 and a full 16-byte tag. Seal appends the tag; open consumes ciphertext and tag.
There is no allocation proportional to message length.

GCM rejects message lengths above `2^36-32` bytes and AAD lengths above `2^61-1`
bytes before counter/bit-length arithmetic. Open rejects input shorter than
16 before subtraction and output capacity checks. Validation occurs before
payload accesses or frame acquisition; invalid calls leave memory untouched.
Capacities are checked, with malformed cryptographic input distinguished from
resource failures. The ABI docs give the exact validation order.

| GCM status | Meaning |
| --- | --- |
| 0 | success |
| 1 / 2 / 3 | invalid key length / nonce length / short ciphertext |
| 4 / 5 | message-counter bound / AAD length bound |
| 6 | authentication failed |
| 7 / 8 | output / workspace capacity |

AES statuses are 0 success, 1 key length, 2 block length, 3 output capacity,
4 workspace capacity. For every accepted call, workspace and owned frame are
zeroized, including the internal GCM schedule. Caller-owned key/schedule and
output remain. Only the required output prefix and workspace prefix are used.
The output length is implied by the checked inputs; no length register is returned.
Nonce uniqueness for repeated seals is a caller protocol obligation.

Open computes and compares all tag bytes before CTR processing. It derives
an all-ones/zero mask using SLTU and arithmetic, then reads and writes every
output byte with `(plaintext & mask) | (oldOutput & ~mask)`. Failure preserves
all output bytes, including pre-existing nonzero bytes. Unauthenticated
plaintext is transient in registers only; no private plaintext array is stored.
The AES state, schedule, GHASH state, masks, frame and caller temporaries are
wiped on both success and authentication failure. The result status is the
explicit declassification; authentication does not control branches/addresses.

## Sources and independence

- AES specification, S-box field inversion/affine map, key schedule and block
  vectors: [FIPS 197-upd1](https://doi.org/10.6028/NIST.FIPS.197-upd1), Appendices
  A.1/B and the original Appendix C.1; further block answers from
  [SP 800-38A](https://doi.org/10.6028/NIST.SP.800-38A), Appendix F.1.1.
- GCM algorithm and normative limits:
  [SP 800-38D](https://doi.org/10.6028/NIST.SP.800-38D), sections 5.2, 6 and 7.
- Official GCM vectors: [NIST AES_GCM.pdf](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/AES_GCM.pdf),
  AES128 examples 1, 2, 3 and 5 (empty, full, AAD-only and partial blocks).
  Two additional zero-key known answers are regression fixtures; the official
  examples above independently establish provenance.
- The 115-gate Boyar–Peralta S-box is translated from BearSSL `aes_ct64.c`,
  commit `7561e7d6c86171257a4153d95202b0791b3612a8`, blob
  `981e63d9ae459eb283c3db357a6bc25a2200c4df`.
  [Primary source](https://www.bearssl.org/gitweb/?p=BearSSL;a=blob_plain;f=src/symcipher/aes_ct64.c;hb=7561e7d6c86171257a4153d95202b0791b3612a8)
  was read at the same commit through its
  [GitHub mirror](https://github.com/ryanwoodsmall/bearssl-mirror/blob/7561e7d6c86171257a4153d95202b0791b3612a8/src/symcipher/aes_ct64.c).
  Copyright Thomas Pornin, MIT license in `LICENSES/bearssl.txt`; the upstream
  code credits [Boyar/Peralta 2009/191](https://eprint.iacr.org/2009/191).
  Only the circuit is adapted, with reversed input/output bit numbering.
- The test-only oracle uses cryptography/OpenSSL AES ECB and AESGCM, with no
  production dependency. Tests also compare against the independent Lean field
  specification. Test key schedules use FIPS's table algorithm and Appendix A.1.

## Evidence and limitations

The suite covers all 256 S-box bytes, full schedules, AES/header protection,
GHASH, empty/partial/full/multiple GCM blocks, AAD, every short input length
0..15, modified tag bytes/ciphertext/AAD/nonces, exact/insufficient capacities,
maximum-length metadata, unaligned buffers, read/write guards, callee/stack
preservation and wiping. It compares complete model snapshots, public control
and address traces, official vectors and the external oracle. GNU assembly bytes
must exactly match `encodeProgram`; QEMU executes both assembly and encoded
bytes for every fixture. No C cryptography is linked into these test ELFs.

The GCM arithmetic bounds and branchless commit/mask identities are universal
Lean theorems. The S-box theorem compares the Boolean circuit with independent
field inversion on all 256 inputs using kernel reduction; no `native_decide`,
`unsafe`, `sorry` or new axiom is used. `ProofAudit.lean` lists dependencies.
These lemmas do **not** prove the full AES/GCM routines, gate-memory compilation,
transposition, instruction fetch, memory safety, wiping or trace noninterference.
Those end-to-end claims currently have executable test evidence only. BearSSL's
upstream C is not a Lean or RV64 proof. Hardware timing, speculation and power
leakage are outside the PC/address trace model.

`fuelBudget(n,a) = 100000 + 40000*(ceil(n/16)+ceil(a/16))` is a conservative
public-length execution budget checked on test fixtures, not a proved universal
termination bound. Validation errors take at most 128 instructions in the suite.
The static code sizes and measured per-case counts are emitted in each routine's
`measurements.txt` rather than inferred from asymptotic descriptions.
