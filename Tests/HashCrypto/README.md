# Whole-message RV64IM crypto

The runtime is typed RV64IM `Instr` inside checked `SAsm`. SHA compression uses
`Sha2.compressBody`; there are no pure hash calls, FFI calls or crypto opcodes in
the emitted runtime. Numeric IVs are generation-time data expanded by `Util.load`
into ordinary ADDI/SLLI/ORI instructions. Round tables are caller-supplied immutable
standard constants in LE64 slots, as in the original compression ABI.

## Public entry points

All parameters below occupy a0 through a7 in order, except the explicitly stated
ninth parameter. All lengths/capacities are unsigned RV64 words. All functions
return a0=status, clear the other caller-saved registers, and preserve ra, sp, gp,
tp and s0..s11. Output bytes are in the supplied output buffer. No function returns
an output pointer or count in a register.

| Entry point | Parameters | Owned stack below entry sp |
| --- | --- | ---: |
| `SHA256.hash` / `SHA512.hash` | input, inputLen, output, work, capacity, constants | 176 bytes |
| `HMAC.sha256` | key, keyLen, message, messageLen, output, work, capacity, constants | 288 bytes |
| `HKDF.extract` | salt, saltLen, IKM, IKMLen, output, work, capacity, constants | 288 bytes |
| `HKDF.expand` | PRK, PRKLen, info, infoLen, output, L, work, capacity; ninth argument = constants pointer at 0(sp) | 400 bytes |
| `TlsKdf.encodeLabel` | label, labelLen, context, contextLen, requested L, encodedOutput, outputCapacity | 0 bytes |

SHA leaves are `SAsm.Stmt`. HMAC/HKDF return `Except String SAsm.Stmt` because
linking checks relocations and all final SAsm ranges. Link errors are generation
errors, not runtime statuses. `TlsKdf.encodeLabel` is the RFC 8446 HkdfLabel encoder;
pass its bytes as HKDF info to perform Expand-Label. Its uint16 L domain deliberately
remains separate from HKDF-SHA256's 8160-byte expansion bound.

The caller provides valid, non-overlapping readable/writable ranges for input,
output, the claimed workspace capacity, stack, constants and code. sp is
16-aligned; work/constants are 8-aligned. Input/output may have any byte alignment.
The ninth argument is a readable, untouched 8-byte slot at entry sp and is outside
the owned stack below sp. Mapping/permissions/ownership are caller preconditions;
the implementation cannot inspect page tables or prove that supplied buffers are
mapped. Runtime checks reject wrapping accessed ranges and wrong work/table
alignment. A range whose last byte is 2^64-1 is accepted. Empty input pointers are
never dereferenced and need not designate a mapped address.

## Exact workspace layouts

All offsets below are from work. Only the required prefix is owned/wiped; any
capacity beyond it remains untouched. Stack sizes include all nested callees.

| Operation | Required bytes | Layout |
| --- | ---: | --- |
| SHA-256 | 704 | state [0,64), schedule [64,576), two tails [576,704) |
| SHA-512 | 960 | state [0,64), schedule [64,704), two tails [704,960) |
| HMAC / extract | max(896, 864+messageLen) | key [0,64), inner digest [64,96), SHA [96,800), concat [800,required) |
| HKDF expand, L>0 | align8(32+m)+max(896,864+m) | T [0,32), concat [32,32+m), alignment padding, HMAC suffix |

For expand, `m=infoLen+1+(if L>32 then 32 else 0)`, and
`align8(x)=8*ceil(x/8)`. The capacity check includes the longest iteration, before
any output is written. The first iteration has no previous T prefix. Counters are
1 through 255, and only the last output copy may be partial. Long keys are hashed
directly; there is no allocation proportional to key length. Long messages/info
use the advertised checked caller workspace, not hidden stack buffers. Calls do
not allocate heap memory. The Lean generation/test machinery is not runtime code.

Each composed routine owns a 112-byte save frame (12 s-registers, ra, 8 bytes of
padding); compression owns another 64 bytes. Restored registers are loaded before
their slots are zeroed. Every owned workspace byte and used frame byte is zero on
successful return. All public failure conditions are checked before secret access;
rejections leave workspace, stack, output and all inputs untouched. Private callees
have prevalidated contracts and contain no runtime rejection paths. A memory trap
from violation of the caller's mapping/ownership contract is not a status return
and has no cleanup guarantee.

## Domains and statuses

| Status | Meaning | Pure-spec correspondence |
| ---: | --- | --- |
| 0 | success | `.ok bytes` |
| 1 | SHA-256 bit-length bound | `Spec.Crypto.Error.messageTooLong` |
| 2 | HKDF output >8160, or label L>65535 | respective `outputTooLong` |
| 3 | HKDF PRK length <32 | `Spec.Crypto.Error.prkTooShort` |
| 4 | accessed range wraps or work/table misaligned | ABI error, no pure-spec error |
| 5 | insufficient caller capacity | resource error, no pure-spec error |
| 6 | application label >249 bytes | `TlsKdf.Error.labelTooLong` |
| 7 | context >255 bytes | `TlsKdf.Error.contextTooLong` |
| 8 | empty application label | `TlsKdf.Error.labelTooShort` |

SHA-256 accepts inputLen<2^61. SHA-512 accepts every representable 64-bit byte
length, subject to a valid backing range, and emits a 128-bit length with high
word `inputLen >> 61` and low word `inputLen << 3`. Its pure spec additionally
supports lengths beyond the machine ABI's representable range.

HMAC accepts empty/short/exact-block keys and any longer key satisfying SHA-256's
length bound. It requires `messageLen+64<2^61`. Extract maps zero salt length to
both `none` and `some []`; both equal the default 32 zero bytes. This equivalence
is a kernel-checked pure-spec lemma. Positive-length expand requires PRKLen>=32,
PRKLen<2^61 and `m+64<2^61`; these match the hashes actually invoked by the spec.
L=0 still checks the HKDF output/PRK-minimum conditions, then succeeds with no input,
workspace, constants-slot or stack access. Its capacity may be zero, and it does
not impose the positive-L hash bounds on unused PRK/info lengths.

The label encoder writes exactly `10+labelLen+contextLen` bytes: big-endian uint16
L, uint8(6+labelLen), ASCII `tls13 `, exact label bytes, uint8 contextLen, exact
context bytes. RFC 8446 section 7.1 requires the prefixed label to contain 7..255
bytes, so application labels contain 1..249 bytes. Empty contexts remain legal.
Empty labels return status 8 before any memory access or write (after the uint16
L check). No extra ASCII/content policy is applied to opaque label/context bytes.

## Internal calls and branch ranges

`Whole.body` and `HMAC.body` are private-contract leaves without validation.
`Whole.compressAt` sets compression arguments from preserved s-registers and
inlines the public no-return `Sha2.compressBody`. Compression still restores its
64-byte frame and working s-registers before control falls through.

Inlining entire HMAC bodies inside HKDF would exceed SAsm's 4096-byte conditional
branch range. `Link.Part` therefore resolves local calls into five existing typed
instructions: AUIPC t6, ADDI t6 (continuation at +20), AUIPC ra, ADDI ra (callee
address), then SAsm.ret (JALR x0,ra,0). The callee adopts t6 as ra and saves it before
nested calls. The public root uses the standard incoming ra. Relocations are
position independent, signed high/low immediates are range-checked before conversion,
and the final complete SAsm passes its unchanged validator. No common lowering or
execution-model file was modified, and no branch offset is truncated to fit.

The original compression wrappers retain all 230/197 instructions. The test runner
pins their original encoded SHA-256 digests:

- SHA-256 compression: `c1b23252c841d98336099a8a3a54b353ca087f39f8da1c29ec1a599e736a1c88`
- SHA-512 compression: `49bf4324ea2e565bbf129f8d10b32523c29c7e103136277825bab280329125e6`

## Running checks

Run from the repository root:

```sh
python3 Tests/HashCrypto/check.py
# Or set QEMU_RISCV64 to the executable on this machine.
# Optional: --only sha256|sha512|hmac|extract|expand|tls|length512
python3 Tests/AsmCrypto/check.py --qemu "${QEMU_RISCV64:-qemu-riscv64}"
```

The new runner defaults to `qemu-riscv64` and accepts `QEMU_RISCV64` or `--qemu`;
GNU defaults to `riscv64-unknown-elf-` with `--prefix` override. It uses the existing
Lake-selected Lean toolchain and standard `lake --no-cache build +Module:olean`
targets, with no separate import/dependency resolver. Lake artifacts stay in ignored
`.lake/build/`; machine code, ELF files, snapshots and logs stay in ignored `build/native/hashes/`.
The code generator exports the individual hash, HMAC, HKDF and TLS-label routines.

Cases run the lowered instructions with `runUntil`, compare success against the
independent established Lean specs and Python hashlib/hmac, compare GNU assembler
bytes with `encodeProgram`, then execute both the GNU and raw-encoded ELF paths in
QEMU. Every case compares the entire memory/register snapshot, including all
preserved registers, all output guards, untouched input/table/capacity suffixes,
and exact stack/workspace wipes. Selected successes and all rejections compare
public PC/access traces for equal-length differing contents and check accesses
against permitted payloads. Trace comparisons are finite diagnostics.

Vectors include existing published NIST CAVP SHA data, RFC 4231 cases 1-7 (case 5
published prefix), NIST block-key HMAC, RFC 5869 A.1-A.3, 55/56/63/64 and
111/112/127/128 padding boundaries, 4097-byte input/key/info, every HKDF counter at
L=8160, longer PRKs, all label length fields, capacity/range/alignment failures.
`length512` runs the actual shared length-field instruction fragment at high-word
transitions and 2^64-1; it is not a whole-message execution of exabyte-sized input.

The suite contains 173 cases (SHA-256 36, SHA-512 35, HMAC 29,
extract 15, expand 34, TLS 18, length-field fragment 6), 346 QEMU executions,
and 95 finite trace pairs. The existing unchanged compression suite separately
passes 85/63 model cases and both QEMU paths, with byte-for-byte wrapper equality.
`build/native/hashes/` contains the emitted code, per-case model snapshots and execution counts.

## Formal proof boundary

`Refinement/Crypto/Composition.lean` proves universal bit-length arithmetic, HKDF
counter bounds, HMAC workspace arithmetic, TLS length arithmetic, compression
wrapper factoring, empty-label rejection, empty-context acceptance, and default-salt
equivalence. Its twelve lemmas are audited for
axioms; only Lean's standard propext/Classical.choice/Quot.sound are allowed.
Existing word-operation lemmas remain unchanged.

The following are still formal proof gaps, not claims established by tests:

1. Compression loop/schedule/feed-forward refinement to the full Spec compressor,
   including instruction fetch and memory representation (word identities alone
   do not prove this).
2. SHA whole-message loop/padding/output refinement for all admissible lengths,
   and instruction-level correctness of the shared length-field emitter.
3. HMAC normalization/concatenation and HKDF iteration/truncation refinement,
   plus TLS encoding refinement from arbitrary valid memory states.
4. General constant-loader and local-call relocation/continuation correctness,
   and compositional frame preservation for arbitrary linked bodies.
5. Universal memory safety, arithmetic nonwrapping, termination, status ordering,
   error atomicity and exact zeroization of all owned memory/register temporaries.
6. Relational constant-time/noninterference proofs for all equal-public-length
   inputs. Finite control/access comparisons and full-hash vectors are not these
   proofs, nor cryptographic-security proofs or microarchitectural guarantees.

The implementation is tested functionality; it does not claim whole-function
formal verification.
