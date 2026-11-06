# ASM codec correspondence

The four embedded entry theorems quantify over all represented input words, capacities,
input bytes, guard bytes, initial register contents, and foreign memory regions.
They establish execution of the existing ASM through `Program.fetch`, `step`, and
`runUntil`, including every success and error outcome of the corresponding SPEC.

| Function | Entry theorem | Instruction bound |
| --- | --- | ---: |
| QUIC encode | `quic_encode_embedded` in `EmbeddedEncode.lean` | 128 |
| QUIC decode | `quic_decode_embedded` in `EmbeddedDecode.lean` | 64 |
| Unsigned encode | `unsigned_encode_embedded` in `EmbeddedEncode.lean` | 160 |
| Unsigned decode | `unsigned_decode_embedded` in `EmbeddedDecode.lean` | 128 |

## Entry representation

The code base, containing program, initial PC and ABI return address are arbitrary.
`Invocation` supplies explicit `ValidImage` alignment, nonempty code, 64-bit
non-wrap, valid memory and writable-code separation; `CodeSlice` identifies the
routine's unchanged instruction subarray inside the containing program.
`Placement` requires an aligned return address outside the leaf, which may be a
continuation inside the containing program. Code at address zero is permitted.

`Returns` proves the actual `runUntil` result, finite instruction bound, return
PC, unchanged original `ra`, callee-saved registers, and that every proper
execution prefix of the containing program has its PC inside the leaf. Thus
execution cannot fetch the surrounding code or execute the return continuation.

The original fixed-layout theorems remain arithmetic proof building blocks.
Generic instruction, trace and write-trace relocation changes PCs and restores
original `ra` while keeping all data addresses and memory effects unchanged.
A finite static proof checks that no instruction reads/writes `ra` except the
ABI return, and that ordinary control transfers cannot reach the source sentinel.
No successful-execution or successful-SPEC premise occurs in the entry contracts.

The first memory region owns the input/output buffer; its address is arbitrary.
`Program.valid` supplies disjoint regions, valid bounds and permissions, and
separation of writable memory from code. Explicit natural-number bounds prevent
pointer wraparound during actual accesses. Encoders require writable ownership
of at least the advertised capacity. Decoders permit either memory permission
and separate the advertised input from arbitrary trailing padding. An empty
input can use nonempty padding to satisfy the model's nonempty-region rule.
These are memory/layout preconditions, not conditions on decoding or execution.

## Results and frames

`DecodePost` gives `a0 = status`, `a1 = value`, `a2 = consumed`; errors zero both
outputs. Decoders preserve the complete memory and all callee-saved registers.
QUIC accepts nonminimal encodings, as its SPEC requires; unsigned decoding
rejects them. Both include truncation, and unsigned includes overflow.

`EncodePost` gives the SPEC bytes exactly, `a1 = written`, and `a2 = 0`.
Value overflow precedes the capacity check. `EncodePost.bytes` exposes every
written byte, unchanged guard bytes, and the unchanged list of foreign regions;
`EncodePost.error_memory` gives an unchanged heap for any error status.

Both encoder entry theorems also return `WriteTrace` with the interval
`[buffer base, buffer base + actual output length)`. Its `prefix_store` theorem
bounds every fetched store in any execution prefix. Errors have an empty
interval, so `empty_no_stores` rules out even stores of unchanged bytes.
`Safety.lean` proves that decoder instruction arrays contain no stores.

`Programs.lean` ties all four instruction arrays to the original ASM lowering.
No execution, ASM, or SPEC definitions are replaced. Intermediate successful
SPEC witnesses are constructed from input bounds in the total encoder proofs.

## Validation

`Tests.AsmCodecProof.Examples` instantiates the universal theorems with concrete
satisfiable states, including nonminimal decode and encodes with guard bytes and
an unrelated writable region. These examples are separate from the universal
proofs. `Tests.AsmCodecProof.Axioms` prints every public theorem's dependencies and
fails if any theorem in this package uses an axiom other than `propext`,
`Quot.sound`, or `Classical.choice`. All bit arithmetic uses kernel-checked lemmas.
`Tests.AsmCodecProof.Relocation` places all four routines at distinct addresses in
one image and returns to a deliberately observable callee-saved-register write.
The owned data buffer occupies the old fixed proof address, demonstrating that
only separation from the actual image is needed. Additional universal-theorem
instances cover base zero with the largest aligned return address and an image
whose exclusive end equals `2^64`.

```sh
lake build Libp2pAsm libp2p-asm-tests libp2p-asm-codegen Tests.Axioms Tests.AsmCodecProof.Axioms
lake exe libp2p-asm-tests
```
