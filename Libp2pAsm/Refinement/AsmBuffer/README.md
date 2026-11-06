# Buffer resolver correspondence

`resolve_table_embedded` proves the original `Asm.resolveBuffer` against the
original `Spec.Abi.resolveBuffer`, through actual instruction fetch and
`runUntil`, with arbitrary admissible placement, enclosing code and ABI return.
No successful resolution, load, or execution is a caller premise.

The universal raw proof includes all 64-bit access/count/reference/descriptor
values. Its bound is 96 instructions (the case proofs take at most 36).
Errors return a0=1/2/3/4/5 and zero both outputs. Success returns the address and
length. All executions preserve the complete memory, original ra and
callee-saved registers. An empty `WriteTrace` proves there are no stores,
including stores of unchanged bytes. Every proper execution prefix stays inside
the leaf, so surrounding code and the return continuation are not fetched.

## Representation and caller obligations

- `Invocation` states code alignment, 64-bit no-wrap, memory validity,
  writable-data/code separation, the exact code subarray and an aligned return
  address outside the leaf. It contains no execution-success condition.
- `WordAt` gives an actual region index, aligned address, byte bounds and pure
  little-endian interpretation. `WordAt.load` derives actual `Memory.load 8`
  success from this representation and disjoint valid memory.
- `ReferenceAt` owns all four reference fields and excludes reference-address
  wrap. Their decoded values are unrestricted words.
- `RegionAt` owns the selected descriptor only after access, count, slot and
  descriptor-address checks have passed. This permits representable wrapping
  table selections to be rejected without assuming an impossible mapping.
  Loaded descriptor fields have explicit 32-byte non-wrap and word ownership.
- `TableModel` relates the representable count and selected raw descriptor to
  the caller's logical table. It does not assume active identity, canonical
  flags, generation equality, permissions, region validity or successful bounds.
- `RegistryMapped` connects valid active logical registrations to actual owned
  memory and permissions. Successful results yield `SpanMapped` in the final
  (unchanged) memory, including valid empty one-past-end views.

## Validation order and SPEC scope

`tableSpec` adds only raw ABI validation that the typed SPEC cannot express:
access > 1, count >= 2^59, wrapping selected-descriptor address, and flags >= 4.
Unknown slot is checked before descriptor addressing/flags. After these checks,
the original table SPEC determines stale identity, invalid region, read-only,
bounds and success. Malformed flags precede active/generation validation.
`raw_refines_spec` and `abiSpec_table` prove this correspondence for all words.
The original region SPEC requires base+capacity < 2^64, including empty end
views; the universal proof includes sum == 2^64 and larger wrapping cases.

`invalid_access` and `invalid_count` separately prove return-before-load behavior
without *any* reference/descriptor ownership or successful-load premise.

`Tests.AbiProof.Buffer` instantiates universal contracts for 13 cases covering
success, all statuses, inactive/stale identity, malformed access/count/flags,
table/region wrap and an empty end view. It also instantiates the full logical
table/mapping contract. `Tests.AbiProof.Axioms` automatically audits all imported
proof-package theorems, allowing only propext, Quot.sound and Classical.choice.
These finite examples establish satisfiable representations; they do not replace
the universal theorems.

## Frozen input/build note

The codec worktree lacks the two existing Buffer SPEC/refinement source files.
They were read from `/home/shouki/libp2p-asm` and compiled read-only into a `/tmp`
module overlay. No SPEC/executable/model/lowering/root export was edited.
Main, which already owns these files, can build normally after copying this scope:

```sh
lake build Tests.AbiProof.Axioms
```

The isolated worktree's reproducible command is
`bash /tmp/libp2p-asm-build-buffer-proofs.sh`. It uses only this worktree and `/tmp`
for writes and never edits the two frozen input sources.
