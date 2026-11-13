# LeanAsm boundary

p2p-asm consumes the portable RV64 foundation from
[NyxFoundation/LeanAsm](https://github.com/NyxFoundation/LeanAsm). LeanAsm owns
the canonical instruction vocabulary; p2p-asm owns only the policy describing
which opcodes its current execution and proofs accept.

## Shared now

- `Word`, integer registers, ABI register aliases, and traps
- canonical fixed-width RV64 instruction vocabulary
- `Opcode`, `IsaProfile`, and the common `EmitAsm` / `LowerRv64` capabilities
- machine-code encoding and GNU assembly emission
- upstream provenance for the reusable RV64 layer

`Rv64/Profile.lean` declares `isaProfile` and provides capability instances for
existing p2p instruction arrays and structured statements. The local `Instr`
inductive and `Instr.toLeanAsm` embedding are transitional compatibility code,
not the final profile representation.

## Local by design

- parser-specific frame and memory lemmas
- relocation and access-footprint predicates
- protocol routines and their contracts

## Remaining consolidation

The next migration replaces the local `Instr` with `LeanAsm.Rv64.Instr` and
adds `isaProfile.Supports` hypotheses to exhaustive project-specific proofs.
The executable region-memory semantics should move with its generic frame
lemmas; replacing definitions with aliases alone changes their unfold shape and
breaks existing proofs without adding assurance.
