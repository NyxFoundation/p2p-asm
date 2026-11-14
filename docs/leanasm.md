---
title: LeanAsm boundary
last_updated: 2026-11-14
tags:
  - leanasm
  - boundaries
  - formal-verification
---

# LeanAsm boundary

p2p-asm consumes the portable RV64 foundation from
[NyxFoundation/LeanAsm](https://github.com/NyxFoundation/LeanAsm). LeanAsm owns
the canonical instruction vocabulary and execution semantics; p2p-asm owns only
the policy describing which opcodes its current execution and proofs accept.

## Shared now

- `Word`, integer registers, ABI register aliases, and traps
- the canonical fixed-width `LeanAsm.Rv64.Instr` type: the local inductive and
  its `Instr.toLeanAsm` embedding are gone; p2p programs use the shared
  constructors directly
- `Opcode`, `IsaProfile`, and the common `EmitAsm` / `LowerRv64` capabilities;
  lowering of local instruction lists is profile-gated, so an opcode outside
  `isaProfile` is rejected instead of silently widening the accepted set
- region memory, register state, executable images, execution semantics, and
  machine-code encoding via the LeanAsm definitions (type abbreviations expose
  them under the local `Memory`/`State`/`Program` names; dot notation and the
  exported qualified names both unfold into the same definitions)
- GNU assembly emission: `Codegen.assembly` renders instructions through the
  shared `LeanAsm.Rv64.emitInstr`; the p2p-specific section and entry symbol
  stay local
- upstream provenance for the reusable RV64 layer

`Rv64/Profile.lean` declares `isaProfile` and provides the gated capability
instances. Widening the profile is an explicit p2p proof change.

## Local by design

- the small structured SAsm AST (`Stmt` with `loop`/`ite`) and its
  position-independent lowering; it bridges to LeanAsm through the gated
  `LowerRv64`/`EmitAsm` instances, and folding it into the shared
  `LeanAsm.SAsm` AST remains future work now that proof consumers keep
  depending on the local unfold shape
- relocation and access-footprint predicates
- protocol routines and their contracts
- parser-specific frame lemmas that step the shared semantics at the
  instruction level
