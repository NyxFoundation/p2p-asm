---
title: LeanAsm boundary
last_updated: 2026-11-15
tags:
  - leanasm
  - boundaries
  - formal-verification
---

# LeanAsm boundary

p2p-asm consumes the RV64 foundation and scalar x86-64 instruction/emission
layer from [NyxFoundation/LeanAsm](https://github.com/NyxFoundation/LeanAsm),
pinned at `c55ebfef6eb0a44149deb4110654f71f4fd35543`. LeanAsm owns both instruction
vocabularies and machine semantics. p2p-asm owns its RV64 opcode policy and the
unproved translation from that profile to x86-64.

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
- typed `LeanAsm.X64.Instr`, `X64.Symbolic.emitLine`, and the
  `ABI.SysVAMD64` entry/exit frame helpers
- upstream provenance for the reusable assembly layers

`Rv64/Profile.lean` declares `isaProfile` and provides the gated capability
instances. Widening the profile is an explicit p2p proof change.

## Local by design

- the small structured SAsm AST (`Stmt` with `loop`/`ite`) and its
  position-independent lowering; it bridges to LeanAsm through the gated
  `LowerRv64`/`EmitAsm` instances, and folding it into the shared
  `LeanAsm.Rv64.SAsm` AST remains future work now that proof consumers keep
  depending on the local unfold shape
- `Codegen.X64`: register-context ABI, scalar translation, checked indirect
  control-flow dispatch, and GNU relative jump-table relocations. This is
  assembly emission, not a `LowerX64` fixed-instruction encoding instance.
  See [x86-64 backend](x86-64.md); existing RV64 proofs do not cover it.
- relocation and access-footprint predicates
- protocol routines and their contracts
- parser-specific frame lemmas that step the shared semantics at the
  instruction level
