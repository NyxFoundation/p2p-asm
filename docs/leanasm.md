# LeanAsm boundary

p2p-asm consumes the portable RV64 foundation from
[NyxFoundation/LeanAsm](https://github.com/NyxFoundation/LeanAsm), but keeps a
finite local instruction profile because several proofs perform exhaustive
case analysis over exactly the instructions implemented by the project.

## Shared now

- `Word`, integer registers, ABI register aliases, and traps
- canonical fixed-width RV64 instruction vocabulary used as the embedding target
- machine-code encoding
- upstream provenance for the reusable RV64 layer

## Local by design

- `Rv64/Profile.lean`: the finite instruction subset admitted by p2p proofs
- region-memory proofs and parser-specific frame lemmas
- compact SAsm frontend used by existing routines
- relocation and access-footprint predicates specialized to the finite profile

The local profile has a total `Instr.toLeanAsm` embedding. Encoding therefore
has one implementation in LeanAsm, while exhaustive p2p proofs cannot silently
change when LeanAsm adds another instruction.

## Remaining consolidation

The executable region-memory semantics in p2p-asm and LeanAsm currently have
the same design ancestry but different proof APIs. They should only be merged
when the memory/frame/relocation lemmas move with the implementation. Replacing
the definitions with aliases alone changes their unfold shape and breaks those
proofs without adding assurance.
