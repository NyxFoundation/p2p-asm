# Clock ASM refinement

`Contract.check_embedded` proves the complete frozen `Asm.checkClock` implementation
corresponds to the frozen `Spec.Clock.update` for every raw ABI word. It executes
the actual lowered instruction array, including fetch, loads, stores and return.
The universal theorem does not assume successful execution or a successful clock
decision. `Tests.AbiProof.ClockAxioms` audits every imported Logic/Clock theorem
and every ABI proof example, including their transitive axiom dependencies.

## Public contracts

- `check_embedded`: arbitrary admissible entry address, enclosing program and ABI
  return address; `runUntil` with a 256-instruction bound; exact status and updated
  state; preserved original return address and callee-saved registers; every proper
  execution prefix stays inside the leaf routine.
- Its memory postcondition names the entire final heap, retaining every other
  region, permission and address. `ByteFrame 0 32` preserves all padding beyond the
  state, and `StateAt` interprets the actual four LE64 words after execution.
- Its `WriteTrace` restricts every actual store to the 32-byte state, including
  stores that happen to write the previous value.
- `invalid_limits_embedded` needs no readable state or sample pointer. It returns
  before any memory access and preserves all memory with an empty store trace.
- `invalid_state_embedded` and `stopped_embedded` need state ownership, but never
  read the sample. Both preserve all memory with an empty store trace.

## Caller representation and placement

The state starts at the first owned writable region's base. That region has at
least 32 bytes and can contain arbitrary padding; the rest of memory is an arbitrary
valid disjoint frame. `StateBytes` describes the four state fields. `SampleAt`
owns five aligned LE64 words and explicitly excludes wrapping the 40-byte sample.
The public contract requires the 32-byte state and 40-byte sample to be disjoint.

`Invocation` supplies aligned, nonempty, nonwrapping code, valid memory, writable
code/data separation, a genuine code subarray in the enclosing program, and an
aligned return address outside the leaf routine. The return address may point into
the enclosing caller. It is not used as a scratch register during relocation.
No source-layout address or zero return-address constraint reaches the caller.

Sample correlation with real observations and chronological scheduling remain
environmental obligations of the protocol core. The machine/SPEC correspondence
itself covers every raw sample, including rejected order, source status and nanos.

## Policy and arithmetic coverage

Mode 0 ignores the previous wall timestamp, including noncanonical previous nanos.
Mode 2 stores a recovery candidate and returns unavailable. Mode 3 stays stopped.
Modes 1 and 4 require canonical previous nanos before reading any sample. All raw
mode, limit, status, epoch and nanos words are covered; signed epochs include both
64-bit extremes.

`signed_difference`, `elapsed_parts` and `multiply_with_carry` connect signed seconds,
nanosecond borrowing, MUL/MULHU and carry to the exact nonnegative elapsed duration.
`withinDrift_exact` proves the complete two-limb subtraction and drift decision,
including a borrow that changes a nonzero high limb to zero. `coherent_exact` then
connects those words to the original integer policy. There is no 64-bit truncation
assumption on elapsed wall time or its difference from monotonic time.

`raw_refines_spec` preserves validation order and all five statuses. `raw_trace`
constructs the complete finite instruction trace. Neither theorem takes an
execution result as a precondition.

## Validation

```sh
lake build Tests.AbiProof.ClockAxioms
```

`ClockEarly` instantiates early-return theorems with an unmapped sample pointer.
`ClockUpdate` instantiates the universal contract with owned sample bytes, writable
state padding and unrelated memory, covering initialization, recovery, nanosecond
borrow, signed epoch extremes, large elapsed durations, a high-limb borrow,
unavailability, monotonic failure, invalid limits/state and sticky stop.
Expected results are checked against the original SPEC. These instances establish
satisfiability of the representations and exercise the universal theorem; they do
not replace its all-domain proof.

The only allowed axiom dependencies are `propext`, `Classical.choice` and
`Quot.sound`. The proof sources contain no `sorry`, added axioms, `native_decide`,
`bv_decide` or `unsafe`. ASM, SPEC, execution semantics and lowering are unchanged.
