# Hunt list

Walk every item in Pass 4. Cite a definition, a `step` body, or a
`#guard`. These are questions, not answers.

## Vacuity — the highest-yield hunt here

- **Unsatisfiable cell.** Which cell does the precondition carry?
  `a ↦ₘ v` requires `isValidDwordAccess a` *inside the resource*, so at
  any address off ZisK's zones the precondition has no inhabitant and the
  triple is vacuously true. `memIsSp1` requires `isValidMemAddrSp1`.
  A transferred ZisK leaf never carries an SP1 cell.
- **Region alignment.** `bytesRegionOn` owns `⌈|bs|/8⌉` **dword** cells
  from a dword-aligned base. An unaligned base makes it unsatisfiable;
  two regions under `**` need disjoint dword-*rounded* spans, which is
  more than byte non-overlap.
- **Judgement invariant.** `cpsWithin` ranges over `st.inv` states. Is
  `inv` true of a state the caller can actually produce?
- **Unused hypothesis.** Does the proof drop a hypothesis that was
  restricting the domain to unreachable states?
- **Is there an inhabitant at the instance that matters?** A `#guard`
  that the cells are valid is cheap and is the check that catches this.

## Observation

- **What is accept?** Does the statement use `cpsHalt` where it needed
  `cpsSyscallHalt`? A trap satisfies the former.
- **What does the postcondition not say?** Registers the block
  overwrote, memory it changed, a pointer it destroyed.
- **Frame.** Is `pcFree` true of the frame, and does the frame contain
  the atom the instruction writes? Framing cannot fake a footprint that
  is genuinely smaller.

## Rules and their side conditions

- **Side condition discharged?** If a certificate returns a `pre` /
  `cond`, is it proved for the caller's state, or only stated?
- **Fuel.** Is a step count a correctness parameter threaded by hand?
- **Loop rule shape.** Does the abstract loop's `side` hold at *every*
  state the rule quantifies over, including unreachable ones? For
  `RunsTo`, including the exit state?
- **Exit labels.** Does every `inr` branch of a `RecB` body reach the
  same machine label, and does the region include the join?
- **Bound arithmetic.** `cpsWithin n` is "at most `n`". A composition
  that claims a smaller `n` than its parts is a real bug.

## Machine

- **Which `none`?** `stepSp1` returns `none` for no code, `.CSRS`,
  `.EBREAK`, a failed `memOkSp1`, and an unmodelled ecall — as well as
  for `HALT`. Which does the statement mean?
- **Backend agreement.** A leaf transferred from ZisK holds on SP1 only
  where `PlainAgree` does. Check `isMemAccess`, `.ECALL`, `.EBREAK`,
  `.CSRS`.
- **Store guard.** SP1 rejects a store where `code` is present at any
  byte; ZisK excludes a fixed window. These are incomparable, not
  ordered.

## Calibration

If the report does not discuss whether the statement can be vacuously
true and what its postcondition fails to say, the audit is incomplete.
