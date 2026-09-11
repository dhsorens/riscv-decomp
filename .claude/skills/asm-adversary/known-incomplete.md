# Already-known incompleteness

Do not score these as new findings unless the finding goes beyond the
known hole. `ROADMAP.md` is the live list; this file is the short form.

## Inherited from `riscv-zkvm`

- `decode` is not tied to Sail `encdec_backwards`.
- `stepExec` (the interpreter) is not proved to simulate `step`.
- The Pallas precompiles are `Accel` functions in the model, with no
  statement relating them to a group law.

## Known here

- `cpsHalt` observes only that the machine cannot step, so it cannot
  distinguish a halt from a trap. `SyscallHalted` / `cpsSyscallHalt` is
  the fix; `cpsHalt` is kept for callers that only need "stops here".
  Scoring `cpsHalt` as under-determined is not news — scoring a *use* of
  it that needed the distinction is.
- `Decomp.Reject` discharges only the trapping half of a reject-path
  argument. The halting half (`a0 ≠ 0` at a panic `HALT`) has no
  vocabulary yet.
- The same-register keystone family covers `LBU` only; the other loads
  have no `_same_at` form.
- `cpsTotal_loopB` requires every `inr` branch to reach one machine
  label. A region with two genuinely divergent exits cannot be stated.
- The `OffText` discharge lemmas are restated per guest rather than
  living here.

## Not known holes (score these)

Anything the library states that is weaker than it reads: a precondition
with no inhabitant at the addresses a caller will use, an unused
hypothesis, a side condition never discharged, a judgement whose `inv`
no reachable state satisfies, a postcondition that drops what the
instruction actually changed.
