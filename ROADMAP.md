# Roadmap

The work queue and the honest list of what is missing. `README.md` is the
contract; this file is what the contract does not yet cover.

Read it today rather than from memory — nothing here is frozen.

---

## Where this is

The L2 layer works end to end. A loop whose trip count depends on its input can
be stated and proved with no fuel and no variant, on either backend, from one
proof (`Decomp.Examples.CountdownMachine`). The instruction leaves and the byte
regions are enough to drive real compiled code: downstream, `memset`'s tail loop
and every path through `memcpy`'s ≤3-byte residual dispatch are proved against
this library, over a source and a destination region separated by `**`.

Both loop rules now have a consumer in this repository: `Countdown` drives the
header-guarded `cpsTotal_loop`, and `FindIndex` drives `cpsTotal_loopB` through
both of its `inr` branches -- a top-of-body break and a bottom exit converging
on one label. Neither touches memory.

What is *not* here is anything above L2. Every statement is machine-level: it
says what the code does to registers and memory, never that it meets a
specification. The refinement layer that would close that gap does not exist
(item 5).

`lake build`: 95 jobs, zero warnings. `scripts/check-axioms.sh`: 482
declarations on the three documented axioms.

---

## Known gaps

Ordered cheapest first within each group. An item is here because it is
*missing*, not merely trusted — `README.md` "Trust" has the trusted set.

### 1. The mid-body exit rule has one consumer, hand-written · small

`cpsTotal_loopB` takes `body : α → α ⊕ β`, so an early `break` is a second `inr`
branch and nothing in the rule counts exits. `Decomp.Examples.FindIndex` is the
first proof in which two distinct `inr` branches of one `body` are discharged
(`exit_` in `FindIndexMachine.lean`): a four-instruction index search that
leaves from the top of the body on a hit and from the bottom, through a `JAL`,
on exhaustion, on both backends from one proof. `Cert.ofLoopB` packages the
shape.

What it does *not* exercise is memory. The body touches three registers, so
there is no region coupling, no `x & 7 = 0 ↔ index % 8 = 0` bridge and no
eleven-atom invariant, and no compiler emitted it. A compiled `memcpy`'s
alignment loop, downstream, is still the first *real* consumer, and still owes
those three things.

*Acceptance (met):* a proof in which two distinct `inr` branches of one `body`
are discharged. *Remaining:* the same against compiler output over a region.

### 2. The same-register keystone family is one instruction wide · small

`LBU rd, off(rd)` needed its own leaf all the way down — `lbu_same_on`,
`bytesRegionOn_lbu_same_at`, `bytesRegionSp1_lbu_same_at` — because the ordinary
keystone's postcondition keeps `rs1 ↦ᵣ ptr`, forcing `rd ≠ rs1`, and framing
cannot fake it: the footprint is genuinely two atoms rather than three.

The same argument applies to `LB`, `LH`, `LHU`, `LW`, `LWU` and `LD`. None has a
`_same_at` form. Each is a ten-line mirror.

*Acceptance:* the six missing forms, and a note in `Region/Bytes.lean` saying
the family is complete.

### 3. The `OffText` discharges are restated per guest · small

A store leaf takes `OffText lo hi addr w`. For a typical image that is free in
both directions — a heap above `.text` discharges the second disjunct, a stack
below it the first — but both lemmas currently live in the downstream project,
stated at *its* `textLo`/`textHi`. They generalise to any window.

*Acceptance:* `offText_of_below` and `offText_of_above` here, with the
downstream instances as one-line corollaries.

### 4. The halting half of the reject path · medium

`Decomp.Reject` discharges the trapping half: a run that reaches a state with no
code at its pc never reaches an accepting halt. Panic machinery generally does
**not** trap — it reaches the `HALT` syscall with a nonzero `a0`, so it *is*
`SyscallHalted`, and no argument in that file touches it.

What it needs is `a0 ≠ 0` at those halts: a proof about *values* rather than
about control, and the first place this library would need vocabulary for
"every path from here carries a nonzero register". There is none.

*Acceptance:* a judgement that composes with `cpsSyscallHalt` and lets a caller
conclude "this region cannot halt with `a0 = 0`" from block-local facts.

### 5. The refinement layer (L3) · large

Every statement here is machine-level. Relating an extracted function to an
abstract specification needs an `nres`-like nondeterminism-with-failure monad, a
`⇓R` refinement relation, the two composition lemmas, and a predicate desugaring
to a `cpsTotal` triple.

It should be a separate `lean_lib` whose abstract half imports nothing from
`Rv64`, so it can be reused by a second project without dragging the machine in.

*Acceptance:* for one function, an abstract-correctness proof and a refinement
proof that are two separate, independently checkable theorems.

### 6. The extractor · large · research risk

The hand proofs are the point being tested, not the destination. A
proof-producing RV64 decompiler in Lean metaprogramming — per region, emit a
tail-recursive function, a side condition, and a certificate triple built from
the existing combinators — is what makes this scale. `riscv-zkvm`'s
`WP.GeneratedCFG`, `run_block` and `SpecDb` exist to receive exactly that.
Myreen's own HOL4 decompiler is ~2,200 lines of ML, ~500 architecture-specific.

The generator stays out of the trusted base because its certificates are
re-checked against the stepper.

*Acceptance:* the extractor reproduces a hand proof automatically, then handles
a second function nobody wrote by hand.

*Known risk:* computed branches defeat CFG recovery. Plan hand-written
`cpsNBranchWithin` certificates at indirect-jump sites.

### 7. Two genuinely divergent exits cannot be stated · design question

`cpsTotal` has a single exit address, so `cpsTotal_loopB` requires every `inr`
branch to reach one machine label, and the region must include whatever the
compiler put between the exits and the join. That is what compilers do, and it
is why the restriction has not bitten — but a region whose exits do not converge
has no statement here. The shape would be a total two-exit judgement, the
`cpsTotal` analogue of `cpsBranch`.

*Acceptance:* either the judgement, or a written argument that the convergence
requirement is the right one.

### 8. `COMMIT` is under-observed · upstream

`PartialState` has no `committed` component, so the `COMMIT` triple says `pc +=
4` and *nothing else observable changed* — true, and weak: no assertion can say
what was committed. Fixing it is an upstream change to `PartialState`.

*Acceptance:* an assertion that names the commit log, and a `COMMIT` triple that
says what was appended.

### 9. Toolchain: `riscv-zkvm` v4.33.0 → v4.33.1 · upstream ask

This library pins Lean v4.33.0 because `riscv-zkvm` does
(`fixedToolchain = true`). Anything that wants to share a toolchain with a
Mathlib-based project on v4.33.1 needs upstream to move first. Carried over from
`zip-2005-asm` issue #23.

### 10. Structural rules are added on demand

`Decomp.Triple` restates about 30 of upstream's ~60 `CPSSpec` lemmas. The rest
are fixed-arity WP frontends (`join2/3/4`, `weakenPosts2/3/4`,
`takenStripPure2/3`) shaped for another project's classifier. This is deliberate
— a rule with no consumer is a statement, not a capability — and it is recorded
here so nobody reads the gap as an oversight.

---

## Owed adversarial passes

`asm-adversary` sets `disable-model-invocation`, so only the user can run it. Two
statements were landed with the pass outstanding, both additive and reversible:

- **`RecB`'s shape.** Getting the datatype wrong would be expensive to undo.
  `Rec`, `TerminatesIn` and `cpsTotal_loop` are untouched beside it, so it can be
  withdrawn. The specific question: is `RunsTo.exit` taking `side x` — where
  `TerminatesIn.exit` takes none — the right departure from TR-765, or does it
  hide an obligation?
- **`SyscallHalted`.** It is stronger than `cpsHalt` and closer to the machine,
  but it is a *definition of accept*, and the whole reject-path argument rests on
  it. Worth attacking directly: is there a state that satisfies it and is not a
  halt, or a real halt it excludes?
