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

Above L2 there is now a first L3: `Refine` (a separate library, no machine in
it) gives nondeterminism-with-failure specs and `⇓R` refinement, and
`Decomp.Refine` ties a certificate's extracted function to a spec and desugars
the pair to a `cpsTotal` triple against the spec. `FindIndex` is refined
against `searchSpec` in two theorems that do not know about each other. What is
still missing there is a program of several regions -- `bind_refine` has no
consumer (item 5).

`lake build`: 95 jobs, zero warnings. `scripts/check-axioms.sh`: 563
declarations on the three documented axioms. (The move to the module system
took 28 compiler-generated `match_*` matchers out of the census; they are
internal under `module` and carry no proof of their own.)

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

### 2. The same-register load family is complete at the leaf layer · done

`LBU rd, off(rd)` needed its own leaf all the way down — `lbu_same_on`,
`bytesRegionOn_lbu_same_at`, `bytesRegionSp1_lbu_same_at` — because the ordinary
keystone's postcondition keeps `rs1 ↦ᵣ ptr`, forcing `rd ≠ rs1`, and framing
cannot fake it: the footprint is genuinely two atoms rather than three.

`LB`, `LH`, `LHU`, `LW`, `LWU` and `LD` now have the same twin at both leaf
layers (`*_same_on` in `Leaf/Mem.lean`, `*_same_sp1Mem` in `Leaf/Sp1Mem.lean`),
each a mirror of its three-atom sibling with one `pull_second` fewer. They are
statements: nothing consumes them yet, and only `LBU`'s has ever been needed.

At the *region* layer nothing changed, and the note in `Region/Bytes.lean` says
why: the byte-indexed keystones are `LBU`/`SB` only, so there is no ordinary
`bytesRegionOn_lw_at` for a `_same_at` to mirror. A wide load at a region index
is a separate item, wanted only when a consumer asks.

*Acceptance (met):* the six missing forms and the note.

### 3. The `OffText` discharges live here now · done

A store leaf takes `OffText lo hi addr w`. For a typical image that is free in
both directions — a heap above `.text` discharges the second disjunct, a stack
below it the first. `offText_of_below` and `offText_of_above` (`Leaf/Sp1Text.lean`)
state that for any window; `offText_region_below` / `_above` are the forms a
loop body's store guard needs at byte `i` of a region, taking the bound the
region keystones already carry. `offText_of_above` asks for a word-aligned
`hi`, which every real `.text` end has; `offText_of_above'` is the raw form.

The downstream instances are not yet rewritten as corollaries — that is a
downstream change, and the `example`s next to the lemmas stand in for it at
realistic numbers.

*Acceptance (met here):* the four lemmas. *Remaining downstream:* replace the
per-guest restatements with one-line instances.

### 4. The halting half of the reject path · rules landed, no consumer

`Decomp.Reject` discharges the trapping half: a run that reaches a state with no
code at its pc never reaches an accepting halt. Panic machinery generally does
**not** trap — it reaches the `HALT` syscall with a nonzero `a0`, so it *is*
`SyscallHalted`.

`Accepted s := SyscallHalted s ∧ a0 = 0` is now the observation that tells the
two apart, and two rules refute it: `not_accepted_of_cpsSyscallHalt` (from a
halt triple whose postcondition pins `a0`, composing with `halt_sp1Text` —
`not_accepted_of_halt_sp1Text` is the SP1 one-liner) and
`not_accepted_of_invariant` (`J` initially, `J` preserved by every step, `J →
¬Accepted`), with the run induction done once. The generic stuck-state lemma
`not_reaches_of_reaches_stuck` now covers both halves.

Neither rule has a consumer. The guest whose panic path motivated them is
downstream, and what it owes is a `cpsTotal` from each panic entry to its
`HALT` with `x10 ↦ᵣ 1` — a proof about values through formatting code, which
nothing here makes cheap.

*Acceptance (met):* a judgement composing with `cpsSyscallHalt` that concludes
"this region cannot halt with `a0 = 0`" from block-local facts. *Remaining:* a
consumer, downstream.

### 5. The refinement layer (L3) · landed for one function

`Refine.Nres` is the abstract half: a spec is a may-fail flag plus a result set
(`fail` is the top of the order, so a precondition is a spec that fails outside
its domain), `conc R` is `⇓R`, and `refine_trans` / `bind_refine` are the two
composition lemmas. It imports nothing from `Rv64` or `Decomp`. `Decomp.Refine`
is the bridge: `Cert.Refines c spec R` and the desugaring `Cert.refines_sound`
to a `cpsTotal` triple whose postcondition names the spec and not `fn`.

The worked instance is `FindIndex`: `searchSpec_ok_iff` (abstract correctness,
on the `Refine` side) and `result_refines` (refinement, about `result` alone)
are independent theorems, composed in `find_meets_spec`.

What is missing: a consumer for `bind_refine`. One loop against one spec never
sequences, so the lemma that makes the layer scale to a program of several
regions is a statement without a consumer, and `Cert.seq` and `Nres.bind` have
not been shown to line up. That is the next slice here, and it wants a
two-region example.

*Acceptance (met):* for one function, an abstract-correctness proof and a
refinement proof that are two separate, independently checkable theorems.
*Remaining:* `bind_refine` against `Cert.seq`.

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

### 7. Two genuinely divergent exits · resolved

`cpsTotal` has a single exit address, and `cpsTotal_loopB` fixed it before the
body ran, so every `inr` branch had to reach one label. That was an artifact of
the order of quantification, not of the judgement: the rule's conclusion is
about one derivation `RunsTo r side n x y`, and `y` says which exit was taken,
so the label may be `exitOf y`. `cpsTotal_loopB_exits` is that rule, with the
same four-line proof; `cpsTotal_loopB` is now its constant-label instance.

The two-exit total judgement the question asked about, `cpsTotalBranch`, exists
too (`Triple.lean`, with `of_cpsBranch`, the two injections, `weaken` and the
join) and is *derived* from the loop rule for a caller holding only
`TerminatesB` (`cpsTotalBranch_of_loopB`), its arm postconditions existentially
quantified over the outputs that reach each label.

Consumer: `FindIndex` with the `JAL` cut off the region — `find_found_div` to
`base + 16`, `find_exhausted_div` to `base + 12`, nothing joining them, and
`find_branch` as the two-exit form. `Cert` still has one `exit_`; a certificate
for divergent exits would carry `exit_ : β → Word`, and nothing has asked.

*Acceptance (met):* the judgement, and the argument — the convergence
requirement was never the machine's.

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
