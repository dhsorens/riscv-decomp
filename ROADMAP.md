# Roadmap

The work queue and the honest list of what is missing. `README.md` is the
contract; this file is what the contract does not yet cover.

Read it today rather than from memory — nothing here is frozen.

---

## Where this is

The L2 layer works end to end. A loop whose trip count depends on its input can
be stated and proved with no fuel and no variant, on either backend, from one
proof (`Decomp.Examples.CountdownMachine`). The instruction leaves and the byte
regions are shaped for compiled code -- byte and wide stores into a region,
loads through one base register at an immediate offset, a source and a
destination region separated by `**` -- but no compiler-emitted consumer lives
in this repository yet.

Both loop rules now have a consumer in this repository: `Countdown` drives the
header-guarded `cpsTotal_loop`, and `FindIndex` drives `cpsTotal_loopB` through
both of its `inr` branches -- a top-of-body break and a bottom exit converging
on one label. Neither touches memory.

Above L2 there is now a first L3: `DecompRefine` (a separate library, no
machine in it) gives nondeterminism-with-failure specs and `⇓R` refinement, and
`Decomp.Refine` ties a certificate's extracted function to a spec and desugars
the pair to a `cpsTotal` triple against the spec. `FindIndex` is refined
against `searchSpec` in two theorems that do not know about each other;
`CountdownThenFind` is two regions glued by `Cert.seq`, refining a `bind` of
two specs, and against a looser spec that admits several answers. Item 5 has
the details; what it still lacks is a second project taking the abstract half
without the machine.

`lake build`: 101 jobs, zero warnings. `scripts/check-axioms.sh`: 1051
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
there is no region coupling and no `x & 7 = 0 ↔ index % 8 = 0` alignment
bridge, and no compiler emitted it. A compiler-emitted alignment loop over a
region would be the first *real* consumer, and would owe all three.

*Acceptance (met):* a proof in which two distinct `inr` branches of one `body`
are discharged. *Remaining:* the same against compiler output over a region.

### 2. The same-register keystone family is two instructions wide · leaf half landed, `LD` region form landed

`LBU rd, off(rd)` needed its own leaf all the way down — `lbu_same_on`,
`bytesRegionOn_lbu_same_at`, `bytesRegionSp1_lbu_same_at` — because the ordinary
keystone's postcondition keeps `rs1 ↦ᵣ ptr`, forcing `rd ≠ rs1`, and framing
cannot fake it: the footprint is genuinely two atoms rather than three.

The *leaf* half is done: `LB`, `LH`, `LHU`, `LW`, `LWU` and `LD` have
`*_same_on` (`Leaf/Mem.lean`) and `*_same_sp1Mem` (`Leaf/Sp1Mem.lean`), each a
mirror of its three-atom sibling with one `pull_second` fewer. They are
statements with no consumer.

The *region* half is partly done. **`LD` landed** — `bytesRegionOn_ld_at` and
`bytesRegionOn_ld_same_at` in `Region/Wide.lean`, with `bytesRegionSp1_ld_at` /
`_ld_same_at` as the SP1 instances — and it landed first because at an
8-aligned index it needs no `packBytes` algebra whatsoever: it reads one whole
cell, and the value is that cell's own chunk. Like `bytesRegionOn_sd_at`, which
it mirrors, it carries neither `halign` nor `hover`. That was not obvious from
this item's previous wording, which put every wide load behind the same
algebra.

The four narrow loads do need it: `LW`, `LWU`, `LH`, `LHU` and `LB` at a
sub-doubleword region index each need an *extract* out of the containing cell,
the other direction from `Region/Wide.lean`'s splicing stores. There is no
ordinary `bytesRegionOn_lw_at` yet, so there is nothing for a
`bytesRegionOn_lw_same_at` to mirror. That is the real remaining work.
`Region/Bytes.lean` says which layer is complete and which is not.

`packBytes_readback_setBytes_dword` is the check that the new load and the
existing `SD` agree about what a cell holds — needed by neither proof, which
is the point: they could disagree and both still typecheck.

**Which half:** the rule and its SP1 instance are here; the consumer is
downstream (`zip-2005-asm`, for a heap region).

*Acceptance:* the missing `_same_at` region forms, and a note in
`Region/Bytes.lean` saying the family is complete. *Landed so far:* the six
leaf twins, the `LD` region pair and both notes; the four narrow loads and
their twins remain.

### 3. The `OffText` discharges are restated per guest · **done**, consumer landed downstream

A store leaf takes `OffText lo hi addr w`. For a typical image that is free in
both directions — a heap above `.text` discharges the second disjunct, a stack
below it the first. `offText_of_below` and `offText_of_above`
(`Leaf/Sp1Text.lean`) now state that for any window; `offText_region_below` /
`_above` are the forms a loop body's store guard needs at byte `i` of a region,
on the bound the region keystones already carry. `offText_of_above` asks for a
word-aligned `hi`, which every real `.text` end has; `offText_of_above'` is the
raw form.

A guest's instances now are. `zip-2005-asm`'s `Guest/Text.lean` states
`offText_of_belowText` through `offText_region_below`, and `heapBase_offText`
and `offText_of_heap` through `offText_of_above` — three multi-line
`Nat`/`BitVec` arguments replaced by three applications, at this repository's
`bbc6d30` (that project's PR #44, open at the time of writing). Its
`offText_of_isValidDwordAccess` stays hand-proved and should: it is about
ZisK's zone map, not about a window.

*Acceptance (met):* `offText_of_below` and `offText_of_above` here, with a
guest's instances as one-line corollaries.

### 4. The halting half of the reject path · rules landed, no consumer

`Decomp.Reject` discharges the trapping half: a run that reaches a state with no
code at its pc never reaches an accepting halt. Panic machinery generally does
**not** trap — it reaches the `HALT` syscall with a nonzero `a0`, so it *is*
`SyscallHalted`.

`Accepted s := SyscallHalted s ∧ a0 = 0` is the observation that tells the two
apart — **as a convention**: `SyscallHalted` is the machine's event, but "`a0`
is the exit code and zero is success" is the host ABI (`Program.lean`'s `HALT`
macro, the interpreter's exit report), which the step relation does not know.
That convention is recorded in README "Trust", as a protocol definition rather
than a machine fact, and it is the one this library reasons about. Two rules
refute it: `not_accepted_of_cpsSyscallHalt` (from a
halt triple whose postcondition pins `a0`, composing with `halt_sp1Text` —
`not_accepted_of_halt_sp1Text` is the SP1 one-liner) and
`not_accepted_of_invariant` (`J` initially, `J` preserved by every step, `J →
¬Accepted`), with the run induction done once. The generic stuck-state lemma
`not_reaches_of_reaches_stuck` now covers both halves.

Neither rule has a consumer. A guest's panic path would owe a `cpsTotal` from
each panic entry to its `HALT` with `x10 ↦ᵣ 1` — a proof about values through
formatting code, which nothing here makes cheap.

*Acceptance (met, by the convention recorded in README "Trust"):* a judgement
composing with `cpsSyscallHalt` that concludes "this region cannot halt with
`a0 = 0`" from block-local facts. *Remaining:* the adversary pass on
`SyscallHalted`, which `Accepted` rests on, and a consumer.

### 5. The refinement layer (L3) · landed, one and two regions

`DecompRefine.Nres` is the abstract half: a spec is a may-fail flag plus a result set
(`fail` is the top of the order, so a precondition is a spec that fails outside
its domain), `conc R` is `⇓R`, and `refine_trans` / `bind_refine` are the two
composition lemmas. It imports nothing from `Rv64` or `Decomp`. `Decomp.Refine`
is the bridge: `Cert.Refines c spec R`, the desugaring `Cert.refines_sound` to a
`cpsTotal` triple whose postcondition names the spec and not `fn`, and
`Cert.Refines.seq` — `Cert.seq` refines `Nres.bind`, with `seq`'s side
condition `c₁.pre x ∧ c₂.pre (c₁.fn x)` being exactly what `bind` asks of the
continuation.

Two worked instances. `FindIndex`: `searchSpec_ok_iff` (abstract correctness,
on the `DecompRefine` side) and `result_refines` (refinement, about `result` alone)
are independent theorems, composed in `find_meets_spec`. `CountdownThenFind`:
two regions back to back, glued by `extendCode` / `frameR` / `seq` with one
`ac_rfl`, refining `pipelineSpec = bind countSpec searchSpec` through
`Cert.Refines.seq` from the two halves' own refinement theorems — the consumer
`bind_refine` was missing.

Nondeterminism is exercised too: `countSpecLe` accepts any value at or below
the start, `pipelineSpecLe` sequences the search after it and admits several
answers (`pipelineSpecLe_two_answers`), and the same two-region certificate
refines it (`cert_refines_le`) with only the first stage's refinement theorem
restated. The failure flag is used only as a precondition throughout, which is
what it is for.

What is missing: a second project. Every spec here was written next to the
code it describes; the layer's claim -- that the abstract half can be taken
without the machine -- is tested only when someone does so.

*Acceptance (met):* for one function, an abstract-correctness proof and a
refinement proof that are two separate, independently checkable theorems.

### 6. The extractor · large · research risk · M0–M3 landed

The hand proofs are the point being tested, not the destination. A
proof-producing RV64 decompiler in Lean metaprogramming — per region, emit a
tail-recursive function, a side condition, and a certificate triple built from
the existing combinators — is what makes this scale. `riscv-zkvm`'s
`WP.GeneratedCFG`, `run_block` and `SpecDb` exist to receive exactly that.
Myreen's own HOL4 decompiler is ~2,200 lines of ML, ~500 architecture-specific.

The generator stays out of the trusted base because its certificates are
re-checked against the stepper. Everything it computes *about a program* is a
`#guard`, never a theorem; the two theorems in `Extract/Body.lean` are about
the generator's own model of the instructions, not about any program.

*Milestones:*

- **M0 — control-flow recovery · done.** `Decomp.Extract.CFG`: basic blocks,
  back edges, loop membership (as an address interval, named so), exits, and
  the *shape* each loop wants — header-guarded (`cpsTotal_loop`), body exits
  that converge through pure-jump blocks (`cpsTotal_loopB`, region extended by
  those blocks), or body exits that do not (`cpsTotal_loopB_exits`). On the two
  hand-proved programs it reproduces the analysis their headers give in prose,
  including the `JAL` `FindIndex`'s region has to include. `JALR` is flagged,
  not followed.
- **M1 — the abstract body · done.** `Decomp.Extract.Body`: from a loop's
  blocks, the `RecB RegFile Exit` over a register file — each block's ALU
  instructions evaluated symbolically into a function on `Reg → Word`
  (`execPlain`, with `execInstrBr`'s semantics: `execPlain_regs`), the branch
  conditions as the `inl`/`inr` split (`branchTaken`, `nextPc`:
  `terminal_step`), exits resolved through pure-jump blocks so the label is
  what `cpsTotal_loopB_exits` wants. The body is total by construction; its
  fallback (`inr` at the current pc) is sound but useless, and `wellFormed`
  is the static check meant to keep every path off it. `emitBody` refuses
  loads, stores, syscalls, `JALR`, calls and nested loops. On `Countdown` and
  `FindIndex` (with and without the `JAL`) the emitted bodies agree with the
  hand-written `countdown` and `find` on every checked input. Not done: the
  `*W` and M-extension ALU forms (a longer `match`, no new idea), and
  `wellFormed = true → no run reaches the fallback`, which is unproved; a
  false positive costs a sound, useless certificate.
- **M2 — the certificate · done, and stronger than planned.** The plan was
  to emit `hCont` / `hExit` per loop and discharge them by a tactic. What
  landed is one theorem, `Decomp.Extract.Cert.emitBody_sound`: *every* body
  the emitter produces is sound, on any `PlainAgree` stepper, with no
  per-loop proof at all. A run of the emitted body that returns `y` is a
  `cpsTotal` from the header to `y.label`, taking the coupling `regsAssn rs`
  (the separating conjunction of `x ↦ᵣ r.get x` over a register list `rs`
  that covers the footprint) from `x` to `y.regs`. The side condition is
  `True` — the register file is an exact abstraction, so the
  representability facts the hand proofs carried were the price of `Nat`,
  not of the machine. Two generic leaves (`cpsWithin_alu`,
  `cpsWithin_terminal`) are proved straight from `execInstrBr` and upstream's
  frame-preserving register update, then the walk is followed by induction
  (`stepBlock_sound`, `runPass_sound`, `resolveJumps_sound`). The theorem asks
  two `Bool`s of the program — `passOk` (loop blocks resident and within the
  coupling) and `jumpsOk` (pure-jump blocks resident and honest) — which the
  three instances (`countdown_extracted`, `findIndex_extracted`,
  `findIndex_div_extracted`) discharge by `decide` at a fixed base. Not done:
  a `Cert` for it (`Cert.exit_` is one label, an extracted exit is
  `Exit.label`; item 7's `exit_ : β → Word` now has its consumer), and a
  lemma that `blocks base prog` always satisfies the two `Bool`s against
  `CodeReq.ofProg base prog`, which is what would make the instances
  base-generic instead of `decide`d at `0x1000`.
- **M3 — acceptance · done, at a fixed base.** `Decomp.Extract.Reproduce`
  relates `RunsTo (bodyOf findIndexProg)` to `RunsTo (find stop e)` under the
  coupling `x10 = i, x11 = stop, x12 = e` (`runsTo_lift`, an induction on the
  hand body's derivation with one case per equation of the emitted body), and
  `find_found` / `find_exhausted` at the emitter's base then fall out of
  `findIndex_extracted` in a few lines each (`find_found_extracted`,
  `find_exhausted_extracted`): same program, same coupling `I`, same
  conclusion, none of the hand proof's five leaves. The side condition
  `i + 1 < 2 ^ 64` reappears because relating a `Nat` abstraction to a
  register file needs `BitVec.ofNat` injective on the values in play; the
  extracted certificate itself has none. `Decomp.Extract.SumDown` is the
  second function nobody wrote by hand — `BEQ x10, x0; ADD x11, x11, x10;
  ADDI x10, x10, -1; JAL` — with no `SumDownMachine.lean`: the machine
  certificate is `emitBody_sound` at the program (`sumDown_extracted`), two
  equations are read off the emitted body (`sd_exit`, `sd_cont`), an
  induction on the counter gives `sd_runsTo`, and `sumDown_correct` is the
  corollary, for every representable `n` on both backends. Not done: the
  results are at the emitter's base `0x1000` where the hand theorems are for
  every base (the base-generic `blocks` lemma from M2's list is what would
  lift them); the equations of the emitted body are still read off by hand
  from the emitted function — proved by running the walk symbolically block
  by block, which is the step a `simp` set for single-loop programs would
  automate; and the M2 list stands (a `Cert` with `exit_ : β → Word`, the
  `*W` and M-extension ALU forms).

*Known risk:* computed branches defeat CFG recovery. M0 reports them
(`LoopInfo.hasIndirect`); plan hand-written `cpsNBranchWithin` certificates at
indirect-jump sites.

### 7. Two genuinely divergent exits · resolved

`cpsTotal` has a single exit address, and `cpsTotal_loopB` fixed it before the
body ran, so every `inr` branch had to reach one label. That was an artifact of
the order of quantification, not of the judgement: the rule's conclusion is
about one derivation `RunsTo r side n x y`, and `y` says which exit was taken,
so the label may be `exitOf y`. `cpsTotal_loopB_exits` is that rule, with the
same four-line proof; `cpsTotal_loopB` is now its constant-label instance.

Decision recorded so it is not rebuilt: a two-exit total judgement with
existential arms (the `cpsTotal` analogue of `cpsBranch`, derived from the loop
rule for a caller holding only `TerminatesB`) was built and withdrawn. Its arms
could only say "some output tagged this way reached this label", which is not
the form this library wants; the exit-per-output loop rule is the answer, and a
caller who wants pinned arms takes the derivation.

Consumer: `FindIndex` with the region ending before the `JAL` — `find_found_div`
to `base + 16`, `find_exhausted_div` to `base + 12`, nothing joining them. The
`JAL` stays **resident** in `cr` (the four residency lemmas are stated over the
four-instruction program) and is never executed; a three-instruction `cr` would
be the stricter test of "nothing between them in the region" and has not been
done. `Cert` still has one `exit_`; a certificate for divergent exits would
carry `exit_ : β → Word`. The extractor now asks: `Extract/Cert.lean`'s
`emitBody_sound` has an exit label per output and no `Cert` to sit in.

*Acceptance (met):* either the judgement, or a written argument that the
convergence requirement is the right one. The argument above — the requirement
was never the machine's — closes the item, with `cpsTotal_loopB_exits` as the
rule.

### 8. `COMMIT` is under-observed · upstream

`PartialState` has no `committed` component, so the `COMMIT` triple says `pc +=
4` and *nothing else observable changed* — true, and weak: no assertion can say
what was committed. Fixing it is an upstream change to `PartialState`.

*Acceptance:* an assertion that names the commit log, and a `COMMIT` triple that
says what was appended.

### 9. Toolchain: `riscv-zkvm` v4.33.0 → v4.33.1 · upstream ask

This library pins Lean v4.33.0 because `riscv-zkvm` does
(`fixedToolchain = true`). Anything that wants to share a toolchain with a
Mathlib-based project on v4.33.1 needs upstream to move first.

### 10. Structural rules are added on demand

`Decomp.Triple` restates about 30 of upstream's ~60 `CPSSpec` lemmas. The rest
are fixed-arity WP frontends (`join2/3/4`, `weakenPosts2/3/4`,
`takenStripPure2/3`) shaped for another project's classifier. This is deliberate
— a rule with no consumer is a statement, not a capability — and it is recorded
here so nobody reads the gap as an oversight.

---

## Owed adversarial passes

`asm-adversary` sets `disable-model-invocation`, so only the user can run it.
Three statements were landed with the pass outstanding, all additive and
reversible:

- **`RecB`'s shape.** Getting the datatype wrong would be expensive to undo.
  `Rec`, `TerminatesIn` and `cpsTotal_loop` are untouched beside it, so it can be
  withdrawn. The specific question: is `RunsTo.exit` taking `side x` — where
  `TerminatesIn.exit` takes none — the right departure from TR-765, or does it
  hide an obligation?
- **`Accepted`** (`Decomp/Reject.lean`). `SyscallHalted ∧ a0 = 0` installs a
  semantic accept boundary the step relation cannot justify on its own: that
  `a0` is the exit code and zero means success is the host ABI. The convention
  question — is this the *verifier's* acceptance event? — was put to the user
  and answered: it is the protocol's accept, not the machine's, and a prover
  proves any `HALT` (README "Trust"). What the pass still owes is the machine
  side, the `SyscallHalted` bullet below, on which `Accepted` rests. Raised by
  the review of PR #10.
- **`SyscallHalted`.** It is stronger than `cpsHalt` and closer to the machine,
  but it is a *definition of accept*, and the whole reject-path argument rests on
  it. Worth attacking directly: is there a state that satisfies it and is not a
  halt, or a real halt it excludes?
- **`emitBody_sound`** (`Extract/Cert.lean`). The one theorem the extractor's
  machine content rests on: M3's triples are all this theorem applied to an
  abstract `RunsTo`. Additive and reversible. The seam: `regsOf` against the
  operands each constructor reads and writes; a missed operand fails
  `aluOf_congr` / `aluOf_dest`, not the theorem. Named as the thing to attack
  by the review of PR #21; the pass has not run.
