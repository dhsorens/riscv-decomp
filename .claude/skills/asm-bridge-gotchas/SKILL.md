---
name: asm-bridge-gotchas
description: >
  Hard-won RV64 / SP1 decompilation pitfalls. Use when proving or
  debugging triples, leaves, byte regions or loop rules, stuck memory
  or halt observations, or before adding a precondition to a triple.
disable-model-invocation: true
---

# Asm bridge gotchas

Living document of failure modes. Add an entry when a session burns
time on a recurring trap. Hunts stay in `asm-adversary`.

Seeded from scars carried over from `zip-2005-asm`, where this library
was extracted from. Status belongs in `ROADMAP.md` — do not treat this
file as the plan.

## Observation and I/O

- **Halted is not accepted, and `cpsHalt` cannot tell them apart.**
  `(st.next s').isNone` is true of a real `HALT` *and* of every trap:
  no code at the pc, `.CSRS`, `.EBREAK`, a failed `memOkSp1`. Use
  `SyscallHalted` / `cpsSyscallHalt` for anything that has to
  distinguish the two — a reject-path argument above all. README
  "Observations" is the finding.
- **Hint framing.** Under the SP1 backend, `--input` is framed
  (length then payload). A raw blob is a different guest.
- **`COMMIT` (`0x10`) is not `write_output`.** SP1's `COMMIT(index,
  word)` is not a ptr+size write. Misreading it as a byte count has
  already crashed a host run.
- **Unmodelled ecall.** If dispatch continues instead of trapping, a
  run that reaches halt is not evidence. Re-read the current `step`
  arm; do not trust an old coverage table.

## Model and Lake

- **`lake build` resets `.lake/packages/<dep>`** to
  `lake-manifest.json`. A hand checkout of a newer rev is silently
  reverted. Uncommitted edits survive; moving HEAD does not. Re-pin
  with `lake update`.
- **Do not edit the Lake `riscv-zkvm` tree** to make a triple hold.
  Vendor or upstream.
- **Precompiles are the model, not the asm.** A wrong `Accel`
  function at the guest's curve/field ids is a wrong answer. No
  per-function RISC-V triple catches it.

## Module system

- **A `module` cannot import a legacy file, and upstream's aggregators
  are legacy.** `import RiscvZkvm.Rv64` / `RiscvZkvm.Rv64.Logic` fail
  from a `module` with "cannot import non-`module`". Use
  `public import Decomp.Upstream`, which re-exports their module-system
  contents; the legacy stragglers (`CPSCall`, `MemSat`,
  `CodeReqExtents`, `WP.Examples`, `Tactics.WP`) are listed in its
  header and nothing here uses them.
- **`#guard` needs `meta import`, transitively.** "Invalid `meta`
  definition … `X` is not accessible here" means the check *runs* `X`;
  add `meta import <module defining X>`. "Could not find native
  implementation of external declaration `Y`" is the same thing one
  level down -- `Y` is called by `X` and lives in a module you did not
  meta-import (`hintRead` → `dwordBytes` in `MemRegionWriteWide`,
  `packBytes` in `ByteOps`). Private `meta import` is enough; nothing
  downstream needs the code.
- **Under `module`, the axiom census shrinks by the `match_*`
  matchers.** They are internal now and were never proofs. Compare
  names, not counts, when the number moves after a structural change.

## Proving over the SP1 stepper

- **Transfer, don't restate.** A one-step ZisK `cpsTripleWithin` already
  pins its successor state, so `Myreen.cpsWithin_of_zisk_one` turns any
  upstream leaf into a leaf on any `Stepper` given `st.next s = step s`
  on the pre-states (`AgreesOn`). Plain instructions: `Stepper.PlainAgree`,
  both backends have it. Loads: `stepSp1_eq_step_l*` — ZisK's address map
  is inside SP1's, so the ZisK cell's validity witness is enough. Stores:
  `stepSp1_eq_step_s*` need `noCodeAt`, which nothing in a pre-state can
  supply. Never copy a leaf proof body.
- **A transferred spec keeps its cells, and `↦ₘ` is unsatisfiable off
  ZisK's zones.** `memIs a v` *requires* `isValidDwordAccess a` inside the
  resource, so at `0x78040618` (this guest's heap) no partial state
  inhabits it — `Examples/GuestHeap.lean` proves both directions. Specs
  about the SP1 heap must be stated with `memIsSp1` (riscv-zkvm PR #12)
  and proved directly, `memIsOn`-generically.
- **`code` is a separate map from `mem`.** So `code_next`-style
  preservation holds structurally for anything built from
  `setReg`/`setMem`/`setPC`, and `Myreen.code_stepSp1` proves it for
  SP1. That is *not* the same as "the instruction stream is intact": a
  store into the text window updates `mem` while `code` still matches.
  Keeping the two in step is the backend's store guard's job — the
  `noCodeAt` conjunct of `memOkSp1` asks the `code` map directly, and
  since PR #12 `hintWindowOk` asks it of `HINT_READ`'s whole write window.
  See `StepOn.lean`'s header. (There is no `storeOkSp1`; an earlier
  version of this note and of upstream's header named one.)

## Tactics, on this model

- **`repeat' split at h` walks past the dispatch you meant.** Proving
  `code_stepSp1`, a greedy `repeat'` ran off the end of SP1's six-deep
  ecall chain and into `execSp1Accel`'s own `match`, leaving goals whose
  hypotheses were shaped differently from the arms written for them.
  Write the splits out. Bounded and explicit beats clever here.
- **`split` cannot see through `have` in a term.** `sp1Ecall` and
  `hintRead` bind intermediates with `have`, so `unfold f at h; split at h`
  fails with "Could not split an `if` or `match`". Use
  `simp only [f] at h` instead — it zeta-reduces first.
- **Adding a `def` to a `simp` set can defeat its own `@[simp]`
  lemmas.** `simp [MachineState.setPC]` unfolds `setPC` into a structure
  literal, after which `code_setPC` no longer matches and the goal
  stalls. Reach for the projection lemmas (`code_setPC`,
  `code_setReg`, `code_execInstrBr`, `code_execSp1Accel`) and leave the
  definitions folded.
- **`simp only [SP1_MAX_MEMORY, …]` strands `decide`.** Unfolding the
  constant inside `decide (a.toNat < SP1_MAX_MEMORY) = true` leaves a
  form `decide_eq_true_eq` no longer fires on, and `omega` then sees an
  opaque `decide`. `unfold isValidMemAddrSp1 SP1_MAX_MEMORY at h` first,
  then `simp only [Bool.and_eq_true, decide_eq_true_eq] at h`, works.
  The ZisK constants are `@[implicit_reducible]` and do not have this
  problem, which is why `MemSat.lean`'s originals look different.
- **`simp` unfolds `isAligned4` in the goal but not in the hypothesis.**
  `simp [memOkSp1_lw, hvalid.2]` with `hvalid.2 : isAligned4 a = true`
  rewrites the goal to `a.toNat % 4 = 0` and reports the argument unused.
  `rw [memOkSp1_lw, Bool.and_eq_true]; exact ⟨_, hvalid.2⟩` keeps both
  sides folded.
- **`align4` is `&&& ~~~3#64`, and `bv_omega` cannot see through `&&&`.**
  `(align4 a).toNat = a.toNat - a.toNat % 4` (`Myreen.toNat_align4`) is
  proved bit by bit: `Nat.eq_of_testBit_eq` with `testBit_and`,
  `testBit_shiftLeft`, `testBit_two_pow_sub_one`, `testBit_div_two_pow`,
  after rewriting `~~~3#64` as `(2^62 - 1) <<< 2` by `decide`. Reuse it
  rather than re-deriving; everything about `noCodeAt` bottoms out here.
- **The sub-dword leaf proofs never look at the cell's validity.** Upstream's
  `generic_lbu/lw/lh/sb/sw/sh_spec_within` take the containing doubleword's
  cell plus `halign`, and the address predicate is a *separate* hypothesis
  fed to `step_*`. So re-proving them over `memIsOn valid` is a textual
  substitution (`Myreen/Leaf/Mem.lean` was generated that way); only
  `LD`/`SD` read validity out of the cell. Put backend side conditions
  (`isAligned4`, `noCodeAt`) in the `hst` caller, not the leaf.
- **`memIsSp1` is an `abbrev`, so it unifies with `memIsOn valid`.** An
  instance of a `memIsOn`-generic leaf at `memIsSp1` needs no rewriting;
  `valid` is inferred. The `pcFree` tactic does not know `memIsOn` --
  pass `pcFree_memIsOn` explicitly.
- **`variable {lo hi : Nat}` eats the customary `hi : i < bs.length`.** With
  the window bounds as section variables, a hypothesis named `hi` shadows
  `hi : Nat` and `Sp1Text lo hi` / `OffText lo hi` get a `Prop` where they
  want a `Nat` ("expected to have type `Nat`"). Name the bound `hlt`.
- **The region keystones are cell-agnostic too.** Upstream's
  `bytesRegion_lbu_within` / `_sb_within` are dword-framing + one leaf +
  `extractByte_packBytes` / `packBytes_set`; only the framing lemmas mention
  the cell. `Myreen/Region/Bytes.lean` restates them over `bytesRegionOn
  valid` and `Myreen/Leaf/Mem.lean`'s leaves with the same text. `xperm_hyp`
  treats `memIsOn valid a v` and `bytesRegionOn valid b bs` as atoms, so the
  permutation steps need no change.
- **`SD` into a region at an 8-aligned index needs no `halign`/`hover`.**
  Upstream's `bytesRegion_sw_at_within` carries `regionBase.toNat % 8 = 0` and
  a no-wrap bound because `SW` reads the containing dword back through
  `alignToDword`/`byteOffset`. An aligned `SD` hits the region's own cell
  (`regionBase + 8k`) and replaces it, so `bytesRegionOn_sd_at` drops both --
  the linter told us, and the tighter statement is the true one. Do not copy
  `SW`'s hypothesis list onto `SD` out of habit.
- **`HINT_READ` writes `n / 8 + 1` doublewords, and the proof should see one
  write, not two.** The model writes the payload with `writeBytesAsWords` and
  then the remainder word with a separate `setMem`. Do not follow it: prove
  the two-phase write equal to one `writeBytesAsWords` of the zero-padded
  payload (`writeBytesAsWords_pad`, both residues) and induct once over the
  region's cells. `packBytes bs = bytesToWordLE bs` is `rfl` after unfolding
  -- the "missing readback lemma" was never missing. Pin the extent with
  `#guard`s that *run `hintRead`* on a probe `MachineState` and read cells
  back; a `#guard` on your own padding function only checks itself.
- **`exact nomatch hv, hib` eats the next tuple component.** `nomatch`
  accepts several discriminants, so inside an anonymous constructor the
  comma after it is parsed as a second discriminant and the constructor
  comes up one field short, with a confusing "expected `A ∧ B`" mismatch.
  Parenthesise the `fun`.
- **Never state an SP1 triple that contains a store on `cpsWithinOn .sp1`.**
  `Backend.stepper .sp1` has `inv := True`; on states with junk code at
  the target `stepSp1` traps, so the theorem is *false*, not vacuous.
  State it on `Sp1Text` / `GuestText.Sp1Guest` and lift plain/load
  results into it with `cpsWithin_sp1Text_of_sp1`. Nothing in the type
  of `cpsWithinOn` warns you.
- **A store triple on SP1 needs `Stepper.inv`, and the invariant is a
  property, not `s.code = imageCode`.** `imageCode` covers three
  functions; the machine's `code` covers `.text`. `CodeWithin lo hi` is
  true of real states and is exactly what `noCodeAt` needs
  (`Myreen/Leaf/Sp1Text.lean`). Destructure `OffText` before `omega` --
  it is a `def`, and `omega` will not unfold it.
- **Mathlib is not a dependency of the machine side today, but it may
  be one.** `by_contra`, `Nat.find`, `f^[n]` / `Nat.iterate`, `norm_num`
  extensions and `exact?`-found Mathlib names are absent from the root
  package. Derek (2026-09-09): adding Mathlib is fine, *targeted* -- a
  few `import Mathlib.<Module>` lines, pulled from the cache (`lake exe
  cache get`), not `import Mathlib`. Until someone does, reach for
  `cases h : e with | none => …` or `Classical.byContradiction`, own
  `Rec.iterate`, and core lemmas (`Nat.eq_of_testBit_eq`,
  `Nat.testBit_*`); budget one probe file per unfamiliar lemma name. If
  a slice is spending real time re-deriving a Mathlib lemma, add the
  dependency instead -- `spec/` already pins Mathlib, so M1a's toolchain
  reconciliation is the thing to coordinate with.
- **`variable (h : P)` is not included in a proof that only uses `h` in
  its body.** Lean 4 includes section variables by *statement* mention.
  A hypothesis like `hst : st.PlainAgree` that only the tactic block
  needs must be an explicit binder (or `include`d, which drags it into
  every later declaration — wrong for the address-arithmetic lemmas
  sharing the section).

## Proving over a region

- **Choose the coupling's parenthesisation to match the leaves — while
  you still can.** For a 2–3 atom loop invariant, group it so each
  leaf's footprint is one whole sub-term:
  `(ptr ** val ** region) ** (counter ** x0)` lets the `SB` step be
  `frameR` and the `BNE` step be `frameL`, with no separating-conjunction
  permutation anywhere (`Examples/MemsetTail.lean`).
- **Past ~4 atoms, stop trying and let `xperm` do it.** A block that
  touches six registers and two regions has a different footprint at
  every step and no single parenthesisation fits them all. The cheap,
  mechanical shape is one *fixed atom order* for the whole block, and at
  each step frame with the complement in that same order and
  `cpsWithin_weaken (fun _ hp => by xperm_hyp hp) (fun _ hp => by xperm_hyp hp)`
  on both ends (`Examples/MemcpyTail.lean`, nine steps, nine atoms).
  `xperm_hyp` is not a symptom of a bad grouping at that size.
- **The state assertion must be an `abbrev`, not a `def`.** `xperm`
  normalizes at *reducible* transparency only, so it cannot see the
  `**` chain through a plain `def` and fails with an atom-count
  mismatch. `abbrev` (as `bytesRegionSp1` itself is) or `simp only [St]`
  at every use — the first is less noise.
- **`pcFree` does not know about regions.** The tactic closes register
  and pure conjuncts; a frame containing `bytesRegionSp1` needs
  `bytesRegionOn_pcFree` by hand. For a loop invariant, state it once as
  a named lemma; for a block with a different frame at every step, a
  local `macro` of
  `repeat (first | exact pcFree_regIs | exact bytesRegionOn_pcFree _ _ _ | apply pcFree_sepConj)`
  closes all of them.
- **`rd = rs1` needs its own leaf, all the way down — framing cannot
  fake it.** A load whose destination *is* its address register
  (`LBU x11, 0(x11)`, `memcpy` index 507) cannot use the ordinary
  keystone: `bytesRegionOn_lbu_at`'s postcondition keeps
  `rs1 ↦ᵣ ptr`, so it forces `rd ≠ rs1`. The instinct is to reach for
  a frame, and it does not work, because the footprint is genuinely
  **two** atoms (register, region) rather than three — after the load
  the pointer is gone. Write the same-register form at each layer
  (`lbu_same_on`, `bytesRegionOn_lbu_same_at`,
  `bytesRegionSp1_lbu_same_at`), which is the shape upstream already
  uses for the register leaves (`ld_spec_same_within`). Each is a
  ten-line mirror of the three-atom proof with one less assoc step.
  And be honest in the postcondition: it cannot say where the pointer
  is, because nothing does.
- **Prove the shared prefix once, with the branch's input left
  symbolic.** Two paths that differ only in which way a `BEQ` goes
  should not be two copies of the block in front of it. State the
  prefix with the tested register as an expression (`x12 = cnt &&& 1`,
  not `0`), then make the branch its own one-instruction lemma over an
  *arbitrary* register state — `beq_zero_taken` / `beq_nonzero_notTaken`
  in `Examples/MemcpyTail.lean`. The callers rewrite the parity fact in.
- **A region owns *dword* cells, not byte cells.** `bytesRegionOn` is
  `⌈|bs|/8⌉` consecutive dwords from a dword-aligned base, so `**`
  between two regions asks for disjoint dword-*rounded* spans — strictly
  more than byte non-overlap. Safe direction (the caller owes more), but
  say so in the statement's prose instead of writing "exactly
  non-overlap", and check the precondition still has an inhabitant at
  the instance you care about.
- **`ADDI rd, rs1, 0` does not simplify by `rw [BitVec.add_zero]`.** The
  leaf leaves `v + signExtend12 0`, whose `0` is not syntactically
  `0#64`. State `a + signExtend12 (0x000 : BitVec 12) = a` once, by
  `show a + (0 : Word) = a; bv_omega`, and rewrite with that.
- **A lookup deep into a long `Program` literal needs
  `set_option maxRecDepth`.** `CodeReq.ofProg_lookup_addr` at index 498
  of `memcpy` reduces 498 `cons` cells in the kernel; the default depth
  fails with "maximum recursion depth" at the *first* such lemma and
  then cascades into `unknown constant` errors for everything after it.
  10000 is enough for a 510-instruction function.
- **`OffText` is a disjunction, so pick the disjunct.** `omega` will not
  choose between "the access ends below `lo`" and "`hi` is below the
  aligned address", and fails with a counterexample that looks like an
  arithmetic gap. `exact ⟨_, Or.inl _⟩` for anything below `.text` (the
  stack), `Or.inr` for anything above it (the heap).

## Proving a loop

- **Pick the rule by where the guard is, not by how the loop looks.**
  `cpsTotal_loop` (over `Rec`) wants the guard at the *header* and a body
  that is a straight line back to it. `cpsTotal_loopB` (over `RecB`,
  `body : α → α ⊕ β`) wants neither: the body decides for itself
  whether to continue. Anything the compiler emitted with an early
  `break`, and anything bottom-guarded, wants `loopB`.
- **Do not rotate a do-while by hand.** Sequencing an unrolled body pass
  in front of `cpsTotal_loop` works, but it costs an extra obligation
  and an extra composition step, and `cpsTotal_loopB` gets the same
  theorem with the region's entry equal to the guest's entry
  (`Examples/MemsetTail.lean` was rewritten from the first shape to the
  second and got shorter).
- **`RecB`'s side condition is checked at the exit state too.** Unlike
  `TerminatesIn.exit`, `RunsTo.exit` takes `side x` — the body *runs* on
  the way out. So a `side` that was fine for `cpsTotal_loop` may need a
  conjunct (`0 < m`, typically) before it will drive `cpsTotal_loopB`.
- **Two `inr` branches need not reach the same machine label.**
  `cpsTotal_loopB` fixes one `exit_`, so with it the region must include
  whatever the compiler put between the exits and the join (in `memcpy`,
  a `JAL`). `cpsTotal_loopB_exits` takes `exitOf : β → Word` instead and
  needs no join; use it when the exits genuinely diverge, and
  `cpsTotalBranch_of_loopB` when the caller has only `TerminatesB`.
- **The obligations are quantified over *every* abstract state, not the
  reachable ones.** Each conjunct of `side` is usually load-bearing for
  exactly one obligation off the reachable path; if an obligation looks
  false, ask which conjunct is missing before doubting the rule.

## Anti-patterns

| temptation | do this instead |
| --- | --- |
| Success-only triple "for now" | Relate reject/trap too, or ledger why not |
| Restrict the relation until both sides agree | Mismatch ledger first |
| Add `axiom` for a stuck lemma | Compiling `sorry`; or restate. Never silent axioms |
| Leave unused-hyp warnings | Tighten the statement |
| Treat a green `run-guest.sh` as soundness | Ask what observation actually implies |
| Prove a function that never retires | Rank against a measurement downstream — but you still owe it a triple or a reject-path argument |
| Read `0 retired` as dead code | Unreached is not unreachable |

## How to extend

When you lose >15 minutes to a bridge-specific trap that is not
listed:

1. Write a short bullet (trigger → wrong move → right move).
2. Link the file/theorem or mismatch id if one exists.
3. Commit the skill update with the work that revealed it when
   practical.
