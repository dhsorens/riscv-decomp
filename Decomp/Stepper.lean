/-
  Decomp.Stepper

  The interface a RISC-V backend owes the Myreen triples.

  `Rv64.Logic`'s `cpsTripleWithin` is stated over `stepN`, i.e. over
  `stepOn .zisk`. Since `step`'s ECALL dispatch handles only
  `t0 ∈ {0, 0x02, 0x10, 0xF2}` and otherwise falls through to a silent pc
  advance, a triple stated that way about an SP1 guest would describe a machine
  whose `HINT_LEN`, `HINT_READ` and Pallas precompiles do nothing at all. So the
  judgement has to be re-stated. The question is what to state it over.

  ## Why a `Stepper` and not `∀ b : Backend`

  `Backend` is a closed `inductive {zisk, sp1}` upstream, so quantifying over it
  does not actually make room for a third backend -- adding one is an upstream
  edit to a datatype every `match` on it must then handle. Abstracting the
  *transition function* costs no more and needs no upstream change: a new
  backend supplies a two-field structure literal.

  Auditing what `Logic/CPSSpec.lean`'s proofs use about `step` gives exactly two
  facts. Everything else those proofs need -- `stepN_zero`, `stepN_succ`,
  `stepN_add_eq` -- is monadic bind algebra, which `iter` below gets for free
  with no hypotheses at all.

  ## What this deliberately does *not* abstract

  Abstracting `Rv64.Logic` itself over an abstract machine would be a mistake,
  and the reason is concrete: `PartialState.mem` is
  doubleword-addressed, every assertion in ~19.7k lines is over
  `MachineState`/`Instr`/`Reg`, and putting the state behind a typeclass risks
  `xsimp`/`xperm`/`xcancel`/`run_block`. None of that happens here.
  `MachineState`, `PartialState`, `Assertion`, `**`, `pcFree` and `CodeReq` are
  used unchanged, so every existing tactic keeps operating on the same syntax,
  and `Stepper` is a *value* whose `next` is a field projection `simp` unfolds
  -- there is no abstraction overhead to normalise back out, hence no
  `simp_machine` to normalise back out.
-/

module

public import Decomp.Upstream

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64

/-- What a RISC-V backend owes the Myreen triples: a transition function, and
    the fact that it never rewrites the instruction stream.

    `code_next` is the *only* semantic fact the structural rules need, and it is
    what licenses `CodeReq` as a persistent side condition rather than a
    resource that has to be consumed and handed back.

    Note what `code_next` does and does not say. `MachineState.code` and
    `MachineState.mem` are separate maps, so `code_next` holds structurally for
    any stepper built out of `setReg`/`setMem`/`setPC` -- including one that
    permits a *store into the text window*, which would leave `mem` and `code`
    disagreeing while this field still holds. Keeping the two in step is the
    backend's own obligation in its store guard, not something this field
    checks. `RiscvZkvm.Rv64.StepOn`'s header discusses it; for SP1 the
    mechanism is the `noCodeAt s addr width` conjunct of `memOkSp1`
    (`StepOn.lean:131`), which asks the `code` map directly rather than
    testing an address window. ZisK instead excludes the text window from
    `isValidMemAddr` outright, which is why `Word.lean:58` calls that
    exclusion load-bearing.

    ZisK's two mechanisms and SP1's are *incomparable*, not ordered: SP1
    rejects a store where `code` is present at any address, ZisK rejects one
    anywhere in `[0x78000000, 0xa0000000)` without consulting `code`. So a
    store leaf spec cannot be shared between them on this axis. -/
structure Stepper where
  /-- One step of the machine. `none` is a trap. -/
  next : MachineState → Option MachineState
  /-- Execution never rewrites code. -/
  code_next : ∀ {s s' : MachineState}, next s = some s' → s'.code = s.code
  /-- The states the judgements range over. `fun _ => True` for a backend whose
      step function needs nothing beyond what a `CodeReq` says; SP1's store
      guard needs more (`Decomp/Leaf/Sp1Text.lean`). -/
  inv : MachineState → Prop
  /-- The invariant survives a step, so a judgement can be sequenced. -/
  inv_next : ∀ {s s' : MachineState}, inv s → next s = some s' → inv s'

namespace Stepper

/-- `n` steps of `st`, or `none` if any of them traps. -/
def iter (st : Stepper) : Nat → MachineState → Option MachineState
  | 0,     s => some s
  | n + 1, s => (st.next s).bind (st.iter n ·)

@[simp] theorem iter_zero (st : Stepper) (s : MachineState) :
    st.iter 0 s = some s := rfl

@[simp] theorem iter_succ (st : Stepper) (n : Nat) (s : MachineState) :
    st.iter (n + 1) s = (st.next s).bind (st.iter n ·) := rfl

theorem iter_one (st : Stepper) (s : MachineState) :
    st.iter 1 s = st.next s := by
  cases h : st.next s <;> simp [h]

/-- Splitting a run: the analogue of `stepN_add`. -/
theorem iter_add (st : Stepper) (n m : Nat) (s : MachineState) :
    st.iter (n + m) s = (st.iter n s).bind (st.iter m ·) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    have : n + 1 + m = (n + m) + 1 := by omega
    rw [this]
    cases h : st.next s with
    | none => simp [h]
    | some s' => simp [h, ih s']

/-- Composing two runs. This is the workhorse every sequencing rule bottoms out
    in -- the analogue of `RiscvZkvm.Rv64.stepN_add_eq`. -/
theorem iter_add_eq {st : Stepper} {n m : Nat} {s s' s'' : MachineState}
    (h1 : st.iter n s = some s') (h2 : st.iter m s' = some s'') :
    st.iter (n + m) s = some s'' := by
  rw [iter_add, h1, Option.bind]
  exact h2

/-- Code is immutable across a whole run, not just one step. This is what
    `CodeReq.SatisfiedBy` persistence is proved from. -/
theorem code_iter {st : Stepper} {n : Nat} {s s' : MachineState}
    (h : st.iter n s = some s') : s'.code = s.code := by
  induction n generalizing s with
  | zero => cases h; rfl
  | succ n ih =>
    cases hs : st.next s with
    | none => rw [iter_succ, hs] at h; simp at h
    | some sm =>
      rw [iter_succ, hs] at h
      simp only [Option.bind_some] at h
      rw [ih h, st.code_next hs]

/-- The invariant holds along a whole run. -/
theorem inv_iter {st : Stepper} {n : Nat} {s s' : MachineState}
    (hinv : st.inv s) (h : st.iter n s = some s') : st.inv s' := by
  induction n generalizing s with
  | zero => cases h; exact hinv
  | succ n ih =>
    cases hs : st.next s with
    | none => rw [iter_succ, hs] at h; simp at h
    | some sm =>
      rw [iter_succ, hs] at h
      simp only [Option.bind_some] at h
      exact ih (st.inv_next hinv hs) h

/-- A `CodeReq` satisfied at entry is satisfied throughout the run. The
    generalisation of `RiscvZkvm.Rv64.CodeReq.SatisfiedBy_preserved`, which is
    stated for `stepN`. -/
theorem satisfiedBy_iter {st : Stepper} {cr : CodeReq} {n : Nat}
    {s s' : MachineState} (h : st.iter n s = some s') (hcr : cr.SatisfiedBy s) :
    cr.SatisfiedBy s' := by
  intro a i ha
  rw [code_iter h]
  exact hcr a i ha

end Stepper

/-! ## The existing backends as `Stepper`s -/

/-- `HINT_READ` never rewrites code: it writes `mem` and drops the consumed
    prefix of `privateInput`, and `code` is a separate field. -/
theorem code_hintRead {s s' : MachineState} (h : hintRead s = some s') :
    s'.code = s.code := by
  -- `simp only` rather than `unfold`, because `hintRead`'s body binds its
  -- intermediate states with `have`, which `split` cannot see through.
  simp only [hintRead] at h
  split at h
  · simp at h                             -- stream exhausted
  · split at h
    · simp at h                           -- `a0` misaligned
    · split at h
      · simp at h                         -- write window out of range or on code
      · split at h
        · simp at h                       -- `a1` disagrees with the length
        · split at h
          · simp at h                     -- payload short
          · simp only [Option.some.injEq] at h; subst h; simp

/-- `stepSp1` never rewrites code.

    Every arm either traps, or ends in one of `execInstrBr` / `execSp1Accel` /
    `setReg` / `setMem` / `setPC` / `writeBytesAsWords` / a `privateInput`
    field update / `sp1Commit` -- all of which have `@[simp]`
    code-preservation lemmas upstream or leave the field syntactically
    untouched -- or delegates to `step`, which has `code_step`.

    The splits are written out rather than driven by `repeat' split`: the SP1
    dispatch chain is six deep, and a greedy `repeat'` walks on past it into
    `execSp1Accel`'s own `match`, leaving goals whose hypotheses are shaped
    differently from the ones the arms below expect. -/
theorem code_stepSp1 {s s' : MachineState} (h : stepSp1 s = some s') :
    s'.code = s.code := by
  unfold stepSp1 at h
  split at h
  · simp at h                             -- nothing fetched
  · simp at h                             -- `.CSRS`: ZisK-only, traps here
  · -- `.ECALL`: the SP1 syscall dispatch
    simp only [sp1Ecall] at h
    split at h
    · -- an accelerator id
      split at h
      · simp only [Option.some.injEq] at h; subst h; simp
      · simp at h                         -- bad operands, or a side condition
    · split at h
      · -- HINT_LEN
        simp only [Option.some.injEq] at h; subst h; simp [hintLen]
      · split at h
        · exact code_hintRead h           -- HINT_READ
        · split at h
          · -- COMMIT
            simp only [Option.some.injEq] at h; subst h; simp [MachineState.sp1Commit]
          · split at h
            · -- COMMIT_DEFERRED_PROOFS: an explicit no-op
              simp only [Option.some.injEq] at h; subst h; simp
            · split at h
              · exact code_step h         -- the enumerated host syscalls
              · simp at h                 -- unmodelled id: traps
  · simp at h                             -- `.EBREAK`
  · -- the backend-independent catch-all, gated on the SP1 memory profile
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; simp
      · simp at h                         -- outside SP1's addressable space
    · simp only [Option.some.injEq] at h; subst h; simp

/-- Neither backend rewrites code. This is the one place anything in `Decomp`
    case-splits on `Backend`. -/
theorem code_stepOn {b : Backend} {s s' : MachineState} (h : stepOn b s = some s') :
    s'.code = s.code := by
  cases b with
  | zisk => exact code_step (by rwa [stepOn_zisk] at h)
  | sp1  => exact code_stepSp1 (by rwa [stepOn_sp1] at h)

/-- Each `Backend` as a `Stepper`. A future backend needs no `Backend`
    constructor: it supplies its own `Stepper` literal. -/
def Backend.stepper (b : Backend) : Stepper where
  next := stepOn b
  code_next := code_stepOn
  inv _ := True
  inv_next _ _ := trivial

@[simp] theorem Backend.stepper_inv (b : Backend) (s : MachineState) :
    (Backend.stepper b).inv s := trivial

@[simp] theorem Backend.stepper_next (b : Backend) :
    (Backend.stepper b).next = stepOn b := rfl

/-- `Stepper.iter` agrees with upstream's `stepNOn`. -/
theorem Backend.stepper_iter (b : Backend) (n : Nat) (s : MachineState) :
    (Backend.stepper b).iter n s = stepNOn b n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Stepper.iter_succ, stepNOn_succ, Backend.stepper_next]
    cases stepOn b s with
    | none => rfl
    | some s' => simpa using ih s'

/-- The ZisK instance recovers `stepN` exactly. Note this needs induction
    rather than `rfl`: `stepOn .zisk = step` is definitional, but `iter` and
    `stepN` are different recursors, so upstream's own `stepNOn_zisk` is a
    theorem too. -/
theorem Backend.stepper_iter_zisk (n : Nat) (s : MachineState) :
    (Backend.stepper .zisk).iter n s = stepN n s := by
  rw [Backend.stepper_iter, stepNOn_zisk]

end Decomp
