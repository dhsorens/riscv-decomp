/-
  Decomp.Loop

  The loop rule: no fuel, no invented variant.

  This is the file the rest of the library exists for. Annotate-and-VCG does not
  scale at the assembly level, where "one needs to invent a precondition, a
  postcondition and, for the loop, an invariant and a variant"; and a step
  budget must not be a correctness parameter threaded by hand (README "Why no
  fuel"). Both are properties of the *loop rule*, and the rule
  available upstream has both problems:

      loopNatCert … (start : Nat) : Nat → Prop
        | 0      => cpsTripleWithin nExit header exit_ cr (inv start) post
        | fuel+1 => cpsBranchWithin … ∧ cpsTripleWithin … ∧ Entails … ∧
                    loopNatCert … (start + 1) fuel

  `fuel` there must be a literal at proof-construction time, the certificate is
  a right-nested conjunction of `fuel` copies of its obligations (so the proof
  term is Θ(fuel)), and `loopBound nHeader nBody nExit fuel` -- the step budget
  the resulting triple carries -- grows linearly in it. A loop whose trip count
  depends on its input has no such bound, so it cannot be stated at all.

  `cpsTotal_loop` below takes no fuel and produces no bound. The trip count
  arrives as the index of a `TerminatesIn` derivation and is eliminated by
  induction on it, so the caller discharges termination with the *same*
  induction that proves the abstract function correct -- which is exactly what
  that asks for, and what TR-765 §2.7's four-line worked example does.

  ## The shape of the header hypothesis

  The header is given as two conditional triples rather than one branch:

      guard true  ⇒ header falls through to the body
      guard false ⇒ header jumps to the exit

  That is deliberate, and it is the primitive. A bare `cpsBranch` at the header
  is *not* enough to drive the induction: it says control goes one way or the
  other, but not which, and nothing in the machine-level judgement relates that
  decision to `r.guard`. Tying the two together is precisely the job of the
  coupling assertion `I`, so it belongs in the caller's obligation. The
  branch-shaped front end `cpsTotal_loop_of_branch` recovers the ergonomic form
  for callers whose header block genuinely produces a `cpsBranch` carrying the
  guard as a pure fact.

  ## Mid-body exits

  `cpsTotal_loopB` below is the same rule over `RecB` -- a body that may return
  instead of continuing -- and it is what a loop with an early `break` needs
  (`memcpy`'s alignment loop leaves from five instructions into its body). It
  is not a second rule bolted on: `cpsTotal_loop` is recoverable
  from it (`cpsTotal_loop_of_loopB`), so the two obligations of the general
  rule subsume the three of the header-shaped one.

  The earlier version of this file said a mid-body break would mean "adding a
  break test and a break observation to `Rec` and a third constructor to
  `TerminatesIn`, roughly doubling `Decomp.Tailrec`". That estimate was of the
  wrong design. Folding the guard *into* the body -- `body : α → α ⊕ β` --
  needs no extra constructor and no extra test, because an early exit is just
  a second `inr` branch, and the rule gets shorter rather than longer: two
  obligations instead of three, and no do-while rotation for a bottom-guarded
  loop.
-/

import Decomp.Triple
import Decomp.Tailrec

namespace Decomp

open RiscvZkvm.Rv64

universe u v

variable {α : Type u} {β : Type v}

/-- **The loop rule.** A `cpsTotal` triple for a loop whose trip count depends
    on its input, with no step bound and no variant.

    * `I x` couples the abstract state `x` to the machine at the header.
    * `J x` is the assertion the header leaves for the body -- upstream's
      `bodyPre`. Take `J = I` when the header only tests and branches.
    * `side` is the per-iteration side condition. TR-765's rider is that a
      verification using the extracted function must prove it holds; here it is
      a hypothesis of `TerminatesIn`, so the caller cannot forget it. It is
      also handed to the header-true and body obligations, because in the
      `iter` case the induction has it from the constructor -- and a header
      typically needs it (`Examples/CountdownMachine.lean` needs `n < 2^64` to
      conclude `ofNat n ≠ 0` from `n ≠ 0`). The header-false obligation cannot
      receive it: `exit` carries no `side`. That asymmetry is TR-765's own --
      the side condition is only checked on states the loop iterates *from*.

    The conclusion's postcondition is `Q (r.runN n x)` for the `n` the
    derivation supplies. `TerminatesIn.unique` says that `n` is determined by
    the loop, and `TerminatesIn.runN_stable` says the answer does not depend on
    it, so quoting `runN n` costs no generality. -/
theorem cpsTotal_loop {st : Stepper} {r : Rec α β} {side : α → Prop}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {I J : α → Assertion} {Q : β → Assertion} {nH nB : Nat}
    (hHeaderTrue : ∀ x, r.guard x = true → side x →
      cpsWithin st nH header bodyEntry cr (I x) (J x))
    (hHeaderFalse : ∀ x, r.guard x = false →
      cpsWithin st nH header exit_ cr (I x) (Q (r.out x)))
    (hBody : ∀ x, r.guard x = true → side x →
      cpsWithin st nB bodyEntry header cr (J x) (I (r.step x)))
    {n : Nat} {x : α} (h : TerminatesIn r side n x) :
    cpsTotal st header exit_ cr (I x) (Q (r.runN n x)) := by
  induction h with
  | exit hx =>
    -- `r.runN 0 x` is `r.out x` by `rfl`, so the exit triple is the whole story.
    exact cpsTotal_of_cpsWithin (hHeaderFalse _ hx)
  | @iter x n hg hs _ ih =>
    -- header -> body -> header, then the tail by induction. No bound survives.
    rw [Rec.runN_succ_of_guard hg]
    exact cpsWithin_seq_cpsTotal_same_cr (hHeaderTrue x hg hs)
      (cpsWithin_seq_cpsTotal_same_cr (hBody x hg hs) ih)

/-- The loop rule against a closed-form function.

    `heq` is the ordinary-induction obligation Myreen's workflow is *about*:
    prove the extracted tail-recursive function equals something you would
    rather reason with. Everything above L2 then sees only `f`. -/
theorem cpsTotal_loop_eq {st : Stepper} {r : Rec α β} {side : α → Prop}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {I J : α → Assertion} {Q : β → Assertion} {nH nB : Nat} {f : α → β}
    (hHeaderTrue : ∀ x, r.guard x = true → side x →
      cpsWithin st nH header bodyEntry cr (I x) (J x))
    (hHeaderFalse : ∀ x, r.guard x = false →
      cpsWithin st nH header exit_ cr (I x) (Q (r.out x)))
    (hBody : ∀ x, r.guard x = true → side x →
      cpsWithin st nB bodyEntry header cr (J x) (I (r.step x)))
    (heq : ∀ n x, TerminatesIn r side n x → r.runN n x = f x)
    {x : α} (h : Terminates r side x) :
    cpsTotal st header exit_ cr (I x) (Q (f x)) := by
  obtain ⟨n, ht⟩ := h
  rw [← heq n x ht]
  exact cpsTotal_loop hHeaderTrue hHeaderFalse hBody ht

/-- The branch-shaped front end. A real loop header is a block ending in a
    conditional branch, so leaf composition produces a `cpsBranch`; this turns
    one into the two conditional triples `cpsTotal_loop` wants, given that the
    arm postconditions carry the guard's value as a pure fact.

    Carrying `⌜r.guard x = _⌝` on the arms is what discharges the unreachable
    arm in each case, via `cpsBranch_takenPath` / `cpsBranch_notTakenPath`. -/
theorem cpsTotal_loop_of_branch {st : Stepper} {r : Rec α β} {side : α → Prop}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {I J : α → Assertion} {Q : β → Assertion} {nH nB : Nat}
    (hHeader : ∀ x, cpsBranch st nH header cr (I x)
      bodyEntry (⌜r.guard x = true⌝ ** J x)
      exit_ (⌜r.guard x = false⌝ ** Q (r.out x)))
    (hBody : ∀ x, r.guard x = true → side x →
      cpsWithin st nB bodyEntry header cr (J x) (I (r.step x)))
    {n : Nat} {x : α} (h : TerminatesIn r side n x) :
    cpsTotal st header exit_ cr (I x) (Q (r.runN n x)) := by
  refine cpsTotal_loop (nH := nH) (fun y hg _ => ?_) (fun y hy => ?_) hBody h
  · refine cpsWithin_weaken (fun _ hp => hp)
      (fun hp hq => ((sepConj_pure_left hp).mp hq).2)
      (cpsBranch_takenPath (fun hp hq => ?_) (hHeader y))
    rw [((sepConj_pure_left hp).mp hq).1] at hg
    exact absurd hg (by simp)
  · refine cpsWithin_weaken (fun _ hp => hp)
      (fun hp hq => ((sepConj_pure_left hp).mp hq).2)
      (cpsBranch_notTakenPath (fun hp hq => ?_) (hHeader y))
    rw [((sepConj_pure_left hp).mp hq).1] at hy
    exact absurd hy (by simp)

/-! ## Loops whose body may return

`cpsTotal_loop` above wants the header-shaped loop: guard at the top, body a
straight line back to it. `Decomp/Tailrec.lean`'s `RecB` drops that split, and
this is the rule over it. Two obligations instead of three, and there is no
`bodyEntry`/`header` distinction -- the region has one entry, which the body
returns to.

That also means a **bottom-guarded** (do-while) loop needs no rotation: the
body is `fun x => if continue x then .inl (step x) else .inr (out x)` and the
region's entry is the guest's own entry. The `memset` tail loop this rule was
first driven against used to sequence one unrolled body pass in front of
`cpsTotal_loop` to get that effect; it does not any more. -/

/-- **The loop rule for a body that may return.** No step bound, no variant,
    and no assumption about where in the body the exit is.

    * `I x` couples the abstract state to the machine at the region's entry.
    * `hCont` is a full pass that comes back: entry to entry.
    * `hExit` is a pass that leaves: entry to `exit_`. A region with several
      machine exits proves this obligation once per `inr` branch of `body`, and
      they must all reach the same `exit_` -- see `Tailrec.lean`'s note on why
      that is the compiler's own behaviour rather than a restriction.
    * `side` is handed to *both*, unlike `cpsTotal_loop`, whose header-false
      obligation cannot have it. Here the body runs on the way out, so it
      needs the same domain facts.

    The two bounds are separate because the continue and exit paths through a
    real body have different lengths. -/
theorem cpsTotal_loopB {st : Stepper} {r : RecB α β} {side : α → Prop}
    {entry exit_ : Word} {cr : CodeReq}
    {I : α → Assertion} {Q : β → Assertion} {nC nE : Nat}
    (hCont : ∀ x x', r.body x = .inl x' → side x →
      cpsWithin st nC entry entry cr (I x) (I x'))
    (hExit : ∀ x y, r.body x = .inr y → side x →
      cpsWithin st nE entry exit_ cr (I x) (Q y))
    {n : Nat} {x : α} {y : β} (h : RunsTo r side n x y) :
    cpsTotal st entry exit_ cr (I x) (Q y) := by
  induction h with
  | exit hb hs => exact cpsTotal_of_cpsWithin (hExit _ _ hb hs)
  | iter hb hs _ ih => exact cpsWithin_seq_cpsTotal_same_cr (hCont _ _ hb hs) ih

/-- The returning-body rule against a closed-form function. `heq` is the
    ordinary-induction obligation: whatever the region returns, it is `f x`. -/
theorem cpsTotal_loopB_eq {st : Stepper} {r : RecB α β} {side : α → Prop}
    {entry exit_ : Word} {cr : CodeReq}
    {I : α → Assertion} {Q : β → Assertion} {nC nE : Nat} {f : α → β}
    (hCont : ∀ x x', r.body x = .inl x' → side x →
      cpsWithin st nC entry entry cr (I x) (I x'))
    (hExit : ∀ x y, r.body x = .inr y → side x →
      cpsWithin st nE entry exit_ cr (I x) (Q y))
    (heq : ∀ n x y, RunsTo r side n x y → y = f x)
    {x : α} (h : TerminatesB r side x) :
    cpsTotal st entry exit_ cr (I x) (Q (f x)) := by
  obtain ⟨n, y, ht⟩ := h
  rw [← heq n x y ht]
  exact cpsTotal_loopB hCont hExit ht

/-- **The header-shaped rule is a special case.** Same conclusion as
    `cpsTotal_loop`, from the same three obligations, but routed through
    `cpsTotal_loopB` and `Rec.toRecB`.

    This is here as evidence, not as the implementation: `cpsTotal_loop` keeps
    its own four-line proof, because an indirection through `RecB` would make
    the primitive harder to read for no gain. What this theorem buys is the
    claim that `RecB` lost nothing -- if the `α ⊕ β` shape could not express a
    `while` loop, this would not typecheck.

    The `side` weakening is `TerminatesIn.toRunsTo`'s, and it is why the
    obligations below take `r.guard x = true → side x` in place of `side x`:
    `TerminatesIn.exit` has no side condition to give at the exit state, and
    the implication is vacuous exactly there. -/
theorem cpsTotal_loop_of_loopB {st : Stepper} {r : Rec α β} {side : α → Prop}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {I J : α → Assertion} {Q : β → Assertion} {nH nB : Nat}
    (hHeaderTrue : ∀ x, r.guard x = true → side x →
      cpsWithin st nH header bodyEntry cr (I x) (J x))
    (hHeaderFalse : ∀ x, r.guard x = false →
      cpsWithin st nH header exit_ cr (I x) (Q (r.out x)))
    (hBody : ∀ x, r.guard x = true → side x →
      cpsWithin st nB bodyEntry header cr (J x) (I (r.step x)))
    {n : Nat} {x : α} (h : TerminatesIn r side n x) :
    cpsTotal st header exit_ cr (I x) (Q (r.runN n x)) := by
  refine cpsTotal_loopB (nC := nH + nB) (nE := nH) (fun z z' hb hs => ?_)
    (fun z y hb hs => ?_) h.toRunsTo
  · -- The body continued, so the guard was true and `z' = r.step z`.
    cases hg : r.guard z with
    | false => rw [Rec.toRecB_body_of_not_guard hg] at hb; exact absurd hb (by simp)
    | true =>
      rw [Rec.toRecB_body_of_guard hg] at hb
      cases Sum.inl.inj hb
      exact cpsWithin_seq_same_cr (hHeaderTrue z hg (hs hg)) (hBody z hg (hs hg))
  · -- The body returned, so the guard was false and `y = r.out z`.
    cases hg : r.guard z with
    | true => rw [Rec.toRecB_body_of_guard hg] at hb; exact absurd hb (by simp)
    | false =>
      rw [Rec.toRecB_body_of_not_guard hg] at hb
      cases Sum.inr.inj hb
      exact hHeaderFalse z hg

end Decomp
