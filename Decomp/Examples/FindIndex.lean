/-
  Decomp.Examples.FindIndex

  The abstract half of a loop with **two exits**, one of them mid-body.

  `cpsTotal_loopB` exists for a body that may return from more than one place
  -- `body : α → α ⊕ β`, a second `inr` branch being an early `break` -- and
  until this file it had been driven only by a single-exit loop (`memset`'s
  tail, downstream), which exercises the rule and not the reason for it. This
  is the smallest loop the author could find whose body genuinely has two
  `inr` branches with **different machine paths behind them**:

      loop:  BEQ  x10, x11, +16      -- if (i == stop) break        exit A
             ADDI x10, x10, 1        -- ++i
             BNE  x10, x12, -8       -- if (i != end) goto loop
             JAL  x0,  +4            -- goto exit                   exit B
      exit:

  i.e. `for (;;) { if (i == stop) return found; ++i; if (i == end) return
  exhausted; }` -- a linear search over an index range, with the search hit
  leaving from the *top* of the body and the range exhaustion from the
  *bottom*, through the `JAL` a compiler puts between an exit and the join.
  It is hand-written, like `Countdown`; what it does and does not exercise is
  listed at the end of `FindIndexMachine.lean`.

  This file is machine-free: the `RecB`, its `RunsTo` derivations, and the
  extracted function. `Decomp/Examples/FindIndexMachine.lean` couples it to
  the four instructions.

  ## Where `RunsTo.exit` taking `side x` costs something

  `side i` is `i + 1 < 2 ^ 64`: the increment must not wrap, or the abstract
  `i + 1 = end` and the machine's `x10 = x12` come apart. The `found` exit
  never increments -- it leaves before the `ADDI` -- yet `RunsTo.exit` demands
  `side` there too, so `runsTo_found` carries `stop + 1 < 2 ^ 64` where
  `stop < 2 ^ 64` would do. That is the asymmetry `Tailrec.lean` documents
  (`RunsTo.exit` takes `side x`, `TerminatesIn.exit` takes none), seen from the
  consumer's side: one strict-vs-non-strict bound, paid once. It is the price
  of a single `side` shared by both exits, and it is small enough to be the
  right trade -- the alternative is a `side` per `inr` branch.
-/

module

public import Decomp.Certificate
-- `#guard` evaluates, so the definitions it runs must be importable as code.
meta import Decomp.Tailrec

@[expose] public section

namespace Decomp.Examples.FindIndex

/-- Which exit the region took, and the index it took it at. The second `inr`
    branch of a `RecB` body is a value of this type, not a second label. -/
inductive Res where
  /-- The index reached `stop` before the range ran out. Leaves from the top of
      the body, before the increment. -/
  | found (i : Nat)
  /-- The index reached `end` without meeting `stop`. Leaves from the bottom of
      the body, through the `JAL`. -/
  | exhausted
  deriving DecidableEq, Repr

/-- The loop, with `stop` and `e` (the end of the range) as parameters: they
    sit in registers the loop never writes. The abstract state is the index. -/
def find (stop e : Nat) : RecB Nat Res where
  body i :=
    if i = stop then .inr (.found i)
    else if i + 1 = e then .inr .exhausted
    else .inl (i + 1)

/-- The per-pass side condition: the increment does not wrap. Checked at every
    state the body is entered on, the exit state included. -/
def side (i : Nat) : Prop := i + 1 < 2 ^ 64

/-! ## The body's three branches, as rewrite lemmas -/

theorem body_found {stop e i : Nat} (h : i = stop) :
    (find stop e).body i = .inr (.found i) := by
  simp [find, h]

theorem body_exhausted {stop e i : Nat} (h1 : i ≠ stop) (h2 : i + 1 = e) :
    (find stop e).body i = .inr .exhausted := by
  simp [find, h1, h2]

theorem body_cont {stop e i : Nat} (h1 : i ≠ stop) (h2 : i + 1 ≠ e) :
    (find stop e).body i = .inl (i + 1) := by
  simp [find, h1, h2]

/-! ## Termination, one derivation per exit

Each is ordinary induction on the distance to the exit. No variant is
invented: the distance *is* the trip count, and it is an index of `RunsTo`. -/

/-- The search hits: `stop` lies ahead of `i` and is reached before `e`. The
    bound on `stop` is strict because the exit state must satisfy `side`
    (see the header). -/
theorem runsTo_found {stop e : Nat} (hse : stop < e) (he : e < 2 ^ 64) :
    ∀ d i, i + d = stop → RunsTo (find stop e) side d i (.found stop) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp only [Nat.add_zero] at hi
    subst hi
    exact .exit (body_found rfl) (by simp only [side]; omega)
  | succ d ih =>
    intro i hi
    have h1 : i ≠ stop := by omega
    have h2 : i + 1 ≠ e := by omega
    exact .iter (body_cont h1 h2) (by simp only [side]; omega) (ih (i + 1) (by omega))

/-- The range runs out: from `i`, no index in `[i, e)` is `stop`. -/
theorem runsTo_exhausted {stop e : Nat} (he : e < 2 ^ 64) :
    ∀ d i, i + 1 + d = e → (∀ j, i ≤ j → j < e → j ≠ stop) →
      RunsTo (find stop e) side d i .exhausted := by
  intro d
  induction d with
  | zero =>
    intro i hi hno
    have h1 : i ≠ stop := hno i (Nat.le_refl i) (by omega)
    exact .exit (body_exhausted h1 (by omega)) (by simp only [side]; omega)
  | succ d ih =>
    intro i hi hno
    have h1 : i ≠ stop := hno i (Nat.le_refl i) (by omega)
    have h2 : i + 1 ≠ e := by omega
    exact .iter (body_cont h1 h2) (by simp only [side]; omega)
      (ih (i + 1) (by omega) (fun j hj hje => hno j (by omega) hje))

/-! ## The extracted function -/

/-- The closed form. `stop` is found exactly when it lies at or ahead of `i`
    and the end of the range does not come first -- where "does not come
    first" is `stop < e ∨ e ≤ i`: either the end is beyond `stop`, or it is
    already behind the start and (in `Nat`, and on the machine under `side`)
    is never reached at all. -/
def result (stop e i : Nat) : Res :=
  if i ≤ stop ∧ (stop < e ∨ e ≤ i) then .found stop else .exhausted

/-- Whatever the region returns is `result`. The `heq` obligation of
    `cpsTotal_loopB_eq` / `Cert.ofLoopB`, by induction on the derivation. -/
theorem runsTo_eq_result {stop e : Nat} :
    ∀ n i y, RunsTo (find stop e) side n i y → y = result stop e i := by
  intro n i y h
  induction h with
  | @exit i y hb _ =>
    by_cases hs : i = stop
    · rw [body_found hs] at hb
      cases Sum.inr.inj hb
      subst hs
      simp [result]
    · by_cases hend : i + 1 = e
      · rw [body_exhausted hs hend] at hb
        cases Sum.inr.inj hb
        have : ¬ (i ≤ stop ∧ (stop < e ∨ e ≤ i)) := by omega
        simp [result, this]
      · rw [body_cont hs hend] at hb
        exact absurd hb (by simp)
  | @iter i i' n y hb _ _ ih =>
    by_cases hs : i = stop
    · rw [body_found hs] at hb; exact absurd hb (by simp)
    · by_cases hend : i + 1 = e
      · rw [body_exhausted hs hend] at hb; exact absurd hb (by simp)
      · rw [body_cont hs hend] at hb
        cases Sum.inl.inj hb
        rw [ih]
        have : (i ≤ stop ∧ (stop < e ∨ e ≤ i)) ↔ (i + 1 ≤ stop ∧ (stop < e ∨ e ≤ i + 1)) := by
          omega
        simp only [result, this]

/-! ## Build-time checks

`#guard` evaluates and produces no proof term. These pin the two exits against
each other: same loop, same parameters, and the start index alone decides
which `inr` branch fires. -/

-- `stop = 5`, `e = 8`: from `2` the search hits, after three passes.
#guard (find 5 8).runN 3 2 == some (.found 5)
#guard (find 5 8).runN 2 2 == none
#guard result 5 8 2 == .found 5

-- Same parameters, from `6`: `stop` is behind us and the range runs out at `8`.
#guard (find 5 8).runN 1 6 == some .exhausted
#guard result 5 8 6 == .exhausted

-- The end is behind the start: the range is never exhausted, and the search hits.
#guard (find 9 3).runN 4 5 == some (.found 9)
#guard result 9 3 5 == .found 9

-- Starting *on* `stop`: the mid-body exit fires with zero increments.
#guard (find 5 8).runN 0 5 == some (.found 5)

end Decomp.Examples.FindIndex
