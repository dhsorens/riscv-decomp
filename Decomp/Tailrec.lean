/-
  Decomp.Tailrec

  Conditional termination and the extracted tail-recursive function.

  TR-765's decompilation emits, per loop region,

      tailrec g f d x = let (cond, v1…vn) = d (while g f x) in
                        (cond ∧ (∃n. ¬g (fⁿ x)), v1…vn)

  with the rider that "any verification that uses such extracted function must
  prove that the returned `cond` is equal to true; otherwise the postcondition
  of the certificate theorem has no meaning". Termination is *conditional* --
  the extracted function need not terminate on all inputs -- and the obligation
  carries an unfolding equation

      terminates f g s x = (g x ⇒ s x ∧ terminates f g s (f x))

  plus a derived induction principle, so it is discharged by the *same*
  induction that proves functional correctness rather than by a separately
  invented variant. That is the whole point: contrast annotate-and-VCG, where a
  human invents a precondition, a postcondition, an invariant *and* a variant
  per loop.

  ## The encoding, and one thing that does not work

  Reading the unfolding equation as an **inductive** rather than a recursive
  definition is what makes this cheap: the least fixpoint *is* conditional
  termination, and Lean's generated `.rec` *is* TR-765's derived induction
  principle, for free.

  The obvious shape -- a `Prop`-valued `Terminates r side x` with a trip count
  `Terminates.iters : Terminates r side x → Nat` read off the derivation -- is
  **not definable**. `Terminates` would be a non-subsingleton `Prop`, and
  eliminating one into `Nat` is large elimination, which Lean rejects. Deriving
  a trip count would then need `Acc`-based well-founded recursion or
  `Classical.choose`, and the extracted function would carry a proof argument
  that leaks into every statement above it.

  So the trip count is an *index* instead. `TerminatesIn r side n x` says the
  loop exits after exactly `n` iterations; `Terminates` existentially quantifies
  it. The extracted function `runN` then takes a plain `Nat`, is total and
  computable, mentions no proof, and -- crucially -- `n` is never a
  human-supplied bound: it is bound by the existential and eliminated by the
  induction. Contrast `RiscvZkvm.Rv64.WP.loopNatCert`, whose `fuel` must be a
  literal at proof-construction time and whose proof term is Θ(fuel).

  Nothing here mentions a machine, an `Instr` or a `Stepper`; this file is pure
  Lean and imports nothing from `Rv64`.
-/

module

@[expose] public section

namespace Decomp

universe u v

variable {α : Type u} {β : Type v}

/-- One extracted loop region: the guard the header tests, the body's effect on
    the abstract state, and the observation taken on exit.

    This is the `(g, f, d)` of TR-765's `tailrec g f d`. -/
structure Rec (α : Type u) (β : Type v) where
  /-- The loop guard, as the header decides it. -/
  guard : α → Bool
  /-- One iteration of the body. -/
  step : α → α
  /-- What is observed once the guard goes false. -/
  out : α → β

namespace Rec

/-- `n` iterations of the body. Defined here rather than via `Nat.iterate`,
    which lives in Mathlib -- not a dependency of the root package when this
    was written. A targeted Mathlib import is acceptable (see the gotchas
    skill); five lines were cheaper than the first `require`. -/
def iterate (r : Rec α β) : Nat → α → α
  | 0,     x => x
  | n + 1, x => r.iterate n (r.step x)

@[simp] theorem iterate_zero (r : Rec α β) (x : α) : r.iterate 0 x = x := rfl

@[simp] theorem iterate_succ (r : Rec α β) (n : Nat) (x : α) :
    r.iterate (n + 1) x = r.iterate n (r.step x) := rfl

/-- The extracted tail-recursive function, at a given iteration count.

    Total and computable, and it takes no proof argument -- see this file's
    header for why that matters. On inputs where the loop does exit, every
    sufficiently large `n` gives the same answer (`runN_stable`), so `runN` is
    the extracted function and the trip count is bookkeeping. -/
def runN (r : Rec α β) : Nat → α → β
  | 0,     x => r.out x
  | n + 1, x => if r.guard x then r.runN n (r.step x) else r.out x

@[simp] theorem runN_zero (r : Rec α β) (x : α) : r.runN 0 x = r.out x := rfl

theorem runN_succ (r : Rec α β) (n : Nat) (x : α) :
    r.runN (n + 1) x = if r.guard x then r.runN n (r.step x) else r.out x := rfl

@[simp] theorem runN_succ_of_guard {r : Rec α β} {x : α} (h : r.guard x = true)
    (n : Nat) : r.runN (n + 1) x = r.runN n (r.step x) := by
  rw [runN_succ, h, if_pos rfl]

@[simp] theorem runN_of_not_guard {r : Rec α β} {x : α} (h : r.guard x = false)
    (n : Nat) : r.runN n x = r.out x := by
  cases n with
  | zero => rfl
  | succ n => rw [runN_succ, h]; rfl

end Rec

/-! ## Conditional termination -/

/-- `TerminatesIn r side n x`: starting from `x`, the loop takes exactly `n`
    iterations before the guard goes false, and `side` holds at every state it
    passes through on the way.

    This is TR-765's `terminates f g s x` with the trip count made an index.
    `TerminatesIn.rec`, generated by Lean, is the derived induction principle. -/
inductive TerminatesIn (r : Rec α β) (side : α → Prop) : Nat → α → Prop where
  /-- The guard is already false: zero iterations. -/
  | exit {x : α} : r.guard x = false → TerminatesIn r side 0 x
  /-- The guard holds, the side condition holds here, and the rest terminates. -/
  | iter {x : α} {n : Nat} : r.guard x = true → side x →
      TerminatesIn r side n (r.step x) → TerminatesIn r side (n + 1) x

/-- The loop exits, after some number of iterations. TR-765's `∃n. ¬g (fⁿ x)`,
    bundled with the accumulated per-iteration side conditions -- which is what
    that paper's returned `cond` is. `terminatesIn_split` below separates the
    two halves. -/
def Terminates (r : Rec α β) (side : α → Prop) (x : α) : Prop :=
  ∃ n, TerminatesIn r side n x

namespace TerminatesIn

/-- Weakening the side condition. -/
theorem mono_side {r : Rec α β} {side side' : α → Prop} {n : Nat} {x : α}
    (hmono : ∀ y, side y → side' y) (h : TerminatesIn r side n x) :
    TerminatesIn r side' n x := by
  induction h with
  | exit hx => exact .exit hx
  | iter hg hs _ ih => exact .iter hg (hmono _ hs) ih

/-- The trip count is determined by the loop, not chosen. Two derivations for
    the same start state agree, which is what makes `Terminates` usable as a
    side condition without a well-definedness caveat. -/
theorem unique {r : Rec α β} {side : α → Prop} {n m : Nat} {x : α}
    (h1 : TerminatesIn r side n x) (h2 : TerminatesIn r side m x) : n = m := by
  induction h1 generalizing m with
  | exit hx =>
    cases h2 with
    | exit _ => rfl
    | iter hg _ _ => rw [hx] at hg; exact absurd hg (by simp)
  | iter hg _ _ ih =>
    cases h2 with
    | exit hx => rw [hx] at hg; exact absurd hg (by simp)
    | iter _ _ ht2 => exact congrArg (· + 1) (ih ht2)

/-- Every state the loop visits before exiting satisfies the side condition.
    This is the direction a verification consumes: TR-765's rider that the
    returned `cond` must be proved true. -/
theorem side_iterate {r : Rec α β} {side : α → Prop} {n : Nat} {x : α}
    (h : TerminatesIn r side n x) : ∀ i, i < n → side (r.iterate i x) := by
  induction h with
  | exit _ => intro i hi; exact absurd hi (by omega)
  | @iter x n hg hs _ ih =>
    intro i hi
    cases i with
    | zero => exact hs
    | succ i => exact ih i (by omega)

/-- Pure termination: the same statement with the side condition discharged. -/
theorem pure {r : Rec α β} {side : α → Prop} {n : Nat} {x : α}
    (h : TerminatesIn r side n x) : TerminatesIn r (fun _ => True) n x :=
  h.mono_side (fun _ _ => trivial)

/-- The guard really is false at the exit state. -/
theorem guard_iterate {r : Rec α β} {side : α → Prop} {n : Nat} {x : α}
    (h : TerminatesIn r side n x) : r.guard (r.iterate n x) = false := by
  induction h with
  | exit hx => exact hx
  | iter _ _ _ ih => exact ih

/-- Above the exit point the extracted function is constant, so `runN` does not
    depend on *which* sufficiently large iteration count it is given. This is
    what lets a certificate quote `runN n` for the `n` its own induction
    produced. -/
theorem runN_stable {r : Rec α β} {side : α → Prop} {n m : Nat} {x : α}
    (h : TerminatesIn r side n x) (hle : n ≤ m) : r.runN m x = r.runN n x := by
  induction h generalizing m with
  | exit hx => rw [Rec.runN_of_not_guard hx, Rec.runN_of_not_guard hx]
  | @iter x n hg _ _ ih =>
    cases m with
    | zero => exact absurd hle (by omega)
    | succ m =>
      rw [Rec.runN_succ_of_guard hg, Rec.runN_succ_of_guard hg]
      exact ih (by omega)

/-- The extracted function is the observation at the exit state. The bridge
    between the recursive form, which the certificate is proved in, and the
    closed form, which downstream reasoning prefers. -/
theorem runN_eq {r : Rec α β} {side : α → Prop} {n : Nat} {x : α}
    (h : TerminatesIn r side n x) : r.runN n x = r.out (r.iterate n x) := by
  induction h with
  | exit hx => simp
  | iter hg _ _ ih => rw [Rec.runN_succ_of_guard hg, ih]; rfl

/-- Recombining the two halves. Inducts on the iteration count rather than on
    the derivation, because `side_iterate`'s conclusion mentions both `n` and
    `x` and `induction` would otherwise revert it into the motive. -/
theorem of_pure {r : Rec α β} {side : α → Prop} :
    ∀ (n : Nat) (x : α), TerminatesIn r (fun _ => True) n x →
      (∀ i, i < n → side (r.iterate i x)) → TerminatesIn r side n x := by
  intro n
  induction n with
  | zero =>
    intro x hp _
    cases hp with
    | exit hx => exact .exit hx
  | succ n ih =>
    intro x hp hside
    cases hp with
    | iter hg _ ht =>
      exact .iter hg (hside 0 (by omega)) (ih _ ht fun i hi => hside (i + 1) (by omega))

/-- Termination is exactly "the guard eventually goes false", once the side
    condition is separated out. The two halves of TR-765's returned `cond`:
    `∃n. ¬g (fⁿ x)` on the left, the accumulated domain facts on the right. -/
theorem split {r : Rec α β} {side : α → Prop} {n : Nat} {x : α} :
    TerminatesIn r side n x ↔
      (TerminatesIn r (fun _ => True) n x ∧ ∀ i, i < n → side (r.iterate i x)) :=
  ⟨fun h => ⟨h.pure, h.side_iterate⟩, fun ⟨hpure, hside⟩ => of_pure n x hpure hside⟩

end TerminatesIn

namespace Terminates

/-- TR-765's unfolding equation,

        terminates f g s x = (g x ⇒ s x ∧ terminates f g s (f x)),

    as an `iff`. Rewriting with this is how a loop's obligation is peeled one
    iteration at a time. -/
theorem unfold {r : Rec α β} {side : α → Prop} {x : α} :
    Terminates r side x ↔
      (r.guard x = true → side x ∧ Terminates r side (r.step x)) := by
  constructor
  · rintro ⟨n, h⟩ hg
    cases h with
    | exit hx => rw [hx] at hg; exact absurd hg (by simp)
    | iter _ hs ht => exact ⟨hs, ⟨_, ht⟩⟩
  · intro h
    cases hg : r.guard x with
    | false => exact ⟨0, .exit hg⟩
    | true =>
      obtain ⟨hs, n, ht⟩ := h hg
      exact ⟨n + 1, .iter hg hs ht⟩

theorem mono_side {r : Rec α β} {side side' : α → Prop} {x : α}
    (hmono : ∀ y, side y → side' y) (h : Terminates r side x) :
    Terminates r side' x :=
  h.imp fun _ ht => ht.mono_side hmono

/-- Inducting on the witness rather than on a derivation, for the same reason
    as `TerminatesIn.of_pure`. Note the trip count this produces need not be the
    `n` supplied: the guard may go false earlier. -/
private theorem of_guard_false (r : Rec α β) :
    ∀ (n : Nat) (x : α), r.guard (r.iterate n x) = false →
      Terminates r (fun _ => True) x := by
  intro n
  induction n with
  | zero => intro x hx; exact ⟨0, .exit hx⟩
  | succ n ih =>
    intro x hx
    cases hg : r.guard x with
    | false => exact ⟨0, .exit hg⟩
    | true =>
      obtain ⟨m, hm⟩ := ih (r.step x) hx
      exact ⟨m + 1, .iter hg trivial hm⟩

/-- Pure termination in TR-765's own `∃n. ¬g (fⁿ x)` form. -/
theorem iff_exists_guard_false {r : Rec α β} {x : α} :
    Terminates r (fun _ => True) x ↔ ∃ n, r.guard (r.iterate n x) = false :=
  ⟨fun ⟨_, h⟩ => ⟨_, h.guard_iterate⟩, fun ⟨n, hn⟩ => of_guard_false r n x hn⟩

end Terminates

/-! ## Loops whose body may return: `RecB`

Everything above assumes the shape TR-765 assumes: the guard is decided at the
*header*, and the body is a straight line from the body entry back to it. LLVM
does not emit that shape for a loop with an early `break`. In a typical compiled
`memcpy`, the alignment loop tests its condition **part-way into the body** and
leaves the loop from there, and the word-copy loops are the same.
This section closes that gap.

The generalisation is to stop separating the guard from the body:

    body : α → α ⊕ β

-- one pass either continues with a new abstract state (`inl`) or returns an
output (`inr`). A header-guarded `while` loop is the special case
`body x = if guard x then .inl (step x) else .inr (out x)`
(`Rec.toRecB` below, with `cpsTotal_loop_of_loopB` as the evidence that no
expressiveness is lost), and a mid-body exit is just a second `inr` branch
inside one `body`. Nothing needs to know how many exits there are.

Three things change, and it is worth being explicit about them:

* **The trip count and the output are both indices.** `RunsTo r side n x y`
  says the body ran `n` times and then returned `y`. Carrying `y` as an index
  rather than reading it off a total `runN` avoids the `Option` that a
  partial extracted function would otherwise force into every postcondition.
  `RecB.runN` still exists, for the same reason `Rec.runN` does, but nothing
  in the loop rule depends on it.
* **The side condition is checked at the exit state too.** `TerminatesIn.exit`
  carries no `side`, because a `while` header's guard-false path executes the
  test and nothing else. Here the body *runs* on the way out -- `memcpy`'s
  alignment loop has already stored a byte and decremented its counter before
  it decides to leave -- so the exit obligation needs the same domain facts as
  the continue obligation. That is why `RunsTo.exit` takes `side x`.
* **The machine exit label may depend on the output.** `cpsTotal` has a single
  exit address, but the loop rule's conclusion is about one derivation
  `RunsTo r side n x y`, and `y` says which exit was taken -- so the label can
  be `exitOf y` (`cpsTotal_loopB_exits`), and two `inr` branches may land on
  two different addresses with no join between them. `cpsTotal_loopB` is the
  constant-label instance, which is all a compiler's own output ever needs (a
  compiled loop's mid-body branch and its bottom jump land on one join label).
-/

/-- One extracted loop region whose body may return instead of continuing.

    The `α ⊕ β` is the whole of the generalisation: `Rec`'s `guard`, `step` and
    `out` are recoverable from it (`Rec.toRecB`), and a mid-body `break` is a
    second `inr` branch that `Rec` cannot express at all. -/
structure RecB (α : Type u) (β : Type v) where
  /-- One pass of the body: continue with a new state, or return an output. -/
  body : α → α ⊕ β

namespace RecB

/-- The extracted function, at a given iteration count. `none` means the count
    was too small -- the body was still asking to continue -- which is the
    partiality `Rec.runN` avoids only because its `out` is total. Kept for
    parity with `Rec.runN`; the loop rule uses `RunsTo` instead. -/
def runN (r : RecB α β) : Nat → α → Option β
  | 0,     x => match r.body x with
    | .inl _ => none
    | .inr y => some y
  | n + 1, x => match r.body x with
    | .inl x' => r.runN n x'
    | .inr y => some y

end RecB

/-- `RunsTo r side n x y`: from `x`, the body runs `n` times and then returns
    `y`, with `side` true at every state it was entered on -- the last one
    included.

    This is `TerminatesIn` with the output carried as a second index. Lean's
    generated `RunsTo.rec` is again TR-765's derived induction principle. -/
inductive RunsTo (r : RecB α β) (side : α → Prop) : Nat → α → β → Prop where
  /-- The body returns: zero further iterations. -/
  | exit {x : α} {y : β} : r.body x = .inr y → side x → RunsTo r side 0 x y
  /-- The body continues, and the rest returns `y`. -/
  | iter {x x' : α} {n : Nat} {y : β} : r.body x = .inl x' → side x →
      RunsTo r side n x' y → RunsTo r side (n + 1) x y

/-- The region returns, after some number of passes, with some output. -/
def TerminatesB (r : RecB α β) (side : α → Prop) (x : α) : Prop :=
  ∃ n y, RunsTo r side n x y

namespace RunsTo

theorem mono_side {r : RecB α β} {side side' : α → Prop} {n : Nat} {x : α} {y : β}
    (hmono : ∀ z, side z → side' z) (h : RunsTo r side n x y) :
    RunsTo r side' n x y := by
  induction h with
  | exit hb hs => exact .exit hb (hmono _ hs)
  | iter hb hs _ ih => exact .iter hb (hmono _ hs) ih

/-- Both indices are determined by the region, not chosen. The `β` half is
    what lets a certificate quote the output without a well-definedness
    caveat; the `Nat` half is `TerminatesIn.unique`. -/
theorem unique {r : RecB α β} {side : α → Prop} {n m : Nat} {x : α} {y z : β}
    (h1 : RunsTo r side n x y) (h2 : RunsTo r side m x z) : n = m ∧ y = z := by
  induction h1 generalizing m z with
  | exit hb _ =>
    cases h2 with
    | exit hb2 _ => rw [hb] at hb2; exact ⟨rfl, Sum.inr.inj hb2⟩
    | iter hb2 _ _ => rw [hb] at hb2; exact absurd hb2 (by simp)
  | iter hb _ _ ih =>
    cases h2 with
    | exit hb2 _ => rw [hb] at hb2; exact absurd hb2 (by simp)
    | iter hb2 _ ht2 =>
      rw [hb] at hb2
      cases Sum.inl.inj hb2
      obtain ⟨hn, hy⟩ := ih ht2
      exact ⟨congrArg (· + 1) hn, hy⟩

/-- The derivation determines the extracted function's answer. -/
theorem runN_eq {r : RecB α β} {side : α → Prop} {n : Nat} {x : α} {y : β}
    (h : RunsTo r side n x y) : r.runN n x = some y := by
  induction h with
  | exit hb _ => simp [RecB.runN, hb]
  | iter hb _ _ ih => simp [RecB.runN, hb, ih]

/-- Above the exit point the answer does not depend on the count, so a
    certificate may quote `runN` at any sufficiently large one. -/
theorem runN_stable {r : RecB α β} {side : α → Prop} {n m : Nat} {x : α} {y : β}
    (h : RunsTo r side n x y) (hle : n ≤ m) : r.runN m x = some y := by
  induction h generalizing m with
  | exit hb _ => cases m <;> simp [RecB.runN, hb]
  | @iter x x' n y hb _ _ ih =>
    cases m with
    | zero => exact absurd hle (by omega)
    | succ m => simp only [RecB.runN, hb]; exact ih (by omega)

end RunsTo

/-! ## The `while` shape is a special case -/

namespace Rec

/-- A header-guarded loop as a returning-body one. The evidence that `RecB` is
    a generalisation rather than a sibling is `cpsTotal_loop_of_loopB` in
    `Decomp/Loop.lean`, which rebuilds the original rule from the new one
    through this. -/
def toRecB (r : Rec α β) : RecB α β :=
  ⟨fun x => if r.guard x then .inl (r.step x) else .inr (r.out x)⟩

@[simp] theorem toRecB_body_of_guard {r : Rec α β} {x : α} (h : r.guard x = true) :
    r.toRecB.body x = .inl (r.step x) := by simp [toRecB, h]

@[simp] theorem toRecB_body_of_not_guard {r : Rec α β} {x : α} (h : r.guard x = false) :
    r.toRecB.body x = .inr (r.out x) := by simp [toRecB, h]

end Rec

/-- `TerminatesIn` transported along `Rec.toRecB`.

    The side condition is weakened to `guard y = true → side y`, and that is
    forced rather than incidental: `TerminatesIn.exit` never supplies `side` at
    the exit state, while `RunsTo.exit` demands it. The guard is false there,
    so the implication is vacuous exactly where the fact is missing -- which is
    TR-765's asymmetry, written as a side condition instead of as a missing
    constructor argument. -/
theorem TerminatesIn.toRunsTo {r : Rec α β} {side : α → Prop} {n : Nat} {x : α}
    (h : TerminatesIn r side n x) :
    RunsTo r.toRecB (fun y => r.guard y = true → side y) n x (r.runN n x) := by
  induction h with
  | exit hx =>
    rw [Rec.runN_of_not_guard hx]
    exact .exit (Rec.toRecB_body_of_not_guard hx) (fun hg => by rw [hx] at hg; simp at hg)
  | @iter x n hg hs _ ih =>
    rw [Rec.runN_succ_of_guard hg]
    exact .iter (Rec.toRecB_body_of_guard hg) (fun _ => hs) ih

end Decomp
