/-
  Decomp.Examples.FindIndexRefine

  The L3 worked instance: `FindIndex` meets `searchSpec`, in two theorems that
  do not know about each other.

  * `DecompRefine.Examples.Search.searchSpec_ok_iff` -- **abstract correctness**. The
    spec's one acceptable answer is `some stop` when `stop` lies in `[i, e)`
    and `none` otherwise. Proved on the `DecompRefine` side; mentions no machine.
  * `result_refines` -- **refinement**. The function extracted from the four
    instructions, `result stop e i`, is `R`-related to an acceptable answer of
    the spec. Proved here about `result` alone; mentions no register.

  `find_meets_spec` composes them with the L2 certificate through
  `Cert.refines_sound`, and its conclusion names the spec, not `result`. This
  is `ROADMAP.md` item 5's acceptance criterion: an abstract-correctness proof
  and a refinement proof that are two separate, independently checkable
  theorems, for one function.

  What it does not show: `bind`. The extracted function is a single loop and
  the spec a single set, so `bind_refine` -- the composition lemma that makes
  the layer scale to a program of several regions -- has no consumer yet.
-/

module

public import Decomp.Refine
public import Decomp.Examples.FindIndexMachine
public import DecompRefine.Examples.Search

@[expose] public section

namespace Decomp.Examples.FindIndex

open RiscvZkvm.Rv64 DecompRefine DecompRefine.Examples.Search

/-- How a concrete exit reads as an abstract answer: a hit at `j` is
    `some j`, exhaustion is `none`. -/
def R : Res → Option Nat → Prop
  | .found j, o => o = some j
  | .exhausted, o => o = none

/-- **The refinement theorem.** `result` refines `searchSpec` up to `R`.
    Outside the spec's domain (`e ≤ i`) the obligation is vacuous -- which is
    right: there the loop may run past `e` and find `stop` anyway, and the spec
    declines to say what it wanted. -/
theorem result_refines (stop e i : Nat) :
    Nres.ret (result stop e i) ≤ Nres.conc R (searchSpec stop e i) := by
  show Nres.ret (result stop e i) ≤ Nres.assert (i < e) (Nres.conc R (Nres.spec _))
  apply Nres.le_assert_of_pre
  intro hlt
  by_cases hin : i ≤ stop ∧ stop < e
  · have hr : result stop e i = .found stop := by
      simp only [result]; rw [if_pos ⟨hin.1, Or.inl hin.2⟩]
    rw [hr]
    exact Nres.ret_le_conc (y := some stop) ⟨rfl, hin.1, hin.2⟩ rfl
  · have hr : result stop e i = .exhausted := by
      simp only [result]; rw [if_neg (by omega)]
    rw [hr]
    exact Nres.ret_le_conc (y := none) (fun j hij hje hjs => hin (hjs ▸ ⟨hij, hje⟩)) rfl

/-- The certificate refines the spec. One line, because `cert.fn` is `result`
    by `rfl` and the refinement theorem is about `result`. -/
theorem cert_refines {st : Stepper} (hst : st.PlainAgree) (base : Word) {stop e : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    (cert hst base hstop he).Refines (fun i => searchSpec stop e i) R :=
  fun i _ => result_refines stop e i

/-- **L2 meets L3.** From any start index in a non-empty range, on either
    backend, the loop reaches the join in a state some acceptable answer of
    `searchSpec` describes. `result` does not appear. -/
theorem find_meets_spec (b : Backend) (base : Word) {stop e i : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) (hlt : i < e)
    (ht : TerminatesB (find stop e) side i) :
    cpsTotalOn b base (base + 16) (cr base) (I stop e i)
      (specPost (Q stop e) R (searchSpec stop e i)) :=
  (cert (Backend.plainAgree b) base hstop he).refines_sound
    (cert_refines (Backend.plainAgree b) base hstop he) i ht (searchSpec_not_fails hlt)

/-- Reading the abstract postcondition back at the machine, using only the
    abstract-correctness theorem: `x10 = stop` if `stop` is in range, `x10 = e`
    otherwise. -/
theorem specPost_search {stop e i : Nat} (h : PartialState)
    (hp : specPost (Q stop e) R (searchSpec stop e i) h) :
    (i ≤ stop ∧ stop < e ∧ I stop e stop h) ∨ (¬ (i ≤ stop ∧ stop < e) ∧ I stop e e h) := by
  obtain ⟨z, hz, y, hR, hQ⟩ := hp
  rw [searchSpec_ok_iff] at hz
  subst hz
  by_cases hin : i ≤ stop ∧ stop < e
  · rw [if_pos hin] at hR
    cases y with
    | found j =>
      simp only [R, Option.some.injEq] at hR
      subst hR
      exact Or.inl ⟨hin.1, hin.2, hQ⟩
    | exhausted => simp [R] at hR
  · rw [if_neg hin] at hR
    cases y with
    | found j => simp [R] at hR
    | exhausted => exact Or.inr ⟨hin, hQ⟩

end Decomp.Examples.FindIndex
