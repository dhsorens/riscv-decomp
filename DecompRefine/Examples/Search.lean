/-
  DecompRefine.Examples.Search

  An abstract specification and its correctness, with no machine in sight.

  This is the abstract half of the L3 worked instance. `searchSpec` is what a
  linear search over an index range *should* return; `searchSpec_ok_iff` is its
  correctness theorem -- on its domain the spec is determinate, and says which
  answer it determines. Neither mentions `Decomp`, a register or an
  instruction. `Decomp/Examples/FindIndexRefine.lean` proves, separately, that
  the function extracted from four RISC-V instructions refines this spec; the
  two theorems compose through `Cert.refines_sound` and neither has to know
  about the other's world.
-/

module

public import DecompRefine.Nres

@[expose] public section

namespace DecompRefine.Examples.Search

open DecompRefine

/-- Linear search over the index range `[i, e)` for `stop`: `some stop` if it
    lies in the range, `none` if no index in the range is `stop`. The
    precondition is a non-empty range, `i < e`; outside it the spec fails and
    asks nothing of an implementation. -/
def searchSpec (stop e i : Nat) : Nres (Option Nat) :=
  Nres.assert (i < e) (Nres.spec fun o =>
    match o with
    | some j => j = stop ∧ i ≤ j ∧ j < e
    | none => ∀ j, i ≤ j → j < e → j ≠ stop)

/-- The spec does not fail on its domain. -/
theorem searchSpec_not_fails {stop e i : Nat} (h : i < e) : ¬ (searchSpec stop e i).fails := by
  simp only [searchSpec, Nres.assert_fails, Nres.spec_fails, or_false]
  exact fun hn => hn h

/-- **Abstract correctness.** The spec is determinate: its one acceptable result
    is `some stop` when `stop` lies in the range and `none` otherwise. A proof
    about the specification alone. -/
theorem searchSpec_ok_iff (stop e i : Nat) (o : Option Nat) :
    (searchSpec stop e i).ok o ↔ o = (if i ≤ stop ∧ stop < e then some stop else none) := by
  simp only [searchSpec, Nres.assert_ok, Nres.spec_ok]
  by_cases hin : i ≤ stop ∧ stop < e
  · rw [if_pos hin]
    cases o with
    | none =>
      simp only [reduceCtorEq, iff_false]
      intro h
      exact h stop hin.1 hin.2 rfl
    | some j =>
      simp only [Option.some.injEq]
      constructor
      · rintro ⟨rfl, _, _⟩; rfl
      · rintro rfl; exact ⟨rfl, hin.1, hin.2⟩
  · rw [if_neg hin]
    cases o with
    | none =>
      simp only [iff_true]
      intro j hij hje hjs
      exact hin (hjs ▸ ⟨hij, hje⟩)
    | some j =>
      simp only [reduceCtorEq, iff_false]
      rintro ⟨rfl, h1, h2⟩
      exact hin ⟨h1, h2⟩

end DecompRefine.Examples.Search
