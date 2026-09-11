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

/-! ## A two-stage specification

`countSpec` is what a countdown should leave behind -- zero -- under the
precondition that the counter is representable. `pipelineSpec` sequences it
into the search with `bind`: count down, then search from where the counter
stopped. Its correctness theorem is again about the specification alone, and
it is what `Decomp/Examples/CountdownThenFind.lean` shows a two-region
`Cert.seq` refines through `Cert.Refines.seq`. -/

/-- Count down to zero. Precondition: the counter fits the machine. -/
def countSpec (n : Nat) : Nres Nat := Nres.assert (n < 2 ^ 64) (Nres.ret 0)

/-- Count down, then search from the counter's final value. -/
def pipelineSpec (n stop e : Nat) : Nres (Option Nat) :=
  Nres.bind (countSpec n) fun z => searchSpec stop e z

theorem pipelineSpec_not_fails {n stop e : Nat} (hn : n < 2 ^ 64) (he : 0 < e) :
    ¬ (pipelineSpec n stop e).fails := by
  rintro (hf | ⟨z, hz, hf⟩)
  · exact (Nres.assert_fails _ _).mp hf |>.elim (fun h => h hn) id
  · have hz0 : z = 0 := hz
    subst hz0
    exact searchSpec_not_fails he hf

/-- **Abstract correctness of the pipeline.** On its domain the composite spec
    is determinate: the search starts from `0`, so the answer is `some stop`
    exactly when `stop < e`. -/
theorem pipelineSpec_ok_iff {n stop e : Nat} (o : Option Nat) :
    (pipelineSpec n stop e).ok o ↔ o = (if stop < e then some stop else none) := by
  constructor
  · rintro ⟨z, hz, ho⟩
    have hz0 : z = 0 := hz
    subst hz0
    rw [searchSpec_ok_iff] at ho
    simpa [Nat.zero_le] using ho
  · intro ho
    refine ⟨0, rfl, ?_⟩
    rw [searchSpec_ok_iff]
    simpa [Nat.zero_le] using ho

/-! ## The same pipeline, with a genuinely nondeterministic first stage

`countSpec` admits one answer. `countSpecLe` admits every value at or below
the start -- a spec with **several** acceptable results, which an
implementation refines by picking one -- and `pipelineSpecLe` sequences the
search after it, so the search may start anywhere in `[0, n]`. This is the
instance where `⇓R` and `bind` are exercised against a result *set* rather
than a singleton, and `pipelineSpecLe_two_answers` shows the set really has
more than one element. -/

/-- Count down, loosely: any value at or below the start is acceptable. -/
def countSpecLe (n : Nat) : Nres Nat := Nres.assert (n < 2 ^ 64) (Nres.spec (· ≤ n))

/-- Loose countdown, then search from wherever it stopped. -/
def pipelineSpecLe (n stop e : Nat) : Nres (Option Nat) :=
  Nres.bind (countSpecLe n) fun z => searchSpec stop e z

/-- On its domain -- every possible start `z ≤ n` lies below `e` -- the
    composite does not fail. -/
theorem pipelineSpecLe_not_fails {n stop e : Nat} (hn : n < 2 ^ 64) (hne : n < e) :
    ¬ (pipelineSpecLe n stop e).fails := by
  rintro (hf | ⟨z, hz, hf⟩)
  · exact (Nres.assert_fails _ _).mp hf |>.elim (fun h => h hn) id
  · have hz' : z ≤ n := hz
    exact searchSpec_not_fails (by omega) hf

/-- **Abstract correctness of the loose pipeline.** Whatever the start, an
    answer is `some stop` only if `stop` really lies below `e`, and otherwise
    `none`. -/
theorem pipelineSpecLe_ok {n stop e : Nat} {o : Option Nat}
    (ho : (pipelineSpecLe n stop e).ok o) : (o = some stop ∧ stop < e) ∨ o = none := by
  obtain ⟨z, _, ho⟩ := ho
  rw [searchSpec_ok_iff] at ho
  by_cases hin : z ≤ stop ∧ stop < e
  · rw [if_pos hin] at ho; exact Or.inl ⟨ho, hin.2⟩
  · rw [if_neg hin] at ho; exact Or.inr ho

/-- The spec is genuinely nondeterministic: from `n = 5`, searching for `1`
    below `9`, both `some 1` (start at `0`) and `none` (start at `3`) are
    acceptable. -/
theorem pipelineSpecLe_two_answers :
    (pipelineSpecLe 5 1 9).ok (some 1) ∧ (pipelineSpecLe 5 1 9).ok none := by
  refine ⟨⟨0, Nat.zero_le 5, ?_⟩, ⟨3, show (3 : Nat) ≤ 5 by decide, ?_⟩⟩
  · rw [searchSpec_ok_iff]; decide
  · rw [searchSpec_ok_iff]; decide

end DecompRefine.Examples.Search
