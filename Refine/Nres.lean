/-
  Refine.Nres

  Nondeterminism with failure, and data refinement over it. The abstract half
  of the L3 layer: nothing here knows there is a machine.

  A specification is a set of acceptable results together with a flag saying
  whether it *fails* -- fails in the sense of the refinement calculus, where
  `fail` is the **top** of the refinement order and refining it is trivial. That
  is how a precondition is written: a spec that fails outside its domain asks
  nothing of an implementation there. Lammich's `nres` (Isabelle's Refinement
  Framework) is the reference design; this is its normal form -- `FAIL` or a
  result set -- as one structure with two fields, so that `bind`, `⇓R` and the
  order are all structural and no case split ever needs classical choice.

  The three things a consumer uses:

  * `ret x ≤ ⇓R m'` -- a deterministic result `x` refines `m'` up to `R`:
    unless `m'` fails, some acceptable result of `m'` is `R`-related to `x`
    (`ret_le_conc_iff`).
  * `refine_trans` -- refinements compose along relation composition.
  * `bind_refine` -- refinements compose along `bind`, given a refinement of
    the continuation on `R`-related inputs.

  `Decomp/Refine.lean` ties `ret (c.fn x) ≤ ⇓R (spec x)` to an L2 certificate
  `c`, and desugars the pair to a `cpsTotal` triple against the abstract spec.
-/

module

@[expose] public section

namespace Refine

universe u v w

/-- A specification: may it fail, and which results are acceptable when it
    does not. `fail` is top; `res P` is the set `P`. -/
structure Nres (α : Type u) where
  /-- The spec fails (asks nothing). -/
  fails : Prop
  /-- The acceptable results, when it does not fail. -/
  ok : α → Prop

namespace Nres

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The failing spec: top of the order. -/
def fail : Nres α := ⟨True, fun _ => True⟩

/-- The set of acceptable results `P`. -/
def spec (P : α → Prop) : Nres α := ⟨False, P⟩

/-- Exactly one acceptable result. -/
def ret (x : α) : Nres α := spec (· = x)

/-- Precondition: `spec` under `pre`, `fail` outside it. The refinement
    obligation is then vacuous where the precondition is false. -/
def assert (pre : Prop) (m : Nres α) : Nres α := ⟨¬ pre ∨ m.fails, m.ok⟩

/-- Sequencing. Fails if `m` does, or if the continuation fails on some
    acceptable result of `m`. -/
def bind (m : Nres α) (f : α → Nres β) : Nres β :=
  ⟨m.fails ∨ ∃ x, m.ok x ∧ (f x).fails, fun y => ∃ x, m.ok x ∧ (f x).ok y⟩

/-- Data refinement: `conc R m'` is the concrete spec whose acceptable results
    are those `R`-related to some acceptable abstract result. Written `⇓R` in
    the literature. -/
def conc (R : α → β → Prop) (m' : Nres β) : Nres α :=
  ⟨m'.fails, fun x => ∃ y, m'.ok y ∧ R x y⟩

/-- The refinement order. `m ≤ m'`: either `m'` fails (and asks nothing), or
    neither fails and every result of `m` is acceptable to `m'`. -/
def Le (m m' : Nres α) : Prop :=
  m'.fails ∨ (¬ m.fails ∧ ∀ x, m.ok x → m'.ok x)

instance : LE (Nres α) := ⟨Le⟩

theorem le_def {m m' : Nres α} :
    m ≤ m' ↔ (m'.fails ∨ (¬ m.fails ∧ ∀ x, m.ok x → m'.ok x)) := Iff.rfl

@[simp] theorem fail_fails : (fail : Nres α).fails := trivial
@[simp] theorem spec_fails (P : α → Prop) : (spec P).fails ↔ False := Iff.rfl
@[simp] theorem spec_ok (P : α → Prop) (x : α) : (spec P).ok x ↔ P x := Iff.rfl
@[simp] theorem ret_fails (x : α) : (ret x).fails ↔ False := Iff.rfl
@[simp] theorem ret_ok (x y : α) : (ret x).ok y ↔ y = x := Iff.rfl
@[simp] theorem conc_fails (R : α → β → Prop) (m' : Nres β) : (conc R m').fails ↔ m'.fails := Iff.rfl
@[simp] theorem conc_ok (R : α → β → Prop) (m' : Nres β) (x : α) :
    (conc R m').ok x ↔ ∃ y, m'.ok y ∧ R x y := Iff.rfl
@[simp] theorem assert_fails (pre : Prop) (m : Nres α) :
    (assert pre m).fails ↔ (¬ pre ∨ m.fails) := Iff.rfl
@[simp] theorem assert_ok (pre : Prop) (m : Nres α) (x : α) :
    (assert pre m).ok x ↔ m.ok x := Iff.rfl

/-! ## The order -/

theorem le_refl (m : Nres α) : m ≤ m := by
  by_cases h : m.fails
  · exact Or.inl h
  · exact Or.inr ⟨h, fun _ hx => hx⟩

theorem le_trans {m₁ m₂ m₃ : Nres α} (h₁ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₃) : m₁ ≤ m₃ := by
  rcases h₂ with h₃ | ⟨hn₂, hok₂⟩
  · exact Or.inl h₃
  · rcases h₁ with h₂f | ⟨hn₁, hok₁⟩
    · exact absurd h₂f hn₂
    · exact Or.inr ⟨hn₁, fun x hx => hok₂ x (hok₁ x hx)⟩

/-- `fail` is the top. This is what makes a precondition free. -/
theorem le_fail (m : Nres α) : m ≤ fail := Or.inl trivial

theorem ret_le_spec {P : α → Prop} {x : α} (h : P x) : ret x ≤ spec P :=
  Or.inr ⟨id, fun _ hy => hy ▸ h⟩

/-- Results of a refinement are acceptable to the spec, unless the spec fails. -/
theorem ok_of_le {m m' : Nres α} (h : m ≤ m') (hnf : ¬ m'.fails) {x : α} (hx : m.ok x) :
    m'.ok x := by
  rcases h with hf | ⟨_, hok⟩
  · exact absurd hf hnf
  · exact hok x hx

/-- The deterministic case, unpacked: `x` refines `m'` up to `R` iff `m'` fails
    or some acceptable result of `m'` is related to `x`. -/
theorem ret_le_conc_iff {R : α → β → Prop} {x : α} {m' : Nres β} :
    ret x ≤ conc R m' ↔ (m'.fails ∨ ∃ y, m'.ok y ∧ R x y) := by
  constructor
  · rintro (hf | ⟨_, hok⟩)
    · exact Or.inl hf
    · exact Or.inr (hok x rfl)
  · rintro (hf | hy)
    · exact Or.inl hf
    · exact Or.inr ⟨id, fun _ hz => hz ▸ hy⟩

theorem ret_le_conc {R : α → β → Prop} {x : α} {y : β} {m' : Nres β}
    (hy : m'.ok y) (hR : R x y) : ret x ≤ conc R m' :=
  ret_le_conc_iff.mpr (Or.inr ⟨y, hy, hR⟩)

/-- `assert pre m` asks nothing outside `pre`, and exactly `m` inside it. -/
theorem le_assert_of_pre {pre : Prop} {m : Nres α} {m' : Nres α} (h : pre → m ≤ m') :
    m ≤ assert pre m' := by
  by_cases hp : pre
  · rcases h hp with hf | ⟨hn, hok⟩
    · exact Or.inl (Or.inr hf)
    · exact Or.inr ⟨hn, hok⟩
  · exact Or.inl (Or.inl hp)

/-! ## The two composition lemmas -/

/-- Relation composition, `R₁ ⨾ R₂`. -/
def relComp (R₁ : α → β → Prop) (R₂ : β → γ → Prop) : α → γ → Prop :=
  fun x z => ∃ y, R₁ x y ∧ R₂ y z

/-- **Transitivity of refinement**, along relation composition. -/
theorem refine_trans {R₁ : α → β → Prop} {R₂ : β → γ → Prop}
    {m₁ : Nres α} {m₂ : Nres β} {m₃ : Nres γ}
    (h₁ : m₁ ≤ conc R₁ m₂) (h₂ : m₂ ≤ conc R₂ m₃) :
    m₁ ≤ conc (relComp R₁ R₂) m₃ := by
  rcases h₂ with hf₃ | ⟨hn₂, hok₂⟩
  · exact Or.inl hf₃
  · rcases h₁ with hf₂ | ⟨hn₁, hok₁⟩
    · exact absurd hf₂ hn₂
    · refine Or.inr ⟨hn₁, fun x hx => ?_⟩
      obtain ⟨y, hy, hxy⟩ := hok₁ x hx
      obtain ⟨z, hz, hyz⟩ := hok₂ y hy
      exact ⟨z, hz, y, hxy, hyz⟩

/-- **Refinement through `bind`.** If `m` refines `m'` up to `R`, and on
    `R`-related inputs `f` refines `f'` up to `R'`, then the sequences refine
    up to `R'`. -/
theorem bind_refine {R : α → β → Prop} {R' : γ → γ → Prop}
    {m : Nres α} {m' : Nres β} {f : α → Nres γ} {f' : β → Nres γ}
    (hm : m ≤ conc R m')
    (hf : ∀ x y, R x y → f x ≤ conc R' (f' y)) :
    bind m f ≤ conc R' (bind m' f') := by
  by_cases hf' : (bind m' f').fails
  · exact Or.inl hf'
  · have hn' : ¬ m'.fails := fun h => hf' (Or.inl h)
    rcases hm with hmf | ⟨hn, hok⟩
    · exact absurd hmf hn'
    · refine Or.inr ⟨?_, ?_⟩
      · rintro (hmf | ⟨x, hx, hfx⟩)
        · exact hn hmf
        · obtain ⟨y, hy, hxy⟩ := hok x hx
          rcases hf x y hxy with hff | ⟨hnf, _⟩
          · exact hf' (Or.inr ⟨y, hy, hff⟩)
          · exact hnf hfx
      · rintro z ⟨x, hx, hz⟩
        obtain ⟨y, hy, hxy⟩ := hok x hx
        have hfy : ¬ (f' y).fails := fun h => hf' (Or.inr ⟨y, hy, h⟩)
        obtain ⟨z', hz', hzz'⟩ := ok_of_le (hf x y hxy) hfy hz
        exact ⟨z', ⟨y, hy, hz'⟩, hzz'⟩

/-! ## Monad laws, for the record

Stated as equalities of `Nres`, which needs `propext` and `funext`; they are
not used by the refinement lemmas above, which never rewrite a spec. -/

theorem ext {m m' : Nres α} (hf : m.fails ↔ m'.fails) (hok : ∀ x, m.ok x ↔ m'.ok x) :
    m = m' := by
  cases m; cases m'
  simp only [mk.injEq]
  exact ⟨propext hf, funext fun x => propext (hok x)⟩

theorem bind_ret (x : α) (f : α → Nres β) : bind (ret x) f = f x := by
  apply ext
  · simp only [bind, ret, spec]
    constructor
    · rintro (h | ⟨y, rfl, h⟩)
      · exact h.elim
      · exact h
    · intro h; exact Or.inr ⟨x, rfl, h⟩
  · intro y
    simp only [bind, ret, spec]
    constructor
    · rintro ⟨z, rfl, h⟩; exact h
    · intro h; exact ⟨x, rfl, h⟩

theorem ret_bind (m : Nres α) : bind m ret = m := by
  apply ext
  · simp only [bind, ret, spec]
    constructor
    · rintro (h | ⟨_, _, h⟩)
      · exact h
      · exact h.elim
    · exact Or.inl
  · intro y
    simp only [bind, ret, spec]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro h; exact ⟨y, h, rfl⟩

theorem bind_assoc (m : Nres α) (f : α → Nres β) (g : β → Nres γ) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  apply ext
  · simp only [bind]
    constructor
    · rintro ((h | ⟨x, hx, hf⟩) | ⟨y, ⟨x, hx, hy⟩, hg⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, Or.inl hf⟩
      · exact Or.inr ⟨x, hx, Or.inr ⟨y, hy, hg⟩⟩
    · rintro (h | ⟨x, hx, (hf | ⟨y, hy, hg⟩)⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨x, hx, hf⟩)
      · exact Or.inr ⟨y, ⟨x, hx, hy⟩, hg⟩
  · intro z
    simp only [bind]
    constructor
    · rintro ⟨y, ⟨x, hx, hy⟩, hz⟩; exact ⟨x, hx, y, hy, hz⟩
    · rintro ⟨x, hx, y, hy, hz⟩; exact ⟨y, ⟨x, hx, hy⟩, hz⟩

end Nres

end Refine
