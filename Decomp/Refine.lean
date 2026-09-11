/-
  Decomp.Refine

  Where L2 meets L3: an extracted function refines an abstract specification.

  `Cert` (L2) says what a region of machine code does, as a function `fn` plus
  a triple coupling it to the machine. `Refine.Nres` (L3) says what a program
  *should* do, as a set of acceptable results. This file joins them with one
  predicate and one theorem:

  * `Cert.Refines c spec R` -- on every input the certificate admits, the
    extracted result is `R`-related to an acceptable result of `spec`. A
    statement about `fn`, provable without the machine.
  * `Cert.refines_sound` -- the desugaring: `Refines` plus the certificate
    give a `cpsTotal` triple whose postcondition is stated *against the spec*,
    so a caller reads "the machine ends in a state that some acceptable answer
    describes" without ever seeing `fn`.

  The point is separation. The abstract-correctness proof lives on the `Refine`
  side and mentions no machine; the refinement proof mentions `fn` and no
  registers; the certificate mentions registers and no spec. Each is checked
  on its own, and this file is the only place all three are in scope.
-/

module

public import Decomp.Certificate
public import Refine.Nres

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64 Refine

universe u v w

variable {st : Stepper} {α : Type u} {β : Type v} {γ : Type w}

/-- The certificate's extracted function refines `spec` up to `R`, on the
    certificate's own domain. Where `spec x` fails the obligation is vacuous:
    that is how an abstract precondition reaches the concrete side. -/
def Cert.Refines (c : Cert st α β) (spec : α → Nres γ) (R : β → γ → Prop) : Prop :=
  ∀ x, c.pre x → Nres.ret (c.fn x) ≤ Nres.conc R (spec x)

/-- The machine-level reading of an abstract spec: some acceptable result `z`,
    and the machine is in a state `post y` for a `y` related to it. -/
def specPost (post : β → Assertion) (R : β → γ → Prop) (m : Nres γ) : Assertion :=
  fun h => ∃ z, m.ok z ∧ ∃ y, R y z ∧ post y h

/-- **The desugaring.** A refining certificate is a `cpsTotal` triple against
    the spec, wherever the spec does not fail. `fn` does not appear in the
    conclusion. -/
theorem Cert.refines_sound (c : Cert st α β) {spec : α → Nres γ} {R : β → γ → Prop}
    (hr : c.Refines spec R) (x : α) (hx : c.pre x) (hnf : ¬ (spec x).fails) :
    cpsTotal st c.entry c.exit_ c.cr (c.couple x) (specPost c.post R (spec x)) := by
  obtain ⟨z, hz, hR⟩ := (Nres.ret_le_conc_iff.mp (hr x hx)).resolve_left hnf
  exact cpsTotal_weaken (fun _ hp => hp) (fun _ hq => ⟨z, hz, c.fn x, hR, hq⟩) (c.sound x hx)

/-- Refinement composes at the certificate level: a certificate refining
    `spec₁`, and `spec₁` refining `spec₂`, give a certificate refining `spec₂`
    along the composed relation. `Nres.refine_trans`, lifted. -/
theorem Cert.Refines.trans {c : Cert st α β} {spec₁ : α → Nres γ} {R₁ : β → γ → Prop}
    {δ : Type w} {spec₂ : α → Nres δ} {R₂ : γ → δ → Prop}
    (h₁ : c.Refines spec₁ R₁)
    (h₂ : ∀ x, c.pre x → spec₁ x ≤ Nres.conc R₂ (spec₂ x)) :
    c.Refines spec₂ (Nres.relComp R₁ R₂) :=
  fun x hx => Nres.refine_trans (h₁ x hx) (h₂ x hx)

/-- **Sequencing refines `bind`.** If `c₁` refines `spec₁` and, on every output
    `c₁` can produce and every `R₁`-related abstract result, `c₂` refines the
    continuation, then `c₁.seq c₂` refines `bind spec₁ spec₂`. This is
    `Nres.bind_refine` at the certificate level -- the two `seq`s line up:
    `Cert.seq`'s side condition is `c₁.pre x ∧ c₂.pre (c₁.fn x)`, and
    `bind_refine` asks about the continuation only at results of the first
    spec, which for `ret (c₁.fn x)` is exactly `c₁.fn x`. -/
theorem Cert.Refines.seq {c₁ : Cert st α β} {c₂ : Cert st β γ}
    {hmid : c₁.exit_ = c₂.entry} {hcr : c₁.cr = c₂.cr}
    {hlink : ∀ y hp, c₁.post y hp → c₂.couple y hp}
    {δ : Type w} {ε : Type w} {spec₁ : α → Nres δ} {R₁ : β → δ → Prop}
    {spec₂ : δ → Nres ε} {R₂ : γ → ε → Prop}
    (h₁ : c₁.Refines spec₁ R₁)
    (h₂ : ∀ y z, R₁ y z → c₂.pre y → Nres.ret (c₂.fn y) ≤ Nres.conc R₂ (spec₂ z)) :
    (c₁.seq c₂ hmid hcr hlink).Refines (fun x => Nres.bind (spec₁ x) spec₂) R₂ := by
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := hx
  show Nres.ret (c₂.fn (c₁.fn x)) ≤ _
  rw [← Nres.bind_ret (c₁.fn x) (fun y => Nres.ret (c₂.fn y))]
  refine Nres.bind_refine (h₁ x hx₁) (fun y z hy hR => ?_)
  have hy' : y = c₁.fn x := hy
  subst hy'
  exact h₂ _ z hR hx₂

/-- Weakening the relation. -/
theorem Cert.Refines.mono {c : Cert st α β} {spec : α → Nres γ} {R R' : β → γ → Prop}
    (hR : ∀ y z, R y z → R' y z) (h : c.Refines spec R) : c.Refines spec R' := by
  intro x hx
  rcases h x hx with hf | ⟨hn, hok⟩
  · exact Or.inl hf
  · refine Or.inr ⟨hn, fun y hy => ?_⟩
    obtain ⟨z, hz, hyz⟩ := hok y hy
    exact ⟨z, hz, hR y z hyz⟩

end Decomp
