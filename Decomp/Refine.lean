/-
  Decomp.Refine

  Where L2 meets L3: an extracted function refines an abstract specification.

  `Cert` (L2) says what a region of machine code does, as a function `fn` plus
  a triple coupling it to the machine. `DecompRefine.Nres` (L3) says what a program
  *should* do, as a set of acceptable results. This file joins them with one
  predicate and one theorem:

  * `Cert.Refines c spec R` -- on every input the certificate admits, the
    extracted result is `R`-related to an acceptable result of `spec`. A
    statement about `fn`, provable without the machine.
  * `Cert.refines_sound` -- the desugaring: `Refines` plus the certificate
    give a `cpsTotal` triple whose postcondition is stated *against the spec*,
    so a caller reads "the machine ends in a state that some acceptable answer
    describes" without ever seeing `fn`.

  The point is separation. The abstract-correctness proof lives on the `DecompRefine`
  side and mentions no machine; the refinement proof mentions `fn` and no
  registers; the certificate mentions registers and no spec. Each is checked
  on its own, and this file is the only place all three are in scope.
-/

module

public import Decomp.Certificate
public import DecompRefine.Nres

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64 DecompRefine

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
