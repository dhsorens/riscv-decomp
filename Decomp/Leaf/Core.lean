/-
  Decomp.Leaf.Core

  How a leaf spec proved on ZisK becomes a leaf spec on another backend.

  Upstream carries 133 one-instruction specs (`GenericSpecs`, `InstructionSpecs`,
  `ByteOps`, `HalfwordOps`, `WordOps`, …), every one of them stated as a
  `cpsTripleWithin 1 …` over ZisK's `step`. The plan was to hoist an `hstep`
  parameter into the ones that lack it and restate them over a `Stepper`. That
  is unnecessary. A one-step ZisK triple already pins the successor state: on
  every framed pre-state it says `stepN k s = some s'` for some `k ≤ 1`, and the
  proof of the triple is the only thing that knows *which* `s'`. So the whole
  backend-independent content of a leaf is recoverable from the ZisK theorem,
  and what a second backend owes is exactly one fact per pre-state:

      st.next s = step s

  `cpsWithin_of_zisk_one` turns a ZisK leaf plus that agreement into a leaf on
  `st`; `cpsBranch_of_zisk_one` does the same for branch leaves. No proof body
  is copied, and the 133 upstream proofs stay the single source of truth.

  ## Where agreement comes from

  For anything that is not a memory access, an `ECALL` or an `EBREAK`, SP1 and
  ZisK agree on every state (`stepSp1_eq_step_of_fetch`), so the eighteen
  non-memory constructors this guest uses transfer uniformly. For loads,
  agreement holds on every state the ZisK cell admits, because ZisK's address
  map is contained in SP1's (`isValidDwordAccessSp1_of_isValidDwordAccess`).
  For stores it holds only where SP1's `noCodeAt` does -- a fact about the code
  map that no pre-state assertion can carry, since `PartialState` has no code
  component. That is the one place transfer cannot be free:
  `Decomp/Leaf/Sp1Step.lean` states the store agreement with `noCodeAt` as an
  explicit hypothesis, and `Decomp/Leaf/Sp1Text.lean` discharges it from the
  judgement invariant `Stepper.inv` -- which `AgreesOn` receives, so a backend
  may lean on it.

  ## What transfer does not give you

  A transferred spec keeps its cells. A ZisK `↦ₘ` cell is unsatisfiable outside
  ZisK's zones, so a transferred load spec cannot name an SP1 heap address --
  the precondition typechecks and has no inhabitant. Specs over `memIsSp1` need
  their own proofs; those are the memory constructors in `Decomp/Leaf/Mem.lean`,
  written with `memIsOn`-generic bodies. Everything else -- 18 of 26
  constructors -- comes through here.
-/

module

public import Decomp.Triple

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64

/-- `st` agrees with ZisK's `step` on every framed pre-state of a leaf at
    `entry`. This is the one obligation a backend owes per leaf. -/
def AgreesOn (st : Stepper) (entry : Word) (cr : CodeReq) (P : Assertion) : Prop :=
  ∀ R : Assertion, R.pcFree → ∀ s, st.inv s → cr.SatisfiedBy s → (P ** R).holdsFor s →
    s.pc = entry → st.next s = step s

/-- Agreement is monotone in the code requirement and antitone in the
    precondition, as it should be: fewer pre-states, weaker obligation. -/
theorem AgreesOn.mono {st : Stepper} {entry : Word} {cr cr' : CodeReq} {P P' : Assertion}
    (hcr : ∀ a i, cr a = some i → cr' a = some i)
    (hP : ∀ h, P' h → P h)
    (h : AgreesOn st entry cr P) : AgreesOn st entry cr' P' := by
  intro R hR s hinv hsat hPR hpc
  refine h R hR s hinv (fun a i hi => hsat a i (hcr a i hi)) ?_ hpc
  obtain ⟨hh, hc, hp⟩ := hPR
  exact ⟨hh, hc, sepConj_mono_left hP hh hp⟩

/-- Agreement on the singleton code requirement follows from agreement on the
    fetched instruction alone, which is how every instance below is built. -/
theorem AgreesOn.of_fetch {st : Stepper} {entry : Word} {cr : CodeReq} {P : Assertion}
    {i : Instr} (hcr : cr entry = some i)
    (h : ∀ s, s.code s.pc = some i → s.pc = entry → st.next s = step s) :
    AgreesOn st entry cr P :=
  fun _ _ s _ hsat _ hpc => h s (by rw [hpc]; exact hsat entry i hcr) hpc

private theorem step_of_stepN_one {s s' : MachineState} (h : stepN 1 s = some s') :
    step s = some s' := by
  cases hs : step s with
  | none => simp [stepN, hs] at h
  | some t => simp [stepN, hs] at h; rw [h]

/-- **Transfer.** A one-step ZisK leaf holds on `st` wherever `st` agrees with
    `step` on the leaf's pre-states. The ZisK proof supplies the successor; the
    agreement says `st` takes the same one. -/
theorem cpsWithin_of_zisk_one {st : Stepper} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion}
    (hz : cpsTripleWithin 1 entry exit_ cr P Q) (hag : AgreesOn st entry cr P) :
    cpsWithin st 1 entry exit_ cr P Q := by
  intro R hR s hinv hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := hz R hR s hcr hPR hpc
  refine ⟨k, hk, s', ?_, hpc', hQR⟩
  match k, hk, hstep with
  | 0, _, hstep => exact hstep
  | 1, _, hstep =>
    rw [Stepper.iter_one, hag R hR s hinv hcr hPR hpc]
    exact step_of_stepN_one hstep
  | _ + 2, hk, _ => exact absurd hk (by omega)

/-- Transfer for branch leaves. -/
theorem cpsBranch_of_zisk_one {st : Stepper} {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (hz : cpsBranchWithin 1 entry cr P exit_t Q_t exit_f Q_f) (hag : AgreesOn st entry cr P) :
    cpsBranch st 1 entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hinv hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hcase⟩ := hz R hR s hcr hPR hpc
  refine ⟨k, hk, s', ?_, hcase⟩
  match k, hk, hstep with
  | 0, _, hstep => exact hstep
  | 1, _, hstep =>
    rw [Stepper.iter_one, hag R hR s hinv hcr hPR hpc]
    exact step_of_stepN_one hstep
  | _ + 2, hk, _ => exact absurd hk (by omega)

/-- ZisK agrees with itself; transfer to `.zisk` is `cpsWithinOn_zisk_iff.mpr`
    by another route. Here so the two bridges can be checked against each other. -/
theorem agreesOn_zisk (entry : Word) (cr : CodeReq) (P : Assertion) :
    AgreesOn (Backend.stepper .zisk) entry cr P :=
  fun _ _ _ _ _ _ _ => rfl

/-! ## Plain instructions, once for every backend

Not a memory access, not `ECALL`, not `EBREAK`: the instructions whose semantics
no backend has any say in. A stepper that agrees with ZisK on all of them, on
every state, gets every plain leaf for free. -/

/-- `st` agrees with ZisK on every plain instruction. -/
def Stepper.PlainAgree (st : Stepper) : Prop :=
  ∀ s (i : Instr), s.code s.pc = some i → i.isMemAccess = false → i ≠ .ECALL → i ≠ .EBREAK →
    st.next s = step s

theorem plainAgree_zisk : (Backend.stepper .zisk).PlainAgree :=
  fun _ _ _ _ _ _ => rfl

theorem CodeReq.singleton_self (a : Word) (i : Instr) : CodeReq.singleton a i a = some i := by
  simp [CodeReq.singleton]

/-- Any one-step ZisK leaf for a plain instruction, on any `PlainAgree` stepper. -/
theorem cpsWithin_of_zisk_plain {st : Stepper} (hst : st.PlainAgree)
    {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion} {i : Instr}
    (hcr : cr entry = some i) (hmem : i.isMemAccess = false)
    (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    (hz : cpsTripleWithin 1 entry exit_ cr P Q) :
    cpsWithin st 1 entry exit_ cr P Q :=
  cpsWithin_of_zisk_one hz
    (AgreesOn.of_fetch hcr fun s hfetch _ => hst s i hfetch hmem he hb)

/-- The branch form. -/
theorem cpsBranch_of_zisk_plain {st : Stepper} (hst : st.PlainAgree)
    {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion} {i : Instr}
    (hcr : cr entry = some i) (hmem : i.isMemAccess = false)
    (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    (hz : cpsBranchWithin 1 entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch st 1 entry cr P exit_t Q_t exit_f Q_f :=
  cpsBranch_of_zisk_one hz
    (AgreesOn.of_fetch hcr fun s hfetch _ => hst s i hfetch hmem he hb)

end Decomp
