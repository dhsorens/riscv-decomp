/-
  Decomp.Leaf.Sp1Text

  SP1 with its code confined to a window -- the stepper SP1 store triples are
  stated on, and why there has to be one.

  `memOkSp1` traps a store whose target holds code (`noCodeAt`). `cpsWithin`
  ranges over every state whose `code` map merely *contains* the `CodeReq`
  (`CodeReq.SatisfiedBy` is positive-only), so among those states are ones with
  junk code at the store target, on which `stepSp1` traps and any store triple
  on `Backend.stepper .sp1` is simply false. No leaf hypothesis can exclude
  them, and no precondition can either: `PartialState` has no code component.
  Restricting the stepper to `if s.code = img then … else none` does not help --
  the transfer lemma then fails on exactly those states.

  What is true is a statement about SP1 *with its code confined to a known
  window*: `Stepper.inv` carries `CodeWithin lo hi`, preserved by
  `code_stepSp1`, and a store off the window is then safe by
  `noCodeAt_of_codeWithin`. The invariant is a *property* of the code map, not
  an equality with a particular one -- deliberately, because
  a project's `CodeReq` covers only the functions it has emitted while
  the machine's `code` covers all of `.text`. Equality with a `CodeReq` would be
  false of every real loaded state; `CodeWithin lo hi` is what stores need, and
  is what a loader establishes for an image with one executable `PT_LOAD`. That
  last step is observation glue, not a theorem -- `Interpreter.load` is
  imperative -- so a downstream project discharges it by stating a
  `codeConfined` predicate, proving it implies this invariant, and *evaluating*
  it on the interpreter's own `load` of its ELF.

  Two honest limits of the invariant. It is weaker than "this image": it says
  nothing about *extra* code inside the window, so it kills junk code only
  outside it -- the same positive-only weakness `CodeReq` already has. And a
  store to a hole *inside* the window (this ELF has three, the `unimp`s) is not
  covered by `OffText`; `noCodeAt` is true there, but nothing here proves it.
  Off-window stores are the ones that matter for the stack and the heap.

  ## What this file gives and does not give

  A ZisK-celled store leaf transferred here keeps its `↦ₘ` cell, which is
  satisfiable only at ZisK-valid addresses: the stack, `.rodata`, the input
  zone. That is where most of a typical guest's stores land, so it is worth
  having. It is **vacuous** on an SP1 heap address, where `↦ₘ` has no
  inhabitant -- a heap store needs a `memIsSp1`-celled leaf, which is
  `Decomp/Leaf/Sp1Mem.lean`.
-/

import Decomp.Leaf.Sp1Step

namespace Decomp

open RiscvZkvm.Rv64

/-! ## The invariant and the stepper -/

/-- Code lives only in `[lo, hi)`. -/
def CodeWithin (lo hi : Nat) (s : MachineState) : Prop :=
  ∀ a : Word, s.code a ≠ none → lo ≤ a.toNat ∧ a.toNat < hi

theorem CodeWithin.of_code_eq {lo hi : Nat} {s s' : MachineState}
    (h : CodeWithin lo hi s) (heq : s'.code = s.code) : CodeWithin lo hi s' :=
  fun a ha => h a (heq ▸ ha)

/-- SP1, on states whose code is confined to `[lo, hi)`. Same `next` as
    `Backend.stepper .sp1`; only the invariant differs. -/
def Sp1Text (lo hi : Nat) : Stepper where
  next := stepSp1
  code_next := code_stepSp1
  inv := CodeWithin lo hi
  inv_next h hs := h.of_code_eq (code_stepSp1 hs)

@[simp] theorem Sp1Text_next (lo hi : Nat) : (Sp1Text lo hi).next = stepSp1 := rfl

/-- Same runs as the unrestricted SP1 stepper: the invariant restricts which
    states a *judgement* speaks about, never what the machine does. -/
theorem Sp1Text_iter (lo hi : Nat) (n : Nat) (s : MachineState) :
    (Sp1Text lo hi).iter n s = (Backend.stepper .sp1).iter n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Stepper.iter_succ, Stepper.iter_succ, Sp1Text_next, Backend.stepper_next, stepOn_sp1]
    cases stepSp1 s with
    | none => rfl
    | some s' => simpa using ih s'

/-- Anything true on the unrestricted SP1 stepper is true here. Loads, plain
    instructions and every rule in `Decomp/Triple.lean` come through this. -/
theorem cpsWithin_sp1Text_of_sp1 {lo hi : Nat} {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} (h : cpsWithinOn .sp1 n entry exit_ cr P Q) :
    cpsWithin (Sp1Text lo hi) n entry exit_ cr P Q := by
  intro R hR s _ hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s trivial hcr hPR hpc
  exact ⟨k, hk, s', (Sp1Text_iter lo hi k s).trans hstep, hpc', hQR⟩

theorem cpsBranch_sp1Text_of_sp1 {lo hi : Nat} {n : Nat} {entry : Word} {cr : CodeReq}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (h : cpsBranchOn .sp1 n entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch (Sp1Text lo hi) n entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s _ hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hcase⟩ := h R hR s trivial hcr hPR hpc
  exact ⟨k, hk, s', (Sp1Text_iter lo hi k s).trans hstep, hcase⟩

theorem cpsTotal_sp1Text_of_sp1 {lo hi : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} (h : cpsTotalOn .sp1 entry exit_ cr P Q) :
    cpsTotal (Sp1Text lo hi) entry exit_ cr P Q := by
  intro R hR s _ hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ := h R hR s trivial hcr hPR hpc
  exact ⟨k, s', (Sp1Text_iter lo hi k s).trans hstep, hpc', hQR⟩

/-- Plain instructions transfer here directly, too. -/
theorem plainAgree_sp1Text (lo hi : Nat) : (Sp1Text lo hi).PlainAgree :=
  fun _ _ hfetch hmem he hb => stepSp1_eq_step_of_fetch hfetch hmem he hb

/-! ## The store guard, from the invariant -/

/-- `align4` clears the low two bits. Out of `bv_omega`'s reach because of the
    `&&&`, so proved bit by bit. -/
theorem toNat_align4 (a : Word) : (align4 a).toNat = a.toNat - a.toNat % 4 := by
  unfold align4
  rw [BitVec.toNat_and]
  have h3 : (~~~3#64).toNat = (2 ^ 62 - 1) <<< 2 := by decide
  rw [h3]
  have ha := a.isLt
  have hsub : a.toNat - a.toNat % 4 = (a.toNat / 2 ^ 2) <<< 2 := by
    rw [Nat.shiftLeft_eq]; omega
  rw [hsub]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hi : 2 ≤ i
  · have : i - 2 + 2 = i := by omega
    rw [this]
    by_cases hi64 : i < 64
    · simp [hi]; omega
    · have hfalse : a.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hfalse]
  · simp [hi]

/-- A `w`-byte access at `a` lies wholly below the window, or wholly at or
    above it (the low bound rounded down to a word, as `noCodeAt` does). The
    `2 ^ 64` bound rules out wrap-around. -/
def OffText (lo hi : Nat) (a : Word) (w : Nat) : Prop :=
  a.toNat + w ≤ 2 ^ 64 ∧ (a.toNat + w ≤ lo ∨ hi ≤ a.toNat - a.toNat % 4)

/-- **The store guard.** Off the window, `noCodeAt` holds on every state the
    invariant admits. This is the fact the plan expected to thread as a
    hypothesis and could not; it is a consequence of `Stepper.inv` instead. -/
theorem noCodeAt_of_codeWithin {lo hi : Nat} {s : MachineState} {a : Word} {w : Nat}
    (hw : 0 < w) (hinv : CodeWithin lo hi s) (hoff : OffText lo hi a w) :
    noCodeAt s a w = true := by
  obtain ⟨hbound, hcase⟩ := hoff
  simp only [noCodeAt, List.all_eq_true, List.mem_range, Option.isNone_iff_eq_none]
  intro i hi_lt
  cases hc : s.code (align4 a + BitVec.ofNat 64 (4 * i)) with
  | none => rfl
  | some _ =>
  exfalso
  have hin := hinv _ (by rw [hc]; exact Option.some_ne_none _)
  have hA := a.isLt
  have hw1 : w - 1 < 2 ^ 64 := by omega
  have hlo := toNat_align4 a
  have hE : (a + BitVec.ofNat 64 (w - 1)).toNat = a.toNat + (w - 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hhi := toNat_align4 (a + BitVec.ofNat 64 (w - 1))
  rw [hE] at hhi
  rw [BitVec.toNat_sub] at hi_lt
  have h4i : 4 * i < 2 ^ 64 := by omega
  have hx : (align4 a + BitVec.ofNat 64 (4 * i)).toNat = (align4 a).toNat + 4 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4i, Nat.mod_eq_of_lt (by omega)]
  rw [hx] at hin
  omega

/-! ## ZisK-celled stores, transferred

Agreement for a store needs the guard, which needs the invariant; so these are
stated on `Sp1Text`, not on `Backend.stepper .sp1`. -/

theorem agreesOn_sp1Text_sd {lo hi : Nat} {base : Word} {rs1 rs2 : Reg}
    {v_addr v_data memOld : Word} {off : BitVec 12}
    (hoff : OffText lo hi (v_addr + signExtend12 off) 8) :
    AgreesOn (Sp1Text lo hi) base (CodeReq.singleton base (.SD rs1 rs2 off))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 off) ↦ₘ memOld)) := by
  intro _ _ s hinv hcr hPR hpc
  have hfetch : s.code s.pc = some (.SD rs1 rs2 off) := by
    rw [hpc]; exact CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hvalid : isValidDwordAccess (v_addr + signExtend12 off) = true :=
    holdsFor_memIs_isValidDwordAccess (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  rw [← hrs1] at hvalid hoff
  exact stepSp1_eq_step_sd hfetch hvalid (noCodeAt_of_codeWithin (by decide) hinv hoff)

/-- `SD rs1, rs2, off` on SP1, from upstream's ZisK leaf. The target must be off
    the code window; the ZisK cell in the precondition supplies the rest. -/
theorem sd_sp1Text {lo hi : Nat} (rs1 rs2 : Reg) (v_addr v_data memOld : Word)
    (off : BitVec 12) (base : Word)
    (hoff : OffText lo hi (v_addr + signExtend12 off) 8) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SD rs1 rs2 off))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 off) ↦ₘ memOld))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** ((v_addr + signExtend12 off) ↦ₘ v_data)) :=
  cpsWithin_of_zisk_one (generic_sd_spec_within rs1 rs2 v_addr v_data memOld off base)
    (agreesOn_sp1Text_sd hoff)

theorem agreesOn_sp1Text_sd_x0 {lo hi : Nat} {base : Word} {rs1 : Reg}
    {v_addr memOld : Word} {off : BitVec 12}
    (hoff : OffText lo hi (v_addr + signExtend12 off) 8) :
    AgreesOn (Sp1Text lo hi) base (CodeReq.singleton base (.SD rs1 .x0 off))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 off) ↦ₘ memOld)) := by
  intro _ _ s hinv hcr hPR hpc
  have hfetch : s.code s.pc = some (.SD rs1 .x0 off) := by
    rw [hpc]; exact CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hvalid : isValidDwordAccess (v_addr + signExtend12 off) = true :=
    holdsFor_memIs_isValidDwordAccess (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR))
  rw [← hrs1] at hvalid hoff
  exact stepSp1_eq_step_sd hfetch hvalid (noCodeAt_of_codeWithin (by decide) hinv hoff)

/-- `SD rs1, x0, off`: store zero. -/
theorem sd_x0_sp1Text {lo hi : Nat} (rs1 : Reg) (v_addr memOld : Word)
    (off : BitVec 12) (base : Word)
    (hoff : OffText lo hi (v_addr + signExtend12 off) 8) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SD rs1 .x0 off))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 off) ↦ₘ memOld))
      ((rs1 ↦ᵣ v_addr) ** ((v_addr + signExtend12 off) ↦ₘ (0 : Word))) :=
  cpsWithin_of_zisk_one (generic_sd_x0_spec_within rs1 v_addr memOld off base)
    (agreesOn_sp1Text_sd_x0 hoff)

/-! ## ZisK-celled loads, transferred

Loads need no guard, so these live on the unrestricted stepper and reach
`Sp1Text` through `cpsWithin_sp1Text_of_sp1`. -/

theorem agreesOn_sp1_ld {base : Word} {rd rs1 : Reg} {v_addr vOld memVal : Word}
    {off : BitVec 12} :
    AgreesOn (Backend.stepper .sp1) base (CodeReq.singleton base (.LD rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** ((v_addr + signExtend12 off) ↦ₘ memVal)) := by
  intro _ _ s _ hcr hPR hpc
  have hfetch : s.code s.pc = some (.LD rd rs1 off) := by
    rw [hpc]; exact CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hvalid : isValidDwordAccess (v_addr + signExtend12 off) = true :=
    holdsFor_memIs_isValidDwordAccess (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  rw [← hrs1] at hvalid
  exact stepSp1_eq_step_ld hfetch hvalid

/-- `LD rd, rs1, off` on SP1, from upstream's ZisK leaf. No side condition:
    ZisK's address map is inside SP1's. -/
theorem ld_sp1 (rd rs1 : Reg) (v_addr vOld memVal : Word) (off : BitVec 12) (base : Word)
    (hrd : rd ≠ .x0) :
    cpsWithinOn .sp1 1 base (base + 4) (CodeReq.singleton base (.LD rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** ((v_addr + signExtend12 off) ↦ₘ memVal))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ memVal) ** ((v_addr + signExtend12 off) ↦ₘ memVal)) :=
  cpsWithin_of_zisk_one (generic_ld_spec_within rd rs1 v_addr vOld memVal off base hrd)
    agreesOn_sp1_ld

end Decomp
