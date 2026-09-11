/-
  Decomp.Examples.Sp1Ecall

  The regression that says the backends are genuinely distinguished.

  This is the correction that cost the parent project a design, kept as a
  regression: `cpsTripleWithin` is stated over `stepN` = `stepOn .zisk`, and `step`'s
  ECALL dispatch handles only `t0 ∈ {0, 0x02, 0x10, 0xF2}`, otherwise falling
  through to `some (execInstrBr s .ECALL)` -- a silent pc advance. So a triple
  stated the old way about an SP1 guest would describe a machine in which
  `HINT_LEN`, `HINT_READ` and both Pallas precompiles do nothing at all: green,
  and about the wrong program.

  The cheapest possible witness that the new judgement does not have that
  problem is one `ecall` proved *both* ways, with different postconditions. That
  is what this file is. `hintLen_sentinel_sp1` and `hintLen_noop_zisk` are the
  same code at the same address under the same precondition, and
  `sentinel_ne_hintLen` shows their postconditions are incompatible -- so no
  single backend-agnostic judgement covers both, and `Decomp.cpsTotalOn` is
  right to be indexed.

  `HINT_LEN` with an empty stream is chosen because it is total: it cannot trap,
  so the triple is about the interesting difference rather than about a guard.
-/

module

public import Decomp.Triple

@[expose] public section

namespace Decomp.Examples

open RiscvZkvm.Rv64

/-! ## The fragment

One `ECALL` at `base`, entered with `t0 = HINT_LEN` and an exhausted hint
stream. Under SP1 this reports the `u64::MAX` sentinel in `t0`; under ZisK the
id is unrecognised and the instruction is inert. -/

/-- SP1 reports the sentinel: `t0` comes back `u64::MAX` because the hint stream
    is empty. This is the guest's own "no more input" test -- `main.rs` does
    `li a0, -1; ecall; beq t0, a0, …`. -/
theorem hintLen_sentinel_sp1 (base : Word) :
    cpsTotalOn .sp1 base (base + 4) (CodeReq.singleton base .ECALL)
      ((.x5 ↦ᵣ Sp1.HINT_LEN) ** privateInputIs [])
      ((.x5 ↦ᵣ (-1#64)) ** privateInputIs []) := by
  intro R hR s _hinv hcr hPR hpc
  subst hpc
  have hfetch : s.code s.pc = some .ECALL := CodeReq.singleton_satisfiedBy.mp hcr
  have hPR' := holdsFor_sepConj_assoc.mp hPR
  have ht0 : s.getReg .x5 = Sp1.HINT_LEN :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR')
  have hpi : s.privateInput = [] :=
    holdsFor_privateInputIs.mp
      (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hPR'))
  -- The stream is exhausted, so `HINT_LEN` reports the sentinel.
  have hfront : frontHintLen s = none := by simp [frontHintLen, hpi]
  have hhl : hintLen s = (s.setReg .x5 (-1#64)).setPC (s.pc + 4) := by
    simp [hintLen, hfront]
  have hstep : stepSp1 s = some ((s.setReg .x5 (-1#64)).setPC (s.pc + 4)) := by
    rw [← hhl]
    unfold stepSp1
    rw [hfetch]
    simp only [sp1Ecall, ht0, Sp1.isAccelId_hint_false.1]
    simp
  refine ⟨1, (s.setReg .x5 (-1#64)).setPC (s.pc + 4), ?_, ?_, ?_⟩
  · show ((Backend.stepper .sp1).next s).bind ((Backend.stepper .sp1).iter 0) = _
    rw [Backend.stepper_next, stepOn_sp1, hstep]
    rfl
  · simp [MachineState.setPC]
  · exact holdsFor_sepConj_assoc.mpr
      (holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hR))
        (holdsFor_sepConj_regIs_setReg (by simp) hPR'))

/-- ZisK does not recognise the id, so the same instruction leaves `t0` alone
    and merely advances the pc. `step_ecall_continue` upstream is the statement
    that this is what `step` does; here it is what a *triple* says. -/
theorem hintLen_noop_zisk (base : Word) :
    cpsTotalOn .zisk base (base + 4) (CodeReq.singleton base .ECALL)
      ((.x5 ↦ᵣ Sp1.HINT_LEN) ** privateInputIs [])
      ((.x5 ↦ᵣ Sp1.HINT_LEN) ** privateInputIs []) := by
  intro R hR s _hinv hcr hPR hpc
  subst hpc
  have hfetch : s.code s.pc = some .ECALL := CodeReq.singleton_satisfiedBy.mp hcr
  have hPR' := holdsFor_sepConj_assoc.mp hPR
  have ht0 : s.getReg .x5 = Sp1.HINT_LEN :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR')
  have hstep : step s = some (execInstrBr s .ECALL) := by
    rw [step_ecall_continue hfetch] <;> simp [ht0, Sp1.HINT_LEN]
  have hexec : execInstrBr s .ECALL = s.setPC (s.pc + 4) := by
    simp [execInstrBr]
  refine ⟨1, s.setPC (s.pc + 4), ?_, ?_, ?_⟩
  · show ((Backend.stepper .zisk).next s).bind ((Backend.stepper .zisk).iter 0) = _
    rw [Backend.stepper_next, stepOn_zisk, hstep, hexec]
    rfl
  · simp [MachineState.setPC]
  · exact holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) hR) hPR

/-- The two postconditions are incompatible, which is the whole point: there is
    no backend-agnostic reading of this instruction. `Decomp.cpsTotal` being
    indexed by a `Stepper` is what makes both statements expressible, and
    `Decomp.cpsWithinOn_zisk_iff` is what makes the second one agree with every
    triple already proved upstream. -/
theorem sentinel_ne_hintLen : (-1#64 : Word) ≠ Sp1.HINT_LEN := by decide

end Decomp.Examples
