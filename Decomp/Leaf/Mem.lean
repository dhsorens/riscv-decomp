/-
  Decomp.Leaf.Mem

  The memory leaves, once, over any cell and any stepper.

  Transfer (`Decomp/Leaf/Core.lean`) carries every upstream leaf to any
  backend -- but a transferred leaf keeps its `↦ₘ` cell, which is unsatisfiable
  off ZisK's zones, so nothing transferred can name an SP1 heap address. The
  memory leaves have to be re-proved with the cell as a parameter. That is this file: the twelve load/store forms over
  `memIsOn valid`, for any `valid`, on any `Stepper`.

  Each is upstream's `generic_*_spec_within` with two substitutions and nothing
  else:

  * `↦ₘ` becomes `memIsOn valid`, and `holdsFor_memIs_*` /
    `holdsFor_sepConj_memIs_setMem` become their `memIsOn` forms (upstream has
    them since riscv-zkvm PR #12);
  * `step_ld hfetch hvalid` becomes a hypothesis `hst`, which says the stepper
    takes the instruction's `execInstrBr` step on any admissible state whose
    address register and cell validity are what the precondition says. The
    caller discharges it from its backend's step lemma -- `Decomp/Leaf/Sp1Mem.lean`
    does so for SP1 from `stepSp1_mem_of_memOk`, using the judgement invariant
    for stores.

  The sub-dword forms take the containing doubleword's cell and `halign`, as
  upstream does; their address-validity side conditions (`isAligned4`,
  `isAligned2`, `noCodeAt`) belong to `hst`'s caller, because they are the
  backend's business, not the cell's.

  Read against upstream, these proofs are the same proofs. The point of having
  them here is that the cell is a parameter, which upstream's are not.
-/

import Decomp.Triple

namespace Decomp

open RiscvZkvm.Rv64

variable {st : Stepper} {valid : Word → Bool}

private theorem pcFree3 {r1 r2 : Reg} {a b c d : Word} :
    ((r1 ↦ᵣ a) ** (r2 ↦ᵣ b) ** memIsOn valid c d).pcFree :=
  pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs pcFree_memIsOn)

private theorem pcFree2 {r1 : Reg} {a c d : Word} :
    ((r1 ↦ᵣ a) ** memIsOn valid c d).pcFree :=
  pcFree_sepConj pcFree_regIs pcFree_memIsOn

/-! ## Doubleword -/

/-- `LD rd, rs1, off`: load the doubleword at the cell. -/
theorem ld_on (rd rs1 : Reg) (v_addr vOld memVal : Word) (off : BitVec 12) (base : Word)
    (hrd : rd ≠ .x0)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LD rd rs1 off) → s.getReg rs1 = v_addr →
      valid (v_addr + signExtend12 off) = true → st.next s = some (execInstrBr s (.LD rd rs1 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LD rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsOn valid (v_addr + signExtend12 off) memVal)
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ memVal) ** memIsOn valid (v_addr + signExtend12 off) memVal) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LD rd rs1 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem (v_addr + signExtend12 off) = memVal := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.LD rd rs1 off) = (s.setReg rd memVal).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setReg rd memVal).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg (v' := memVal) hrd h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h4

/-- `SD rs1, rs2, off`: store a doubleword to the cell. -/
theorem sd_on (rs1 rs2 : Reg) (v_addr v_data memOld : Word) (off : BitVec 12) (base : Word)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SD rs1 rs2 off) → s.getReg rs1 = v_addr →
      valid (v_addr + signExtend12 off) = true → st.next s = some (execInstrBr s (.SD rs1 rs2 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SD rs1 rs2 off))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsOn valid (v_addr + signExtend12 off) memOld)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsOn valid (v_addr + signExtend12 off) (v_data)) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SD rs1 rs2 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v_data :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem (v_addr + signExtend12 off) = memOld := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.SD rs1 rs2 off) =
      (s.setMem (v_addr + signExtend12 off) (v_data)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hrs2]
  refine ⟨1, Nat.le_refl 1, (s.setMem (v_addr + signExtend12 off) (v_data)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_memIsOn_setMem (v' := v_data) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h5

/-- `SD rs1, x0, off`: store zero. Two-atom precondition, as upstream. -/
theorem sd_x0_on (rs1 : Reg) (v_addr memOld : Word) (off : BitVec 12) (base : Word)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SD rs1 .x0 off) → s.getReg rs1 = v_addr →
      valid (v_addr + signExtend12 off) = true → st.next s = some (execInstrBr s (.SD rs1 .x0 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SD rs1 .x0 off))
      ((rs1 ↦ᵣ v_addr) ** memIsOn valid (v_addr + signExtend12 off) memOld)
      ((rs1 ↦ᵣ v_addr) ** memIsOn valid (v_addr + signExtend12 off) (0 : Word)) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SD rs1 .x0 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR))
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.SD rs1 .x0 off) =
      (s.setMem (v_addr + signExtend12 off) 0).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1]; rfl
  refine ⟨1, Nat.le_refl 1, (s.setMem (v_addr + signExtend12 off) 0).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_memIsOn_setMem (v' := (0 : Word)) h1
    have h3 := holdsFor_sepConj_pull_second.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree2 hR) h3

/-! ## Word -/

/-- `LW`: sign-extended 32-bit load from the containing doubleword. -/
theorem lw_on (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word)
    (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LW rd rs1 off) → s.getReg rs1 = v_addr →
      valid dwordAddr = true → st.next s = some (execInstrBr s (.LW rd rs1 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LW rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsOn valid dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).signExtend 64)) ** memIsOn valid dwordAddr wordVal) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LW rd rs1 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordVal := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.LW rd rs1 off) = (s.setReg rd ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).signExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getWord32_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setReg rd ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).signExtend 64)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg (v' := ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).signExtend 64)) hrd h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h4

/-- `LWU`: zero-extended 32-bit load from the containing doubleword. -/
theorem lwu_on (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word)
    (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LWU rd rs1 off) → s.getReg rs1 = v_addr →
      valid dwordAddr = true → st.next s = some (execInstrBr s (.LWU rd rs1 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LWU rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsOn valid dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).zeroExtend 64)) ** memIsOn valid dwordAddr wordVal) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LWU rd rs1 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordVal := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.LWU rd rs1 off) = (s.setReg rd ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).zeroExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getWord32_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setReg rd ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).zeroExtend 64)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg (v' := ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).zeroExtend 64)) hrd h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h4

/-- `SW`: 32-bit store into the containing doubleword. -/
theorem sw_on (rs1 rs2 : Reg) (v_addr v_data : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SW rs1 rs2 off) → s.getReg rs1 = v_addr →
      valid dwordAddr = true → st.next s = some (execInstrBr s (.SW rs1 rs2 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SW rs1 rs2 off))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsOn valid dwordAddr wordOld)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsOn valid dwordAddr (replaceWord32 wordOld ((byteOffset (v_addr + signExtend12 off)) / 4) (v_data.truncate 32))) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SW rs1 rs2 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v_data :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordOld := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.SW rs1 rs2 off) =
      (s.setMem dwordAddr (replaceWord32 wordOld ((byteOffset (v_addr + signExtend12 off)) / 4) (v_data.truncate 32))).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hrs2, setWord32_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setMem dwordAddr (replaceWord32 wordOld ((byteOffset (v_addr + signExtend12 off)) / 4) (v_data.truncate 32))).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_memIsOn_setMem (v' := replaceWord32 wordOld ((byteOffset (v_addr + signExtend12 off)) / 4) (v_data.truncate 32)) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h5

/-! ## Halfword -/

/-- `LH`: sign-extended 16-bit load. -/
theorem lh_on (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word)
    (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LH rd rs1 off) → s.getReg rs1 = v_addr →
      valid dwordAddr = true → st.next s = some (execInstrBr s (.LH rd rs1 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LH rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsOn valid dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).signExtend 64)) ** memIsOn valid dwordAddr wordVal) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LH rd rs1 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordVal := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.LH rd rs1 off) = (s.setReg rd ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).signExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getHalfword_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setReg rd ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).signExtend 64)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg (v' := ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).signExtend 64)) hrd h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h4

/-- `LHU`: zero-extended 16-bit load. -/
theorem lhu_on (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word)
    (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LHU rd rs1 off) → s.getReg rs1 = v_addr →
      valid dwordAddr = true → st.next s = some (execInstrBr s (.LHU rd rs1 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LHU rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsOn valid dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).zeroExtend 64)) ** memIsOn valid dwordAddr wordVal) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LHU rd rs1 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordVal := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.LHU rd rs1 off) = (s.setReg rd ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).zeroExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getHalfword_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setReg rd ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).zeroExtend 64)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg (v' := ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).zeroExtend 64)) hrd h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h4

/-- `SH`: 16-bit store into the containing doubleword. -/
theorem sh_on (rs1 rs2 : Reg) (v_addr v_data : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SH rs1 rs2 off) → s.getReg rs1 = v_addr →
      valid dwordAddr = true → st.next s = some (execInstrBr s (.SH rs1 rs2 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SH rs1 rs2 off))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsOn valid dwordAddr wordOld)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsOn valid dwordAddr (replaceHalfword wordOld ((byteOffset (v_addr + signExtend12 off)) / 2) (v_data.truncate 16))) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SH rs1 rs2 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v_data :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordOld := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.SH rs1 rs2 off) =
      (s.setMem dwordAddr (replaceHalfword wordOld ((byteOffset (v_addr + signExtend12 off)) / 2) (v_data.truncate 16))).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hrs2, setHalfword_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setMem dwordAddr (replaceHalfword wordOld ((byteOffset (v_addr + signExtend12 off)) / 2) (v_data.truncate 16))).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_memIsOn_setMem (v' := replaceHalfword wordOld ((byteOffset (v_addr + signExtend12 off)) / 2) (v_data.truncate 16)) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h5

/-! ## Byte -/

/-- `LB`: sign-extended byte load. -/
theorem lb_on (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word)
    (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LB rd rs1 off) → s.getReg rs1 = v_addr →
      valid dwordAddr = true → st.next s = some (execInstrBr s (.LB rd rs1 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LB rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsOn valid dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).signExtend 64)) ** memIsOn valid dwordAddr wordVal) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LB rd rs1 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordVal := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.LB rd rs1 off) = (s.setReg rd ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).signExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getByte_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setReg rd ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).signExtend 64)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg (v' := ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).signExtend 64)) hrd h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h4

/-- `LBU`: zero-extended byte load. -/
theorem lbu_on (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word)
    (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LBU rd rs1 off) → s.getReg rs1 = v_addr →
      valid dwordAddr = true → st.next s = some (execInstrBr s (.LBU rd rs1 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LBU rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsOn valid dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).zeroExtend 64)) ** memIsOn valid dwordAddr wordVal) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LBU rd rs1 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordVal := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.LBU rd rs1 off) = (s.setReg rd ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).zeroExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getByte_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setReg rd ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).zeroExtend 64)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h1a := holdsFor_sepConj_assoc.mp h1
    have h2 := holdsFor_sepConj_regIs_setReg (v' := ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).zeroExtend 64)) hrd h1a
    have h3 := holdsFor_sepConj_assoc.mpr h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h4

/-- `LBU rd, off(rd)`: the same instruction with the address register as the
    destination, which is what LLVM emits for the last byte of a copy
    (`memcpy` index 507 is `LBU x11, 0(x11)`).

    It needs its own leaf rather than an instance of `lbu_on`: that theorem's
    postcondition keeps `rs1 ↦ᵣ v_addr`, and here the address register is gone
    -- overwritten by the byte. So the precondition owns **two** atoms, not
    three, and a caller with a spare register cannot fake it by framing. -/
theorem lbu_same_on (rd : Reg) (v_addr : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word)
    (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LBU rd rd off) → s.getReg rd = v_addr →
      valid dwordAddr = true → st.next s = some (execInstrBr s (.LBU rd rd off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LBU rd rd off))
      ((rd ↦ᵣ v_addr) ** memIsOn valid dwordAddr wordVal)
      ((rd ↦ᵣ ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).zeroExtend 64))
        ** memIsOn valid dwordAddr wordVal) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.LBU rd rd off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rd = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_left hPR))
  have hmem : s.getMem dwordAddr = wordVal := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.LBU rd rd off) =
      (s.setReg rd ((extractByte wordVal
        (byteOffset (v_addr + signExtend12 off))).zeroExtend 64)).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, getByte_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setReg rd ((extractByte wordVal
    (byteOffset (v_addr + signExtend12 off))).zeroExtend 64)).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_assoc.mp hPR
    have h2 := holdsFor_sepConj_regIs_setReg (v' := ((extractByte wordVal
      (byteOffset (v_addr + signExtend12 off))).zeroExtend 64)) hrd h1
    have h3 := holdsFor_sepConj_assoc.mpr h2
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree2 hR) h3

/-- `SB`: byte store into the containing doubleword. -/
theorem sb_on (rs1 rs2 : Reg) (v_addr v_data : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SB rs1 rs2 off) → s.getReg rs1 = v_addr →
      valid dwordAddr = true → st.next s = some (execInstrBr s (.SB rs1 rs2 off))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SB rs1 rs2 off))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsOn valid dwordAddr wordOld)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsOn valid dwordAddr (replaceByte wordOld (byteOffset (v_addr + signExtend12 off)) (v_data.truncate 8))) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some (.SB rs1 rs2 off) := CodeReq.singleton_satisfiedBy.mp hcr
  have hrs1 : s.getReg rs1 = v_addr :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  have hrs2 : s.getReg rs2 = v_data :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right
      (holdsFor_sepConj_elim_left hPR)))
  have hcell := holdsFor_memIsOn.mp (holdsFor_sepConj_elim_right
    (holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)))
  have hmem : s.getMem dwordAddr = wordOld := hcell.1
  have hstep' := hst s hinv hfetch hrs1 hcell.2
  have hexec' : execInstrBr s (.SB rs1 rs2 off) =
      (s.setMem dwordAddr (replaceByte wordOld (byteOffset (v_addr + signExtend12 off)) (v_data.truncate 8))).setPC (s.pc + 4) := by
    simp only [execInstrBr, hrs1, hrs2, setByte_eq]; rw [halign, hmem]
  refine ⟨1, Nat.le_refl 1, (s.setMem dwordAddr (replaceByte wordOld (byteOffset (v_addr + signExtend12 off)) (v_data.truncate 8))).setPC (s.pc + 4), ?_, rfl, ?_⟩
  · show (st.next s).bind (st.iter 0) = some _
    rw [hstep', hexec']; rfl
  · have h1 := holdsFor_sepConj_pull_second.mp hPR
    have h2 := holdsFor_sepConj_pull_second.mp h1
    have h3 := holdsFor_sepConj_memIsOn_setMem (v' := replaceByte wordOld (byteOffset (v_addr + signExtend12 off)) (v_data.truncate 8)) h2
    have h4 := holdsFor_sepConj_pull_second.mpr h3
    have h5 := holdsFor_sepConj_pull_second.mpr h4
    exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree3 hR) h5

end Decomp
