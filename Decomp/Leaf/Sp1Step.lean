/-
  Decomp.Leaf.Sp1Step

  Where SP1 agrees with ZisK, instruction by instruction.

  `Decomp/Leaf/Core.lean` reduces "prove this leaf on SP1" to "show `stepSp1 s =
  step s` on the leaf's pre-states". This file discharges that for every
  instruction class:

  * **Plain** (not memory, not `ECALL`, not `EBREAK`): agreement on every state,
    upstream's `stepSp1_eq_step_of_fetch`. Covers 18 of this guest's 26
    constructors.
  * **Loads**: agreement on every state where ZisK's access predicate holds,
    because ZisK's address map is strictly inside SP1's. Seven constructors.
  * **Stores**: agreement where ZisK's predicate holds *and* the target holds
    no code (`noCodeAt`). The second conjunct is SP1's, ZisK never asks it, and
    nothing in a pre-state assertion can supply it -- so it is a hypothesis
    here, and turning it into something a triple can discharge is Phase 4's
    problem, not this file's. Four constructors.

  The `memOkSp1_*` lemmas are the per-constructor unfoldings of SP1's memory
  profile; they are what make the agreement proofs one line each.
-/

import Decomp.Leaf.Core

namespace Decomp

open RiscvZkvm.Rv64

/-! ## ZisK's address map sits inside SP1's

`Sp1Mem.lean` upstream has the dword form. The word, halfword and byte forms
are the same three-line `omega`. -/

theorem isValidMemAddrSp1_of_isValidMemAddr {a : Word} (h : isValidMemAddr a = true) :
    isValidMemAddrSp1 a = true := by
  unfold isValidMemAddr MEM_START MEM_END INPUT_MEM_START INPUT_MEM_END RAM_MEM_START
    RAM_MEM_END at h
  unfold isValidMemAddrSp1 SP1_MAX_MEMORY
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  omega

/-! ## `memOkSp1`, per constructor -/

@[simp] theorem memOkSp1_ld (s : MachineState) (rd rs1 : Reg) (off : BitVec 12) :
    memOkSp1 s (.LD rd rs1 off) = isValidDwordAccessSp1 (s.getReg rs1 + signExtend12 off) := by
  simp [memOkSp1, memAccess, alignedFor, isValidDwordAccessSp1]

@[simp] theorem memOkSp1_sd (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 12) :
    memOkSp1 s (.SD rs1 rs2 off) =
      (isValidDwordAccessSp1 (s.getReg rs1 + signExtend12 off) &&
        noCodeAt s (s.getReg rs1 + signExtend12 off) 8) := by
  simp [memOkSp1, memAccess, alignedFor, isValidDwordAccessSp1]

@[simp] theorem memOkSp1_lw (s : MachineState) (rd rs1 : Reg) (off : BitVec 12) :
    memOkSp1 s (.LW rd rs1 off) =
      (isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) &&
        isAligned4 (s.getReg rs1 + signExtend12 off)) := by
  simp [memOkSp1, memAccess, alignedFor]

@[simp] theorem memOkSp1_lwu (s : MachineState) (rd rs1 : Reg) (off : BitVec 12) :
    memOkSp1 s (.LWU rd rs1 off) =
      (isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) &&
        isAligned4 (s.getReg rs1 + signExtend12 off)) := by
  simp [memOkSp1, memAccess, alignedFor]

@[simp] theorem memOkSp1_sw (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 12) :
    memOkSp1 s (.SW rs1 rs2 off) =
      (isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) &&
        isAligned4 (s.getReg rs1 + signExtend12 off) &&
        noCodeAt s (s.getReg rs1 + signExtend12 off) 4) := by
  simp [memOkSp1, memAccess, alignedFor]

@[simp] theorem memOkSp1_lh (s : MachineState) (rd rs1 : Reg) (off : BitVec 12) :
    memOkSp1 s (.LH rd rs1 off) =
      (isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) &&
        isAligned2 (s.getReg rs1 + signExtend12 off)) := by
  simp [memOkSp1, memAccess, alignedFor]

@[simp] theorem memOkSp1_lhu (s : MachineState) (rd rs1 : Reg) (off : BitVec 12) :
    memOkSp1 s (.LHU rd rs1 off) =
      (isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) &&
        isAligned2 (s.getReg rs1 + signExtend12 off)) := by
  simp [memOkSp1, memAccess, alignedFor]

@[simp] theorem memOkSp1_sh (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 12) :
    memOkSp1 s (.SH rs1 rs2 off) =
      (isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) &&
        isAligned2 (s.getReg rs1 + signExtend12 off) &&
        noCodeAt s (s.getReg rs1 + signExtend12 off) 2) := by
  simp [memOkSp1, memAccess, alignedFor]

@[simp] theorem memOkSp1_lb (s : MachineState) (rd rs1 : Reg) (off : BitVec 12) :
    memOkSp1 s (.LB rd rs1 off) = isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) := by
  simp [memOkSp1, memAccess, alignedFor]

@[simp] theorem memOkSp1_lbu (s : MachineState) (rd rs1 : Reg) (off : BitVec 12) :
    memOkSp1 s (.LBU rd rs1 off) = isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) := by
  simp [memOkSp1, memAccess, alignedFor]

@[simp] theorem memOkSp1_sb (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 12) :
    memOkSp1 s (.SB rs1 rs2 off) =
      (isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) &&
        noCodeAt s (s.getReg rs1 + signExtend12 off) 1) := by
  simp [memOkSp1, memAccess, alignedFor]

/-- `stepSp1` on a memory instruction the profile admits: the catch-all arm of
    `stepSp1`, with its guard discharged. The `.CSRS` exclusion is needed because
    `isMemAccess` counts the ZisK accelerator call as a memory access. -/
theorem stepSp1_mem_of_memOk {s : MachineState} {i : Instr}
    (hfetch : s.code s.pc = some i) (hmem : i.isMemAccess = true)
    (hcsrs : ∀ c r, i ≠ .CSRS c r) (hok : memOkSp1 s i = true) :
    stepSp1 s = some (execInstrBr s i) := by
  unfold stepSp1; rw [hfetch]
  cases i <;> simp_all [Instr.isMemAccess]

/-! ## Plain instructions -/

/-- SP1 agrees with ZisK on every plain instruction, on every state. -/
theorem agreesOn_sp1_plain {entry : Word} {cr : CodeReq} {P : Assertion} {i : Instr}
    (hcr : cr entry = some i) (hmem : i.isMemAccess = false)
    (he : i ≠ .ECALL) (hb : i ≠ .EBREAK) :
    AgreesOn (Backend.stepper .sp1) entry cr P :=
  AgreesOn.of_fetch hcr fun _ hfetch _ => stepSp1_eq_step_of_fetch hfetch hmem he hb

theorem plainAgree_sp1 : (Backend.stepper .sp1).PlainAgree :=
  fun _ _ hfetch hmem he hb => stepSp1_eq_step_of_fetch hfetch hmem he hb

/-- Both backends agree with ZisK on plain instructions -- ZisK trivially, SP1
    by `stepSp1_eq_step_of_fetch`. This is the hypothesis a backend-generic
    proof takes, and `Examples/CountdownMachine.lean` is one. -/
theorem Backend.plainAgree : ∀ b : Backend, (Backend.stepper b).PlainAgree
  | .zisk => plainAgree_zisk
  | .sp1 => plainAgree_sp1

/-- **The uniform transfer.** Any one-step ZisK leaf for a plain instruction is
    an SP1 leaf, verbatim. -/
theorem cpsWithinOn_sp1_of_zisk_plain {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    {i : Instr} (hcr : cr entry = some i) (hmem : i.isMemAccess = false)
    (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    (hz : cpsTripleWithin 1 entry exit_ cr P Q) :
    cpsWithinOn .sp1 1 entry exit_ cr P Q :=
  cpsWithin_of_zisk_plain plainAgree_sp1 hcr hmem he hb hz

theorem cpsBranchOn_sp1_of_zisk_plain {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    {i : Instr} (hcr : cr entry = some i) (hmem : i.isMemAccess = false)
    (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    (hz : cpsBranchWithin 1 entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranchOn .sp1 1 entry cr P exit_t Q_t exit_f Q_f :=
  cpsBranch_of_zisk_plain plainAgree_sp1 hcr hmem he hb hz

/-! ## Loads: agreement wherever ZisK's predicate holds -/


theorem stepSp1_eq_step_ld {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.LD rd rs1 off))
    (hvalid : isValidDwordAccess (s.getReg rs1 + signExtend12 off) = true) :
    stepSp1 s = step s := by
  rw [step_ld hfetch hvalid]
  exact stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h)
    (by rw [memOkSp1_ld]; exact isValidDwordAccessSp1_of_isValidDwordAccess hvalid)

theorem stepSp1_eq_step_lw {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.LW rd rs1 off))
    (hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 off) = true) :
    stepSp1 s = step s := by
  rw [step_lw hfetch hvalid]
  refine stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) ?_
  simp only [isValidMemAccess, Bool.and_eq_true] at hvalid
  rw [memOkSp1_lw, Bool.and_eq_true]
  exact ⟨isValidMemAddrSp1_of_isValidMemAddr hvalid.1, hvalid.2⟩

theorem stepSp1_eq_step_lwu {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.LWU rd rs1 off))
    (hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 off) = true) :
    stepSp1 s = step s := by
  rw [step_lwu hfetch hvalid]
  refine stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) ?_
  simp only [isValidMemAccess, Bool.and_eq_true] at hvalid
  rw [memOkSp1_lwu, Bool.and_eq_true]
  exact ⟨isValidMemAddrSp1_of_isValidMemAddr hvalid.1, hvalid.2⟩

theorem stepSp1_eq_step_lh {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.LH rd rs1 off))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 off) = true) :
    stepSp1 s = step s := by
  rw [step_lh hfetch hvalid]
  refine stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) ?_
  simp only [isValidHalfwordAccess, Bool.and_eq_true] at hvalid
  rw [memOkSp1_lh, Bool.and_eq_true]
  exact ⟨isValidMemAddrSp1_of_isValidMemAddr hvalid.1, hvalid.2⟩

theorem stepSp1_eq_step_lhu {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.LHU rd rs1 off))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 off) = true) :
    stepSp1 s = step s := by
  rw [step_lhu hfetch hvalid]
  refine stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) ?_
  simp only [isValidHalfwordAccess, Bool.and_eq_true] at hvalid
  rw [memOkSp1_lhu, Bool.and_eq_true]
  exact ⟨isValidMemAddrSp1_of_isValidMemAddr hvalid.1, hvalid.2⟩

theorem stepSp1_eq_step_lb {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.LB rd rs1 off))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 off) = true) :
    stepSp1 s = step s := by
  rw [step_lb hfetch hvalid]
  refine stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) ?_
  simp [memOkSp1_lb, isValidMemAddrSp1_of_isValidMemAddr hvalid]

theorem stepSp1_eq_step_lbu {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.LBU rd rs1 off))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 off) = true) :
    stepSp1 s = step s := by
  rw [step_lbu hfetch hvalid]
  refine stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) ?_
  simp [memOkSp1_lbu, isValidMemAddrSp1_of_isValidMemAddr hvalid]

/-! ## Stores: agreement needs `noCodeAt`, which is SP1's alone -/

theorem stepSp1_eq_step_sd {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.SD rs1 rs2 off))
    (hvalid : isValidDwordAccess (s.getReg rs1 + signExtend12 off) = true)
    (hcode : noCodeAt s (s.getReg rs1 + signExtend12 off) 8 = true) :
    stepSp1 s = step s := by
  rw [step_sd hfetch hvalid]
  refine stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) ?_
  simp [memOkSp1_sd, isValidDwordAccessSp1_of_isValidDwordAccess hvalid, hcode]

theorem stepSp1_eq_step_sw {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.SW rs1 rs2 off))
    (hvalid : isValidMemAccess (s.getReg rs1 + signExtend12 off) = true)
    (hcode : noCodeAt s (s.getReg rs1 + signExtend12 off) 4 = true) :
    stepSp1 s = step s := by
  rw [step_sw hfetch hvalid]
  refine stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) ?_
  simp only [isValidMemAccess, Bool.and_eq_true] at hvalid
  rw [memOkSp1_sw, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨isValidMemAddrSp1_of_isValidMemAddr hvalid.1, hvalid.2⟩, hcode⟩

theorem stepSp1_eq_step_sh {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.SH rs1 rs2 off))
    (hvalid : isValidHalfwordAccess (s.getReg rs1 + signExtend12 off) = true)
    (hcode : noCodeAt s (s.getReg rs1 + signExtend12 off) 2 = true) :
    stepSp1 s = step s := by
  rw [step_sh hfetch hvalid]
  refine stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) ?_
  simp only [isValidHalfwordAccess, Bool.and_eq_true] at hvalid
  rw [memOkSp1_sh, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨isValidMemAddrSp1_of_isValidMemAddr hvalid.1, hvalid.2⟩, hcode⟩

theorem stepSp1_eq_step_sb {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (hfetch : s.code s.pc = some (.SB rs1 rs2 off))
    (hvalid : isValidByteAccess (s.getReg rs1 + signExtend12 off) = true)
    (hcode : noCodeAt s (s.getReg rs1 + signExtend12 off) 1 = true) :
    stepSp1 s = step s := by
  rw [step_sb hfetch hvalid]
  refine stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) ?_
  simp [memOkSp1_sb, isValidMemAddrSp1_of_isValidMemAddr hvalid, hcode]

end Decomp
