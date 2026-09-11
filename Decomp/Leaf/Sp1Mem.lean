/-
  Decomp.Leaf.Sp1Mem

  The memory leaves on SP1, with SP1's cell.

  `Decomp/Leaf/Mem.lean` proves each load/store form once, over `memIsOn valid`
  and any stepper, against a hypothesis `hst` that the stepper takes the
  instruction's step on admissible states. This file discharges `hst` for SP1
  from `stepSp1_mem_of_memOk` and the `memOkSp1_*` unfoldings, with
  `valid := isValidDwordAccessSp1` -- so the cell is `memIsSp1`, which *can*
  name the heap -- and on `Sp1Text lo hi`, whose invariant is what a store's
  `noCodeAt` is discharged from (`noCodeAt_of_codeWithin`).

  Side conditions, and where they come from:

  * **Loads** need only the cell: an SP1-valid doubleword puts every byte of
    it in the addressable space (`isValidMemAddrSp1_of_alignToDword`).
    `LW`/`LWU` and `LH`/`LHU` additionally take the natural-alignment fact
    `memOkSp1` asks for, which the cell cannot supply because the cell is the
    containing doubleword.
  * **Stores** additionally take `OffText lo hi addr w`: the access lies off
    the code window. For a typical guest that is free in both directions -- a
    heap above `.text` discharges `OffText`'s second disjunct and a stack below
    it the first -- but the two discharge lemmas are currently restated per
    guest rather than living here (ROADMAP, "Generalise the `OffText`
    discharges").

  Everything here is a one-line instantiation; the proofs are in `Mem.lean` and
  the step lemmas in `Sp1Step.lean`.
-/

module

public import Decomp.Leaf.Mem
public import Decomp.Leaf.Sp1Text

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64

/-! ## Address arithmetic for the containing doubleword -/

/-- `alignToDword` clears the low three bits. Same bit-by-bit proof as
    `toNat_align4`, since `bv_omega` cannot see through `&&&`. -/
theorem toNat_alignToDword (a : Word) : (alignToDword a).toNat = a.toNat - a.toNat % 8 := by
  unfold alignToDword
  rw [BitVec.toNat_and]
  have h7 : (~~~7#64).toNat = (2 ^ 61 - 1) <<< 3 := by decide
  rw [h7]
  have ha := a.isLt
  have hsub : a.toNat - a.toNat % 8 = (a.toNat / 2 ^ 3) <<< 3 := by
    rw [Nat.shiftLeft_eq]; omega
  rw [hsub]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hi : 3 ≤ i
  · have : i - 3 + 3 = i := by omega
    rw [this]
    by_cases hi64 : i < 64
    · simp [hi]; omega
    · have hfalse : a.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hfalse]
  · simp [hi]

/-- If the containing doubleword is SP1-valid, so is every byte address in it:
    `SP1_MAX_MEMORY` is 8-aligned, so the doubleword ends below it. -/
theorem isValidMemAddrSp1_of_alignToDword {a : Word}
    (h : isValidDwordAccessSp1 (alignToDword a) = true) : isValidMemAddrSp1 a = true := by
  unfold isValidDwordAccessSp1 isValidMemAddrSp1 SP1_MAX_MEMORY isAligned8 at h
  unfold isValidMemAddrSp1 SP1_MAX_MEMORY
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
  have := toNat_alignToDword a
  omega

variable {lo hi : Nat}

/-! ## Doubleword -/

theorem ld_sp1Mem (rd rs1 : Reg) (v_addr vOld memVal : Word) (off : BitVec 12) (base : Word)
    (hrd : rd ≠ .x0) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LD rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsSp1 (v_addr + signExtend12 off) memVal)
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ memVal) ** memIsSp1 (v_addr + signExtend12 off) memVal) :=
  ld_on rd rs1 v_addr vOld memVal off base hrd fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h)
      (by rw [memOkSp1_ld, hrs1]; exact hv)


/-- `LD rd, off(rd)` on SP1: `ld_same_on` with `hst` discharged. -/
theorem ld_same_sp1Mem (rd : Reg) (v_addr memVal : Word) (off : BitVec 12) (base : Word)
    (hrd : rd ≠ .x0) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LD rd rd off))
      ((rd ↦ᵣ v_addr) ** memIsSp1 (v_addr + signExtend12 off) memVal)
      ((rd ↦ᵣ memVal) ** memIsSp1 (v_addr + signExtend12 off) memVal) :=
  ld_same_on rd v_addr memVal off base hrd fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h)
      (by rw [memOkSp1_ld, hrs1]; exact hv)

theorem sd_sp1Mem (rs1 rs2 : Reg) (v_addr v_data memOld : Word) (off : BitVec 12) (base : Word)
    (hoff : OffText lo hi (v_addr + signExtend12 off) 8) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SD rs1 rs2 off))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsSp1 (v_addr + signExtend12 off) memOld)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsSp1 (v_addr + signExtend12 off) v_data) :=
  sd_on rs1 rs2 v_addr v_data memOld off base fun _ hinv hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_sd, hrs1, Bool.and_eq_true]
      exact ⟨hv, noCodeAt_of_codeWithin (by decide) hinv hoff⟩)

theorem sd_x0_sp1Mem (rs1 : Reg) (v_addr memOld : Word) (off : BitVec 12) (base : Word)
    (hoff : OffText lo hi (v_addr + signExtend12 off) 8) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SD rs1 .x0 off))
      ((rs1 ↦ᵣ v_addr) ** memIsSp1 (v_addr + signExtend12 off) memOld)
      ((rs1 ↦ᵣ v_addr) ** memIsSp1 (v_addr + signExtend12 off) (0 : Word)) :=
  sd_x0_on rs1 v_addr memOld off base fun _ hinv hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_sd, hrs1, Bool.and_eq_true]
      exact ⟨hv, noCodeAt_of_codeWithin (by decide) hinv hoff⟩)

/-! ## Word -/

theorem lw_sp1Mem (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (h4 : isAligned4 (v_addr + signExtend12 off) = true) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LW rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsSp1 dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) **
        (rd ↦ᵣ ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).signExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lw_on rd rs1 v_addr vOld off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lw, hrs1, Bool.and_eq_true]
      exact ⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv), h4⟩)


/-- `LW rd, off(rd)` on SP1: `lw_same_on` with `hst` discharged. -/
theorem lw_same_sp1Mem (rd : Reg) (v_addr : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (h4 : isAligned4 (v_addr + signExtend12 off) = true) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LW rd rd off))
      ((rd ↦ᵣ v_addr) ** memIsSp1 dwordAddr wordVal)
      ((rd ↦ᵣ ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).signExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lw_same_on rd v_addr off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lw, hrs1, Bool.and_eq_true]
      exact ⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv), h4⟩)

theorem lwu_sp1Mem (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (h4 : isAligned4 (v_addr + signExtend12 off) = true) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LWU rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsSp1 dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) **
        (rd ↦ᵣ ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).zeroExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lwu_on rd rs1 v_addr vOld off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lwu, hrs1, Bool.and_eq_true]
      exact ⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv), h4⟩)


/-- `LWU rd, off(rd)` on SP1: `lwu_same_on` with `hst` discharged. -/
theorem lwu_same_sp1Mem (rd : Reg) (v_addr : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (h4 : isAligned4 (v_addr + signExtend12 off) = true) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LWU rd rd off))
      ((rd ↦ᵣ v_addr) ** memIsSp1 dwordAddr wordVal)
      ((rd ↦ᵣ ((extractWord32 wordVal ((byteOffset (v_addr + signExtend12 off)) / 4)).zeroExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lwu_same_on rd v_addr off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lwu, hrs1, Bool.and_eq_true]
      exact ⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv), h4⟩)

theorem sw_sp1Mem (rs1 rs2 : Reg) (v_addr v_data : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (h4 : isAligned4 (v_addr + signExtend12 off) = true)
    (hoff : OffText lo hi (v_addr + signExtend12 off) 4) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SW rs1 rs2 off))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsSp1 dwordAddr wordOld)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
        memIsSp1 dwordAddr
          (replaceWord32 wordOld ((byteOffset (v_addr + signExtend12 off)) / 4) (v_data.truncate 32))) :=
  sw_on rs1 rs2 v_addr v_data off base dwordAddr wordOld halign fun _ hinv hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_sw, hrs1, Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv), h4⟩,
        noCodeAt_of_codeWithin (by decide) hinv hoff⟩)

/-! ## Halfword -/

theorem lh_sp1Mem (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (h2 : isAligned2 (v_addr + signExtend12 off) = true) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LH rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsSp1 dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) **
        (rd ↦ᵣ ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).signExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lh_on rd rs1 v_addr vOld off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lh, hrs1, Bool.and_eq_true]
      exact ⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv), h2⟩)


/-- `LH rd, off(rd)` on SP1: `lh_same_on` with `hst` discharged. -/
theorem lh_same_sp1Mem (rd : Reg) (v_addr : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (h2 : isAligned2 (v_addr + signExtend12 off) = true) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LH rd rd off))
      ((rd ↦ᵣ v_addr) ** memIsSp1 dwordAddr wordVal)
      ((rd ↦ᵣ ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).signExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lh_same_on rd v_addr off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lh, hrs1, Bool.and_eq_true]
      exact ⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv), h2⟩)

theorem lhu_sp1Mem (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (h2 : isAligned2 (v_addr + signExtend12 off) = true) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LHU rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsSp1 dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) **
        (rd ↦ᵣ ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).zeroExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lhu_on rd rs1 v_addr vOld off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lhu, hrs1, Bool.and_eq_true]
      exact ⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv), h2⟩)


/-- `LHU rd, off(rd)` on SP1: `lhu_same_on` with `hst` discharged. -/
theorem lhu_same_sp1Mem (rd : Reg) (v_addr : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (h2 : isAligned2 (v_addr + signExtend12 off) = true) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LHU rd rd off))
      ((rd ↦ᵣ v_addr) ** memIsSp1 dwordAddr wordVal)
      ((rd ↦ᵣ ((extractHalfword wordVal ((byteOffset (v_addr + signExtend12 off)) / 2)).zeroExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lhu_same_on rd v_addr off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lhu, hrs1, Bool.and_eq_true]
      exact ⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv), h2⟩)

theorem sh_sp1Mem (rs1 rs2 : Reg) (v_addr v_data : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (h2 : isAligned2 (v_addr + signExtend12 off) = true)
    (hoff : OffText lo hi (v_addr + signExtend12 off) 2) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SH rs1 rs2 off))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsSp1 dwordAddr wordOld)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
        memIsSp1 dwordAddr
          (replaceHalfword wordOld ((byteOffset (v_addr + signExtend12 off)) / 2) (v_data.truncate 16))) :=
  sh_on rs1 rs2 v_addr v_data off base dwordAddr wordOld halign fun _ hinv hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_sh, hrs1, Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv), h2⟩,
        noCodeAt_of_codeWithin (by decide) hinv hoff⟩)

/-! ## Byte -/

theorem lb_sp1Mem (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LB rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsSp1 dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) **
        (rd ↦ᵣ ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).signExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lb_on rd rs1 v_addr vOld off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lb, hrs1]
      exact isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv))


/-- `LB rd, off(rd)` on SP1: `lb_same_on` with `hst` discharged. -/
theorem lb_same_sp1Mem (rd : Reg) (v_addr : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LB rd rd off))
      ((rd ↦ᵣ v_addr) ** memIsSp1 dwordAddr wordVal)
      ((rd ↦ᵣ ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).signExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lb_same_on rd v_addr off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lb, hrs1]
      exact isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv))

theorem lbu_sp1Mem (rd rs1 : Reg) (v_addr vOld : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LBU rd rs1 off))
      ((rs1 ↦ᵣ v_addr) ** (rd ↦ᵣ vOld) ** memIsSp1 dwordAddr wordVal)
      ((rs1 ↦ᵣ v_addr) **
        (rd ↦ᵣ ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).zeroExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lbu_on rd rs1 v_addr vOld off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lbu, hrs1]
      exact isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv))


/-- `LBU rd, off(rd)` on SP1: `lbu_same_on` with `hst` discharged. -/
theorem lbu_same_sp1Mem (rd : Reg) (v_addr : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordVal : Word) (hrd : rd ≠ .x0)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LBU rd rd off))
      ((rd ↦ᵣ v_addr) ** memIsSp1 dwordAddr wordVal)
      ((rd ↦ᵣ ((extractByte wordVal (byteOffset (v_addr + signExtend12 off))).zeroExtend 64)) **
        memIsSp1 dwordAddr wordVal) :=
  lbu_same_on rd v_addr off base dwordAddr wordVal hrd halign fun _ _ hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_lbu, hrs1]
      exact isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv))

theorem sb_sp1Mem (rs1 rs2 : Reg) (v_addr v_data : Word) (off : BitVec 12) (base : Word)
    (dwordAddr wordOld : Word)
    (halign : alignToDword (v_addr + signExtend12 off) = dwordAddr)
    (hoff : OffText lo hi (v_addr + signExtend12 off) 1) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SB rs1 rs2 off))
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) ** memIsSp1 dwordAddr wordOld)
      ((rs1 ↦ᵣ v_addr) ** (rs2 ↦ᵣ v_data) **
        memIsSp1 dwordAddr
          (replaceByte wordOld (byteOffset (v_addr + signExtend12 off)) (v_data.truncate 8))) :=
  sb_on rs1 rs2 v_addr v_data off base dwordAddr wordOld halign fun _ hinv hfetch hrs1 hv =>
    stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
      rw [memOkSp1_sb, hrs1, Bool.and_eq_true]
      exact ⟨isValidMemAddrSp1_of_alignToDword (by rw [halign]; exact hv),
        noCodeAt_of_codeWithin (by decide) hinv hoff⟩)

end Decomp
