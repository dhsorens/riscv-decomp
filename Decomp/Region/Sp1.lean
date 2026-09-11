/-
  Decomp.Region.Sp1

  Byte regions with SP1's cell, on SP1 with its code confined to a window.

  `bytesRegionSp1 base bs` is `bs` laid across `memIsSp1` cells, so a region
  on the heap is inhabited where a `bytesRegion` (ZisK cells) is not. The two
  keystones from `Decomp/Region/Bytes.lean` and the wide stores from
  `Decomp/Region/Wide.lean` are instantiated with the step facts
  `Decomp/Leaf/Sp1Mem.lean` uses: a valid containing dword puts the access in
  SP1's addressable space, and a store additionally needs its bytes off the
  code window.
-/

module

public import Decomp.Region.Wide
public import Decomp.Leaf.Sp1Mem

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64

/-- `bs` laid across consecutive `memIsSp1` cells from `base`. -/
abbrev bytesRegionSp1 (base : Word) (bs : List (BitVec 8)) : Assertion :=
  bytesRegionOn isValidDwordAccessSp1 base bs

variable {lo hi : Nat}

private theorem ptr_eq (a : Word) : a + signExtend12 (0 : BitVec 12) = a := by
  show _ + (0 : Word) = _; bv_omega

/-- `LBU` at byte `i` of an SP1 region: no side condition beyond the region. -/
theorem bytesRegionSp1_lbu (rd rs1 : Reg) (regionBase vOld : Word) (base : Word)
    (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (halign : regionBase.toNat % 8 = 0) (hlt : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LBU rd rs1 0))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rd ↦ᵣ vOld) **
        bytesRegionSp1 regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
        (rd ↦ᵣ ((bs[i]'hlt).zeroExtend 64)) ** bytesRegionSp1 regionBase bs) :=
  bytesRegionOn_lbu rd rs1 regionBase vOld base bs i hrd halign hlt hover
    fun _ _ hfetch hrs1 hv =>
      stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
        rw [memOkSp1_lbu, hrs1, ptr_eq]
        exact isValidMemAddrSp1_of_alignToDword
          (by rw [alignToDword_add_ofNat_of_aligned halign hover]; exact hv))

/-- `SB` at byte `i` of an SP1 region: the byte must be off the code window. -/
theorem bytesRegionSp1_sb (rs1 rs2 : Reg) (regionBase v_data : Word) (base : Word)
    (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hlt : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hoff : OffText lo hi (regionBase + BitVec.ofNat 64 i) 1) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SB rs1 rs2 0))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rs2 ↦ᵣ v_data) **
        bytesRegionSp1 regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rs2 ↦ᵣ v_data) **
        bytesRegionSp1 regionBase (bs.set i (v_data.truncate 8))) :=
  bytesRegionOn_sb rs1 rs2 regionBase v_data base bs i halign hlt hover
    fun _ hinv hfetch hrs1 hv =>
      stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
        rw [memOkSp1_sb, hrs1, ptr_eq, Bool.and_eq_true]
        exact ⟨isValidMemAddrSp1_of_alignToDword
            (by rw [alignToDword_add_ofNat_of_aligned halign hover]; exact hv),
          noCodeAt_of_codeWithin (by decide) hinv hoff⟩)

/-! ## Wide stores

The address is `ptr + offset` with the caller's `hptr`, as in
`Decomp/Region/Wide.lean`. The `OffText` width is the store's. -/

/-- A 4-aligned offset from a dword-aligned base is 4-aligned. -/
private theorem isAligned4_add_ofNat {base : Word} {i : Nat}
    (halign : base.toNat % 8 = 0) (hi4 : 4 ∣ i) (hover : base.toNat + i < 2 ^ 64) :
    isAligned4 (base + BitVec.ofNat 64 i) = true := by
  rw [isAligned4_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mod_eq_of_lt hover, beq_iff_eq]
  omega

/-- `SW` at 4-aligned index `i` of an SP1 region: the four bytes must be off the
    code window. -/
theorem bytesRegionSp1_sw_at (rs1 rs2 : Reg) (regionBase ptr v_data : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi4 : 4 ∣ i) (hlt : i + 4 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hoff : OffText lo hi (regionBase + BitVec.ofNat 64 i) 4) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SW rs1 rs2 offset))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** bytesRegionSp1 regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
        bytesRegionSp1 regionBase (setBytes bs i (word32Bytes (v_data.truncate 32)))) :=
  bytesRegionOn_sw_at rs1 rs2 regionBase ptr v_data offset base bs i hptr halign hi4 hlt hover
    fun _ hinv hfetch hrs1 hv =>
      stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
        rw [memOkSp1_sw, hrs1, hptr, Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨isValidMemAddrSp1_of_alignToDword
            (by rw [alignToDword_add_ofNat_of_aligned halign hover]; exact hv),
          isAligned4_add_ofNat halign hi4 hover⟩,
          noCodeAt_of_codeWithin (by decide) hinv hoff⟩)

/-- A 2-aligned offset from a dword-aligned base is 2-aligned. -/
private theorem isAligned2_add_ofNat {base : Word} {i : Nat}
    (halign : base.toNat % 8 = 0) (hi2 : 2 ∣ i) (hover : base.toNat + i < 2 ^ 64) :
    isAligned2 (base + BitVec.ofNat 64 i) = true := by
  unfold isAligned2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mod_eq_of_lt hover, beq_iff_eq]
  omega

/-- `SH` at 2-aligned index `i` of an SP1 region: the two bytes must be off the
    code window. -/
theorem bytesRegionSp1_sh_at (rs1 rs2 : Reg) (regionBase ptr v_data : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi2 : 2 ∣ i) (hlt : i + 2 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hoff : OffText lo hi (regionBase + BitVec.ofNat 64 i) 2) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SH rs1 rs2 offset))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** bytesRegionSp1 regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
        bytesRegionSp1 regionBase (setBytes bs i (halfwordBytes (v_data.truncate 16)))) :=
  bytesRegionOn_sh_at rs1 rs2 regionBase ptr v_data offset base bs i hptr halign hi2 hlt hover
    fun _ hinv hfetch hrs1 hv =>
      stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
        rw [memOkSp1_sh, hrs1, hptr, Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨isValidMemAddrSp1_of_alignToDword
            (by rw [alignToDword_add_ofNat_of_aligned halign hover]; exact hv),
          isAligned2_add_ofNat halign hi2 hover⟩,
          noCodeAt_of_codeWithin (by decide) hinv hoff⟩)

/-- `SD` at 8-aligned index `i` of an SP1 region: the doubleword must be off the
    code window. The store's own cell supplies its validity. -/
theorem bytesRegionSp1_sd_at (rs1 rs2 : Reg) (regionBase ptr v_data : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (hi8 : 8 ∣ i) (hlt : i + 8 ≤ bs.length)
    (hoff : OffText lo hi (regionBase + BitVec.ofNat 64 i) 8) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SD rs1 rs2 offset))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** bytesRegionSp1 regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
        bytesRegionSp1 regionBase (setBytes bs i (dwordBytes v_data))) :=
  bytesRegionOn_sd_at rs1 rs2 regionBase ptr v_data offset base bs i hptr hi8 hlt
    fun _ hinv hfetch hrs1 hv =>
      stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
        rw [memOkSp1_sd, hrs1, hptr, Bool.and_eq_true]
        exact ⟨hv, noCodeAt_of_codeWithin (by decide) hinv hoff⟩)

/-! ## Byte accesses at an immediate offset

A compiled `memcpy` tail copies with `LBU rd, 1(rs1)` and `SB rs1, rs2, 1`, i.e. through
one base register with immediate offsets, the way compiled code addresses a
small run of bytes. These are the offset-taking forms of the two keystones
above; the offset-zero versions are their special case. -/

/-- `lbu rd, off(rs1)` reading byte `i` of an SP1 region. -/
theorem bytesRegionSp1_lbu_at (rd rs1 : Reg) (regionBase ptr vOld : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hlt : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LBU rd rs1 offset))
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ vOld) ** bytesRegionSp1 regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ ((bs[i]'hlt).zeroExtend 64)) ** bytesRegionSp1 regionBase bs) :=
  bytesRegionOn_lbu_at rd rs1 regionBase ptr vOld offset base bs i hrd hptr halign hlt hover
    fun _ _ hfetch hrs1 hv =>
      stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
        rw [memOkSp1_lbu, hrs1, hptr]
        exact isValidMemAddrSp1_of_alignToDword
          (by rw [alignToDword_add_ofNat_of_aligned halign hover]; exact hv))

/-- `LBU rd, off(rd)` at byte `i` of an SP1 region: the pointer register is the
    destination, so the region is the only other atom in the footprint. -/
theorem bytesRegionSp1_lbu_same_at (rd : Reg) (regionBase ptr : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hlt : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.LBU rd rd offset))
      ((rd ↦ᵣ ptr) ** bytesRegionSp1 regionBase bs)
      ((rd ↦ᵣ ((bs[i]'hlt).zeroExtend 64)) ** bytesRegionSp1 regionBase bs) :=
  bytesRegionOn_lbu_same_at rd regionBase ptr offset base bs i hrd hptr halign hlt hover
    fun _ _ hfetch hrs1 hv =>
      stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
        rw [memOkSp1_lbu, hrs1, hptr]
        exact isValidMemAddrSp1_of_alignToDword
          (by rw [alignToDword_add_ofNat_of_aligned halign hover]; exact hv))

/-- `sb rs2, off(rs1)` writing byte `i` of an SP1 region. -/
theorem bytesRegionSp1_sb_at (rs1 rs2 : Reg) (regionBase ptr v_data : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hlt : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hoff : OffText lo hi (regionBase + BitVec.ofNat 64 i) 1) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base (.SB rs1 rs2 offset))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** bytesRegionSp1 regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
        bytesRegionSp1 regionBase (bs.set i (v_data.truncate 8))) :=
  bytesRegionOn_sb_at rs1 rs2 regionBase ptr v_data offset base bs i hptr halign hlt hover
    fun _ hinv hfetch hrs1 hv =>
      stepSp1_mem_of_memOk hfetch rfl (fun _ _ h => Instr.noConfusion h) (by
        rw [memOkSp1_sb, hrs1, hptr, Bool.and_eq_true]
        exact ⟨isValidMemAddrSp1_of_alignToDword
            (by rw [alignToDword_add_ofNat_of_aligned halign hover]; exact hv),
          noCodeAt_of_codeWithin (by decide) hinv hoff⟩)

end Decomp
