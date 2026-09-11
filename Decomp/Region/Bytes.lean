/-
  Decomp.Region.Bytes

  Byte regions over any cell and any stepper: the multi-dword resource a byte
  loop reads from and writes into.

  Upstream's `MemRegion.lean` / `MemRegionStore.lean` build `bytesRegion` -- a
  `List (BitVec 8)` laid across consecutive `↦ₘ` cells -- and prove the two
  keystones: `bytesRegion_lbu_within` (`LBU` at byte `i` reads `bs[i]`) and
  `bytesRegion_sb_within` (`SB` at byte `i` yields `bs.set i b`). Both are a
  dword-framing lemma (`bytesRegion_dword_at`, `_set`) plus one leaf plus byte
  algebra (`extractByte_packBytes`, `packBytes_set`), and nothing in them
  depends on the cell being ZisK's except the cell itself and the leaf.

  Since riscv-zkvm PR #12 the region is `bytesRegionOn valid`, so this file
  restates the framing lemmas over `valid` and the two keystones over any
  `Stepper`, with the leaf taken from `Decomp/Leaf/Mem.lean` and the stepper's
  step fact as the hypothesis `hst` those leaves take. The byte algebra is
  imported unchanged. `Decomp/Region/Sp1.lean` instantiates at SP1.

  Read against upstream, the proofs are the same proofs. That is the point.
-/

import Decomp.Leaf.Mem
import RiscvZkvm.Rv64.Logic

namespace Decomp

open RiscvZkvm.Rv64

variable {valid : Word → Bool}

private theorem sepConj_assoc_eq {P Q R : Assertion} :
    ((P ** Q) ** R) = (P ** (Q ** R)) := by
  funext h; exact propext (sepConj_assoc h)

/-! ## Framing one dword out of a region -/

/-- Extract the `dw`-th dword cell from a region, framing the rest. Generic in
    the cell; upstream's `bytesRegion_dword_at` is the `isValidDwordAccess`
    instance. -/
theorem bytesRegionOn_dword_at (regionBase : Word) (bs : List (BitVec 8)) (dw : Nat)
    (hdw : 8 * dw < bs.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      bytesRegionOn valid regionBase bs
        = (front ** (memIsOn valid (regionBase + BitVec.ofNat 64 (8 * dw))
            (packBytes ((bs.drop (8 * dw)).take 8)) ** rest)) := by
  induction dw generalizing regionBase bs with
  | zero =>
    have hne : bs ≠ [] := by intro h; subst h; simp at hdw
    refine ⟨empAssertion, bytesRegionOn valid (regionBase + 8) (bs.drop 8),
      pcFree_emp, bytesRegionOn_pcFree _ _ _, ?_⟩
    rw [bytesRegionOn_eq_cons valid regionBase bs hne]
    simp [sepConj_emp_left']
  | succ k ih =>
    have hne : bs ≠ [] := by intro h; subst h; simp at hdw
    have hdw' : 8 * k < (bs.drop 8).length := by rw [List.length_drop]; omega
    obtain ⟨front', rest', hf', hr', heq'⟩ := ih (regionBase + 8) (bs.drop 8) hdw'
    have haddr : (regionBase + 8) + BitVec.ofNat 64 (8 * k)
        = regionBase + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h8]
      omega
    have hdrop : (bs.drop 8).drop (8 * k) = bs.drop (8 * (k + 1)) := by
      rw [List.drop_drop]; congr 1; omega
    refine ⟨memIsOn valid regionBase (packBytes (bs.take 8)) ** front', rest',
      pcFree_sepConj pcFree_memIsOn hf', hr', ?_⟩
    rw [bytesRegionOn_eq_cons valid regionBase bs hne, heq', haddr, hdrop, ← sepConj_assoc_eq]

/-- Frame the `q`-th dword for both `bs` and `bs.set (8q+r) b`, with shared
    `front`/`rest`. The store-side analogue; upstream's
    `bytesRegion_dword_at_set`. -/
theorem bytesRegionOn_dword_at_set (regionBase : Word) (bs : List (BitVec 8)) (q r : Nat)
    (b : BitVec 8) (hr : r < 8) (hi : 8 * q + r < bs.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      bytesRegionOn valid regionBase bs
        = (front ** (memIsOn valid (regionBase + BitVec.ofNat 64 (8 * q))
            (packBytes ((bs.drop (8 * q)).take 8)) ** rest))
      ∧ bytesRegionOn valid regionBase (bs.set (8 * q + r) b)
        = (front ** (memIsOn valid (regionBase + BitVec.ofNat 64 (8 * q))
            (packBytes (((bs.drop (8 * q)).take 8).set r b)) ** rest)) := by
  induction q generalizing regionBase bs with
  | zero =>
    have hne : bs ≠ [] := by intro h; subst h; simp at hi
    have hbspos : 0 < bs.length := List.length_pos_iff.mpr hne
    refine ⟨empAssertion, bytesRegionOn valid (regionBase + 8) (bs.drop 8), pcFree_emp,
      bytesRegionOn_pcFree _ _ _, ?_, ?_⟩
    · rw [bytesRegionOn_eq_cons valid regionBase bs hne,
        show regionBase + BitVec.ofNat 64 (8 * 0) = regionBase from by bv_omega]
      simp only [Nat.mul_zero, List.drop_zero, sepConj_emp_left']
    · have hset_ne : bs.set (8 * 0 + r) b ≠ [] :=
        List.ne_nil_of_length_pos (by rw [List.length_set]; exact hbspos)
      rw [bytesRegionOn_eq_cons valid regionBase (bs.set (8 * 0 + r) b) hset_ne]
      have htake : (bs.set (8 * 0 + r) b).take 8 = (bs.take 8).set (8 * 0 + r) b := List.take_set
      have hdrop : (bs.set (8 * 0 + r) b).drop 8 = bs.drop 8 := by
        rw [List.drop_set]; simp only [if_pos (show 8 * 0 + r < 8 from by omega)]
      rw [htake, hdrop,
        show regionBase + BitVec.ofNat 64 (8 * 0) = regionBase from by bv_omega]
      simp only [Nat.mul_zero, Nat.zero_add, List.drop_zero, sepConj_emp_left']
  | succ k ih =>
    have hne : bs ≠ [] := by intro h; subst h; simp at hi
    have hi' : 8 * k + r < (bs.drop 8).length := by
      rw [List.length_drop]; omega
    obtain ⟨front', rest', hf', hr', heq', heqset'⟩ := ih (regionBase + 8) (bs.drop 8) hi'
    have haddr : (regionBase + 8) + BitVec.ofNat 64 (8 * k)
        = regionBase + BitVec.ofNat 64 (8 * (k + 1)) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : BitVec 64).toNat = 8 := by decide
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h8]; omega
    have hdrop : (bs.drop 8).drop (8 * k) = bs.drop (8 * (k + 1)) := by
      rw [List.drop_drop]; congr 1; omega
    have htake_first : (bs.set (8 * (k + 1) + r) b).take 8 = bs.take 8 := by
      rw [List.take_set, List.set_eq_of_length_le (by rw [List.length_take]; omega)]
    have hdrop_first : (bs.set (8 * (k + 1) + r) b).drop 8 = (bs.drop 8).set (8 * k + r) b := by
      rw [List.drop_set]; simp only [show ¬ (8 * (k + 1) + r < 8) from by omega, if_false]
      congr 1; omega
    refine ⟨memIsOn valid regionBase (packBytes (bs.take 8)) ** front', rest',
      pcFree_sepConj pcFree_memIsOn hf', hr', ?_, ?_⟩
    · rw [bytesRegionOn_eq_cons valid regionBase bs hne, heq', haddr, hdrop, ← sepConj_assoc_eq]
    · have hset_ne : bs.set (8 * (k + 1) + r) b ≠ [] :=
        List.ne_nil_of_length_pos (by rw [List.length_set]; exact List.length_pos_iff.mpr hne)
      rw [bytesRegionOn_eq_cons valid regionBase (bs.set (8 * (k + 1) + r) b) hset_ne,
        htake_first, hdrop_first, heqset', haddr, hdrop, ← sepConj_assoc_eq]

/-! ## The keystones, over any stepper

`hst` is the leaf's step hypothesis specialised to this access: the stepper
takes the instruction's step on any admissible state whose address register
holds `regionBase + i` and whose containing dword cell is valid. The containing
dword is `regionBase + 8 * (i / 8)`, spelled out so a backend can discharge it
from its own memory profile. -/

variable {st : Stepper}

/-- **`LBU` reads byte `i` of the region.** -/
theorem bytesRegionOn_lbu_at (rd rs1 : Reg) (regionBase ptr vOld : Word)
    (offset : BitVec 12) (base : Word)
    (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LBU rd rs1 offset) →
      s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LBU rd rs1 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LBU rd rs1 offset))
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ vOld) **
        bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) **
        (rd ↦ᵣ ((bs[i]'hi).zeroExtend 64)) ** bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ := bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lbu := lbu_on (st := st) rd rs1 ptr vOld offset base
    dwordAddr wordVal hrd halign' hst
  rw [hptr] at lbu
  have hbyte : extractByte wordVal (byteOffset (regionBase + BitVec.ofNat 64 i)) = bs[i]'hi := by
    rw [byteOffset_add_ofNat_of_aligned halign hover, hwv,
        extractByte_packBytes _ _ (by omega)
          (by rw [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [hbyte] at lbu
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lbu)

/-- **`LBU rd, off(rd)` reads byte `i` of the region**, overwriting the pointer
    it read through.

    The same fact as `bytesRegionOn_lbu_at` for a *different* instruction: there
    `rd ≠ rs1` is forced by the postcondition keeping `rs1 ↦ᵣ ptr`, and here
    there is no such conjunct to keep, because the register that held the
    pointer now holds the byte. Two atoms in the footprint instead of three.
    `memcpy` index 507 is exactly this. -/
theorem bytesRegionOn_lbu_same_at (rd : Reg) (regionBase ptr : Word)
    (offset : BitVec 12) (base : Word)
    (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LBU rd rd offset) →
      s.getReg rd = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LBU rd rd offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LBU rd rd offset))
      ((rd ↦ᵣ ptr) ** bytesRegionOn valid regionBase bs)
      ((rd ↦ᵣ ((bs[i]'hi).zeroExtend 64)) ** bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lbu := lbu_same_on (st := st) rd ptr offset base dwordAddr wordVal hrd halign' hst
  rw [hptr] at lbu
  have hbyte : extractByte wordVal (byteOffset (regionBase + BitVec.ofNat 64 i)) = bs[i]'hi := by
    rw [byteOffset_add_ofNat_of_aligned halign hover, hwv,
        extractByte_packBytes _ _ (by omega)
          (by rw [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [hbyte] at lbu
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lbu)

/-- **`SB` writes byte `i` of the region**: `bs` becomes `bs.set i (v_data.truncate 8)`. -/
theorem bytesRegionOn_sb_at (rs1 rs2 : Reg) (regionBase ptr v_data : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SB rs1 rs2 offset) →
      s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.SB rs1 rs2 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SB rs1 rs2 offset))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
        bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
        bytesRegionOn valid regionBase (bs.set i (v_data.truncate 8))) := by
  have hr : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hi_eq : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegionOn_dword_at_set (valid := valid) regionBase bs (i / 8) (i % 8) (v_data.truncate 8) hr
      (by omega)
  rw [hi_eq] at heqset
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have sb := sb_on (st := st) rs1 rs2 ptr v_data offset base
    dwordAddr wordVal halign' hst
  rw [hptr] at sb
  have hbo : byteOffset (regionBase + BitVec.ofNat 64 i) = i % 8 :=
    byteOffset_add_ofNat_of_aligned halign hover
  have hchunk_len : i % 8 < ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, packBytes_set _ (i % 8) (v_data.truncate 8) hr hchunk_len] at sb
  rw [heq, heqset]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hrst) sb)
/-- **`LBU` reads byte `i` of the region** at offset zero. -/
theorem bytesRegionOn_lbu (rd rs1 : Reg) (regionBase vOld : Word) (base : Word)
    (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LBU rd rs1 0) →
      s.getReg rs1 = regionBase + BitVec.ofNat 64 i →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LBU rd rs1 0))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LBU rd rs1 0))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rd ↦ᵣ vOld) **
        bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) **
        (rd ↦ᵣ ((bs[i]'hi).zeroExtend 64)) ** bytesRegionOn valid regionBase bs) :=
  bytesRegionOn_lbu_at rd rs1 regionBase (regionBase + BitVec.ofNat 64 i) vOld 0 base bs i hrd
    (by show _ + (0 : Word) = _; bv_omega) halign hi hover hst

/-- **`SB` writes byte `i` of the region** at offset zero: the special case the
    loop bodies use, and the form the existing instances are stated over. -/
theorem bytesRegionOn_sb (rs1 rs2 : Reg) (regionBase v_data : Word) (base : Word)
    (bs : List (BitVec 8)) (i : Nat)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SB rs1 rs2 0) →
      s.getReg rs1 = regionBase + BitVec.ofNat 64 i →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.SB rs1 rs2 0))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SB rs1 rs2 0))
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rs2 ↦ᵣ v_data) **
        bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ (regionBase + BitVec.ofNat 64 i)) ** (rs2 ↦ᵣ v_data) **
        bytesRegionOn valid regionBase (bs.set i (v_data.truncate 8))) :=
  bytesRegionOn_sb_at rs1 rs2 regionBase (regionBase + BitVec.ofNat 64 i) v_data 0 base bs i
    (by show _ + (0 : Word) = _; bv_omega) halign hi hover hst


end Decomp
