/-
  Decomp.Region.WideLoad

  Wide loads out of a byte region, and the same-register family at the
  region layer.

  `Decomp/Region/Bytes.lean` reads one byte at a region index (`LBU`);
  `Decomp/Region/Wide.lean` writes two, four or eight. This file reads them:
  `LB`, `LH`, `LHU`, `LW`, `LWU` at a 1-, 2- or 4-aligned index of a
  dword-aligned region, and `LD` at an 8-aligned index of any region. Each
  keystone comes in the ordinary three-atom form (`bytesRegionOn_lw_at`:
  `rs1 ↦ᵣ ptr ** rd ↦ᵣ vOld ** region`) and the same-register two-atom form
  (`bytesRegionOn_lw_same_at`: `rd ↦ᵣ ptr ** region`, the pointer register
  overwritten by what it pointed at), which is what `ROADMAP.md` item 2 asked
  for and `Bytes.lean`'s `LBU` pair already showed for one instruction.

  ## The algebra, run the other way

  A store splices a payload into the containing dword's byte list
  (`packBytes_setBytes_word32`: `replaceWord32` on the packed dword is
  `setBytes` on the chunk). A load is the converse: the `8 * n`-bit field at
  byte offset `r` of a packed chunk is the packing of the chunk's window
  `(chunk.drop r).take n` (`packBytes_window`, one bit-level lemma), and
  `extractWord32` / `extractHalfword` are its `n = 4` / `n = 2` cases. So an
  `LW` at index `i` delivers `packBytes ((bs.drop i).take 4)`, truncated to
  32 bits and sign- or zero-extended as the instruction says. Upstream has
  no wide region loads and none of this algebra; the store side's
  `eq_of_forall_extractByte` route does not apply because the result is
  narrower than a dword, so the proof goes bit by bit through `getLsbD`.

  ## Shape

  Every proof is `Bytes.lean`'s: frame the containing dword out of the region
  (`bytesRegionOn_dword_at`), apply the leaf from `Decomp/Leaf/Mem.lean` at
  that cell, rewrite the leaf's `extract*` of the packed chunk into the
  window of `bs`, frame back. The same-register twin is the same proof with
  the same-register leaf; it differs by the leaf's name and two atoms.

  Side conditions are the store side's: the region base is dword-aligned and
  does not wrap, the index is aligned to the access width and the access
  stays inside `bs`. `LD` needs neither alignment nor overflow bound, as `SD`
  does not: it hits one of the region's own cells exactly. All hold for any
  `valid` and any stepper whose step on the instruction is `execInstrBr`
  (`hst`); `Decomp/Region/Sp1.lean` discharges `hst` on SP1.
-/

module

public import Decomp.Region.Wide

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64

variable {valid : Word → Bool}

/-! ## The load-side splice algebra -/

/-- Bit `q` of a word is bit `q % 8` of its byte `q / 8`. -/
theorem getLsbD_eq_extractByte (w : Word) (q : Nat) :
    w.getLsbD q = (extractByte w (q / 8)).getLsbD (q % 8) := by
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  have : q / 8 * 8 + q % 8 = q := by omega
  rw [this]
  simp [Nat.mod_lt]

/-- Bit `q` of a packed byte list is bit `q % 8` of byte `q / 8`. -/
theorem getLsbD_packBytes (bytes : List (BitVec 8)) (q : Nat) (hq : q < 64) :
    (packBytes bytes).getLsbD q = (getByteAt bytes (q / 8)).getLsbD (q % 8) := by
  rw [getLsbD_eq_extractByte, extractByte_packBytes_total _ _ (by omega)]

/-- Byte `j` of the `n`-byte window at `r`. -/
theorem getByteAt_drop_take (bytes : List (BitVec 8)) (r n j : Nat) (hj : j < n)
    (hlen : r + n ≤ bytes.length) :
    getByteAt ((bytes.drop r).take n) j = getByteAt bytes (r + j) := by
  have h1 : j < ((bytes.drop r).take n).length := by
    rw [List.length_take, List.length_drop]; omega
  have h2 : r + j < bytes.length := by omega
  simp only [getByteAt, h1, h2, ↓reduceDIte, List.getElem_take, List.getElem_drop]

/-- **The load-side splice algebra**: the `8 * n`-bit field at byte offset `r`
    of a packed chunk is the packing of the window `(chunk.drop r).take n`.
    The converse of `packBytes_setBytes_*`, and the one lemma the wide loads
    need. -/
theorem packBytes_window (chunk : List (BitVec 8)) (r n : Nat)
    (hr8 : r + n ≤ 8) (hlen : r + n ≤ chunk.length) :
    ((packBytes chunk) >>> (r * 8)).truncate (8 * n)
      = (packBytes ((chunk.drop r).take n)).truncate (8 * n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  simp only [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hp,
    decide_true, Bool.true_and]
  rw [getLsbD_packBytes _ _ (by omega), getLsbD_packBytes _ _ (by omega),
    getByteAt_drop_take _ _ _ _ (by omega) hlen]
  have h1 : (r * 8 + p) / 8 = r + p / 8 := by omega
  have h2 : (r * 8 + p) % 8 = p % 8 := by omega
  rw [h1, h2]

/-- `extractWord32` of a packed chunk at a 4-aligned byte offset. -/
theorem extractWord32_packBytes (chunk : List (BitVec 8)) (r : Nat)
    (hr4 : 4 ∣ r) (hr8 : r + 4 ≤ 8) (hlen : r + 4 ≤ chunk.length) :
    extractWord32 (packBytes chunk) (r / 4)
      = (packBytes ((chunk.drop r).take 4)).truncate 32 := by
  have h : r / 4 * 32 = r * 8 := by obtain ⟨m, rfl⟩ := hr4; omega
  show ((packBytes chunk) >>> (r / 4 * 32)).truncate 32 = _
  rw [h]
  exact packBytes_window chunk r 4 hr8 hlen

/-- `extractHalfword` of a packed chunk at a 2-aligned byte offset. -/
theorem extractHalfword_packBytes (chunk : List (BitVec 8)) (r : Nat)
    (hr2 : 2 ∣ r) (hr8 : r + 2 ≤ 8) (hlen : r + 2 ≤ chunk.length) :
    extractHalfword (packBytes chunk) (r / 2)
      = (packBytes ((chunk.drop r).take 2)).truncate 16 := by
  have h : r / 2 * 16 = r * 8 := by obtain ⟨m, rfl⟩ := hr2; omega
  show ((packBytes chunk) >>> (r / 2 * 16)).truncate 16 = _
  rw [h]
  exact packBytes_window chunk r 2 hr8 hlen

/-- The window of the containing chunk is the window of the list. -/
theorem drop_take_chunk (bs : List (BitVec 8)) (i n : Nat) (hn : i % 8 + n ≤ 8) :
    (((bs.drop (8 * (i / 8))).take 8).drop (i % 8)).take n = (bs.drop i).take n := by
  rw [List.drop_take, List.drop_drop, List.take_take]
  have h1 : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  have h2 : min n (8 - i % 8) = n := by omega
  rw [h1, h2]

/-- A 4-aligned index sits in its dword with room for four bytes. -/
theorem mod_four_room {i : Nat} (hi4 : 4 ∣ i) : 4 ∣ i % 8 ∧ i % 8 + 4 ≤ 8 := by
  have hr4 : 4 ∣ i % 8 := Nat.dvd_mod_iff (by decide) |>.mpr hi4
  refine ⟨hr4, ?_⟩
  obtain ⟨m, hm⟩ := hr4
  have := Nat.mod_lt i (show 0 < 8 by decide)
  omega

/-- A 2-aligned index sits in its dword with room for two bytes. -/
theorem mod_two_room {i : Nat} (hi2 : 2 ∣ i) : 2 ∣ i % 8 ∧ i % 8 + 2 ≤ 8 := by
  have hr2 : 2 ∣ i % 8 := Nat.dvd_mod_iff (by decide) |>.mpr hi2
  refine ⟨hr2, ?_⟩
  obtain ⟨m, hm⟩ := hr2
  have := Nat.mod_lt i (show 0 < 8 by decide)
  omega

/-! ## The wide loads, over any stepper

`hst` is as in `Bytes.lean`: the stepper takes the instruction's step on any
admissible state whose address register holds `ptr` and whose containing dword
cell `regionBase + 8 * (i / 8)` is valid. -/

variable {st : Stepper}

/-- **`LW` reads the 4 bytes at index `i`**, sign-extended. -/
theorem bytesRegionOn_lw_at (rd rs1 : Reg) (regionBase ptr vOld : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi4 : 4 ∣ i) (hlt : i + 4 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LW rd rs1 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LW rd rs1 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LW rd rs1 offset))
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ vOld) ** bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) **
        (rd ↦ᵣ ((packBytes ((bs.drop i).take 4)).truncate 32).signExtend 64) **
        bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lw := lw_on (st := st) rd rs1 ptr vOld offset base dwordAddr wordVal hrd halign' hst
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  obtain ⟨hr4, hr8⟩ := mod_four_room hi4
  have hchunk_len : i % 8 + 4 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, extractWord32_packBytes _ _ hr4 hr8 hchunk_len, drop_take_chunk bs i 4 hr8] at lw
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lw)

/-- **`LWU` reads the 4 bytes at index `i`**, zero-extended. -/
theorem bytesRegionOn_lwu_at (rd rs1 : Reg) (regionBase ptr vOld : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi4 : 4 ∣ i) (hlt : i + 4 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LWU rd rs1 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LWU rd rs1 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LWU rd rs1 offset))
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ vOld) ** bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) **
        (rd ↦ᵣ ((packBytes ((bs.drop i).take 4)).truncate 32).zeroExtend 64) **
        bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lwu := lwu_on (st := st) rd rs1 ptr vOld offset base dwordAddr wordVal hrd halign' hst
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  obtain ⟨hr4, hr8⟩ := mod_four_room hi4
  have hchunk_len : i % 8 + 4 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, extractWord32_packBytes _ _ hr4 hr8 hchunk_len, drop_take_chunk bs i 4 hr8] at lwu
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lwu)

/-- **`LH` reads the 2 bytes at index `i`**, sign-extended. -/
theorem bytesRegionOn_lh_at (rd rs1 : Reg) (regionBase ptr vOld : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi2 : 2 ∣ i) (hlt : i + 2 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LH rd rs1 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LH rd rs1 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LH rd rs1 offset))
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ vOld) ** bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) **
        (rd ↦ᵣ ((packBytes ((bs.drop i).take 2)).truncate 16).signExtend 64) **
        bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lh := lh_on (st := st) rd rs1 ptr vOld offset base dwordAddr wordVal hrd halign' hst
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  obtain ⟨hr2, hr8⟩ := mod_two_room hi2
  have hchunk_len : i % 8 + 2 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, extractHalfword_packBytes _ _ hr2 hr8 hchunk_len, drop_take_chunk bs i 2 hr8] at lh
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lh)

/-- **`LHU` reads the 2 bytes at index `i`**, zero-extended. -/
theorem bytesRegionOn_lhu_at (rd rs1 : Reg) (regionBase ptr vOld : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi2 : 2 ∣ i) (hlt : i + 2 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LHU rd rs1 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LHU rd rs1 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LHU rd rs1 offset))
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ vOld) ** bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) **
        (rd ↦ᵣ ((packBytes ((bs.drop i).take 2)).truncate 16).zeroExtend 64) **
        bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lhu := lhu_on (st := st) rd rs1 ptr vOld offset base dwordAddr wordVal hrd halign' hst
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  obtain ⟨hr2, hr8⟩ := mod_two_room hi2
  have hchunk_len : i % 8 + 2 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, extractHalfword_packBytes _ _ hr2 hr8 hchunk_len, drop_take_chunk bs i 2 hr8] at lhu
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lhu)

/-- **`LB` reads byte `i` of the region**, sign-extended: `LBU`'s sibling. -/
theorem bytesRegionOn_lb_at (rd rs1 : Reg) (regionBase ptr vOld : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LB rd rs1 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LB rd rs1 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LB rd rs1 offset))
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ vOld) ** bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ ((bs[i]'hi).signExtend 64)) **
        bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lb := lb_on (st := st) rd rs1 ptr vOld offset base dwordAddr wordVal hrd halign' hst
  rw [hptr] at lb
  have hbyte : extractByte wordVal (byteOffset (regionBase + BitVec.ofNat 64 i)) = bs[i]'hi := by
    rw [byteOffset_add_ofNat_of_aligned halign hover, hwv,
        extractByte_packBytes _ _ (by omega)
          (by rw [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [hbyte] at lb
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lb)

/-- **`LD` reads the 8 bytes at index `i`**: one whole cell, so, as for `SD`,
    no `halign`/`hover`, and the cell's validity is the region's own. -/
theorem bytesRegionOn_ld_at (rd rs1 : Reg) (regionBase ptr vOld : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (hi8 : 8 ∣ i) (hlt : i + 8 ≤ bs.length)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LD rd rs1 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 i) = true →
      st.next s = some (execInstrBr s (.LD rd rs1 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LD rd rs1 offset))
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ vOld) ** bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rd ↦ᵣ packBytes ((bs.drop i).take 8)) **
        bytesRegionOn valid regionBase bs) := by
  have hi_eq : 8 * (i / 8) = i := Nat.mul_div_cancel' hi8
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) (by omega)
  rw [hi_eq] at heq
  have ld := ld_on (st := st) rd rs1 ptr vOld (packBytes ((bs.drop i).take 8)) offset base hrd
    (fun s hinv hfetch hreg hv => hst s hinv hfetch hreg (hptr ▸ hv))
  rw [hptr] at ld
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) ld)

/-! ## The same-register family, complete

`LW rd, off(rd)` and the rest: the pointer register receives the value. Two
atoms in the footprint instead of three, the same-register leaf instead of the
ordinary one, and otherwise the proof above. With `Bytes.lean`'s
`bytesRegionOn_lbu_same_at` these are the seven load forms. -/

/-- **`LW rd, off(rd)` reads the 4 bytes at index `i`**, sign-extended, into
    the register that held the pointer. -/
theorem bytesRegionOn_lw_same_at (rd : Reg) (regionBase ptr : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi4 : 4 ∣ i) (hlt : i + 4 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LW rd rd offset) → s.getReg rd = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LW rd rd offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LW rd rd offset))
      ((rd ↦ᵣ ptr) ** bytesRegionOn valid regionBase bs)
      ((rd ↦ᵣ ((packBytes ((bs.drop i).take 4)).truncate 32).signExtend 64) **
        bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lw := lw_same_on (st := st) rd ptr offset base dwordAddr wordVal hrd halign' hst
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  obtain ⟨hr4, hr8⟩ := mod_four_room hi4
  have hchunk_len : i % 8 + 4 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, extractWord32_packBytes _ _ hr4 hr8 hchunk_len, drop_take_chunk bs i 4 hr8] at lw
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lw)

/-- **`LWU rd, off(rd)` reads the 4 bytes at index `i`**, zero-extended, into
    the register that held the pointer. -/
theorem bytesRegionOn_lwu_same_at (rd : Reg) (regionBase ptr : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi4 : 4 ∣ i) (hlt : i + 4 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LWU rd rd offset) → s.getReg rd = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LWU rd rd offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LWU rd rd offset))
      ((rd ↦ᵣ ptr) ** bytesRegionOn valid regionBase bs)
      ((rd ↦ᵣ ((packBytes ((bs.drop i).take 4)).truncate 32).zeroExtend 64) **
        bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lwu := lwu_same_on (st := st) rd ptr offset base dwordAddr wordVal hrd halign' hst
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  obtain ⟨hr4, hr8⟩ := mod_four_room hi4
  have hchunk_len : i % 8 + 4 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, extractWord32_packBytes _ _ hr4 hr8 hchunk_len, drop_take_chunk bs i 4 hr8] at lwu
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lwu)

/-- **`LH rd, off(rd)` reads the 2 bytes at index `i`**, sign-extended, into
    the register that held the pointer. -/
theorem bytesRegionOn_lh_same_at (rd : Reg) (regionBase ptr : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi2 : 2 ∣ i) (hlt : i + 2 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LH rd rd offset) → s.getReg rd = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LH rd rd offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LH rd rd offset))
      ((rd ↦ᵣ ptr) ** bytesRegionOn valid regionBase bs)
      ((rd ↦ᵣ ((packBytes ((bs.drop i).take 2)).truncate 16).signExtend 64) **
        bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lh := lh_same_on (st := st) rd ptr offset base dwordAddr wordVal hrd halign' hst
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  obtain ⟨hr2, hr8⟩ := mod_two_room hi2
  have hchunk_len : i % 8 + 2 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, extractHalfword_packBytes _ _ hr2 hr8 hchunk_len, drop_take_chunk bs i 2 hr8] at lh
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lh)

/-- **`LHU rd, off(rd)` reads the 2 bytes at index `i`**, zero-extended, into
    the register that held the pointer. -/
theorem bytesRegionOn_lhu_same_at (rd : Reg) (regionBase ptr : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi2 : 2 ∣ i) (hlt : i + 2 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LHU rd rd offset) → s.getReg rd = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LHU rd rd offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LHU rd rd offset))
      ((rd ↦ᵣ ptr) ** bytesRegionOn valid regionBase bs)
      ((rd ↦ᵣ ((packBytes ((bs.drop i).take 2)).truncate 16).zeroExtend 64) **
        bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lhu := lhu_same_on (st := st) rd ptr offset base dwordAddr wordVal hrd halign' hst
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  obtain ⟨hr2, hr8⟩ := mod_two_room hi2
  have hchunk_len : i % 8 + 2 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, extractHalfword_packBytes _ _ hr2 hr8 hchunk_len, drop_take_chunk bs i 2 hr8] at lhu
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lhu)

/-- **`LB rd, off(rd)` reads byte `i` of the region**, sign-extended, into the
    register that held the pointer. -/
theorem bytesRegionOn_lb_same_at (rd : Reg) (regionBase ptr : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi : i < bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LB rd rd offset) → s.getReg rd = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.LB rd rd offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LB rd rd offset))
      ((rd ↦ᵣ ptr) ** bytesRegionOn valid regionBase bs)
      ((rd ↦ᵣ ((bs[i]'hi).signExtend 64)) ** bytesRegionOn valid regionBase bs) := by
  have hq : 8 * (i / 8) < bs.length := by omega
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) hq
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have lb := lb_same_on (st := st) rd ptr offset base dwordAddr wordVal hrd halign' hst
  rw [hptr] at lb
  have hbyte : extractByte wordVal (byteOffset (regionBase + BitVec.ofNat 64 i)) = bs[i]'hi := by
    rw [byteOffset_add_ofNat_of_aligned halign hover, hwv,
        extractByte_packBytes _ _ (by omega)
          (by rw [List.length_take, List.length_drop]; omega),
        List.getElem_take, List.getElem_drop]
    congr 1; omega
  rw [hbyte] at lb
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) lb)

/-- **`LD rd, off(rd)` reads the 8 bytes at index `i`** into the register that
    held the pointer. -/
theorem bytesRegionOn_ld_same_at (rd : Reg) (regionBase ptr : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat) (hrd : rd ≠ .x0)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (hi8 : 8 ∣ i) (hlt : i + 8 ≤ bs.length)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.LD rd rd offset) → s.getReg rd = ptr →
      valid (regionBase + BitVec.ofNat 64 i) = true →
      st.next s = some (execInstrBr s (.LD rd rd offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.LD rd rd offset))
      ((rd ↦ᵣ ptr) ** bytesRegionOn valid regionBase bs)
      ((rd ↦ᵣ packBytes ((bs.drop i).take 8)) ** bytesRegionOn valid regionBase bs) := by
  have hi_eq : 8 * (i / 8) = i := Nat.mul_div_cancel' hi8
  obtain ⟨front, rest, hf, hr, heq⟩ :=
    bytesRegionOn_dword_at (valid := valid) regionBase bs (i / 8) (by omega)
  rw [hi_eq] at heq
  have ld := ld_same_on (st := st) rd ptr (packBytes ((bs.drop i).take 8)) offset base hrd
    (fun s hinv hfetch hreg hv => hst s hinv hfetch hreg (hptr ▸ hv))
  rw [hptr] at ld
  rw [heq]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hr) ld)

end Decomp
