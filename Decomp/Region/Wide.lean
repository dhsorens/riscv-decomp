/-
  Decomp.Region.Wide

  Wide stores into a byte region, and ownership with forgotten contents.

  `Decomp/Region/Bytes.lean` has the byte keystones. This file adds the three
  wide stores compiled code emits into a buffer -- `SW` at a 4-aligned index
  (upstream's `bytesRegion_sw_at_within`), and `SH` at a 2-aligned index and
  `SD` at an 8-aligned index, which upstream never stated though it proved the
  algebra for both (`packBytes_setBytes_halfword`, `packBytes_setBytes_dword`)
  -- plus `anyBytesOn`, the havoc weakening that lets a buffer's ownership
  cross a phase boundary with its contents forgotten.

  As in `Bytes.lean`: the framing lemma is restated over `bytesRegionOn valid`,
  the leaf comes from `Decomp/Leaf/Mem.lean`, the splice algebra
  (`setBytes`, `packBytes_setBytes_word32`, `packBytes_setBytes_dword`) is
  imported unchanged, and the proofs are upstream's proofs.

  `SD` at an aligned index is the one to notice: it is the store RV64 code
  emits for every spill and every whole-doubleword copy, and a
  `memset`/`memcpy` body writes whole doublewords into exactly this resource. The cell is replaced outright, so unlike `SW`
  there is no read-modify-write and the payload is just `dwordBytes v`.
-/

module

public import Decomp.Region.Bytes

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64

variable {valid : Word → Bool}

private theorem sepConj_assoc_eq {P Q R : Assertion} :
    ((P ** Q) ** R) = (P ** (Q ** R)) := by
  funext h; exact propext (sepConj_assoc h)

/-! ## Framing one dword for a spliced payload -/

/-- Frame the `q`-th dword for both `bs` and `setBytes bs (8q+r) ns`, with shared
    `front`/`rest`. Upstream's `bytesRegion_dword_at_setBytes`, over any cell. -/
theorem bytesRegionOn_dword_at_setBytes (regionBase : Word)
    (bs ns : List (BitVec 8)) (q r : Nat)
    (hns : ns ≠ []) (hr : r + ns.length ≤ 8)
    (hi : 8 * q + r + ns.length ≤ bs.length) :
    ∃ front rest : Assertion, front.pcFree ∧ rest.pcFree ∧
      bytesRegionOn valid regionBase bs
        = (front ** (memIsOn valid (regionBase + BitVec.ofNat 64 (8 * q))
            (packBytes ((bs.drop (8 * q)).take 8)) ** rest))
      ∧ bytesRegionOn valid regionBase (setBytes bs (8 * q + r) ns)
        = (front ** (memIsOn valid (regionBase + BitVec.ofNat 64 (8 * q))
            (packBytes (setBytes ((bs.drop (8 * q)).take 8) r ns)) ** rest)) := by
  have hnslen : 0 < ns.length := List.length_pos_iff.mpr hns
  induction q generalizing regionBase bs with
  | zero =>
    have hne : bs ≠ [] := by
      intro h; subst h; simp only [List.length_nil] at hi; omega
    refine ⟨empAssertion, bytesRegionOn valid (regionBase + 8) (bs.drop 8), pcFree_emp,
      bytesRegionOn_pcFree _ _ _, ?_, ?_⟩
    · rw [bytesRegionOn_eq_cons valid regionBase bs hne,
        show regionBase + BitVec.ofNat 64 (8 * 0) = regionBase from by bv_omega]
      simp only [Nat.mul_zero, List.drop_zero, sepConj_emp_left']
    · have hset_ne : setBytes bs (8 * 0 + r) ns ≠ [] :=
        List.ne_nil_of_length_pos
          (by rw [length_setBytes]; exact List.length_pos_iff.mpr hne)
      rw [bytesRegionOn_eq_cons valid regionBase (setBytes bs (8 * 0 + r) ns) hset_ne]
      rw [setBytes_take_of_le ns bs (8 * 0 + r) 8 (by omega),
        setBytes_drop_of_le ns bs (8 * 0 + r) 8 (by omega),
        show regionBase + BitVec.ofNat 64 (8 * 0) = regionBase from by bv_omega]
      simp only [Nat.mul_zero, Nat.zero_add, List.drop_zero, sepConj_emp_left']
  | succ k ih =>
    have hne : bs ≠ [] := by
      intro h; subst h; simp only [List.length_nil] at hi; omega
    have hi' : 8 * k + r + ns.length ≤ (bs.drop 8).length := by
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
    have htake_first : (setBytes bs (8 * (k + 1) + r) ns).take 8 = bs.take 8 :=
      setBytes_take_of_ge ns bs _ 8 (by omega)
    have hdrop_first : (setBytes bs (8 * (k + 1) + r) ns).drop 8
        = setBytes (bs.drop 8) (8 * k + r) ns := by
      rw [setBytes_drop_of_ge ns bs _ 8 (by omega)]
      congr 1
      omega
    refine ⟨memIsOn valid regionBase (packBytes (bs.take 8)) ** front', rest',
      pcFree_sepConj pcFree_memIsOn hf', hr', ?_, ?_⟩
    · rw [bytesRegionOn_eq_cons valid regionBase bs hne, heq', haddr, hdrop, ← sepConj_assoc_eq]
    · have hset_ne : setBytes bs (8 * (k + 1) + r) ns ≠ [] :=
        List.ne_nil_of_length_pos
          (by rw [length_setBytes]; exact List.length_pos_iff.mpr hne)
      rw [bytesRegionOn_eq_cons valid regionBase (setBytes bs (8 * (k + 1) + r) ns) hset_ne,
        htake_first, hdrop_first, heqset', haddr, hdrop, ← sepConj_assoc_eq]

/-! ## The wide stores, over any stepper

The address is `ptr + signExtend12 offset` with a caller-supplied `hptr`, as
upstream does for `SW`: the callers that need these write several words off one
base register with different immediates. -/

variable {st : Stepper}

/-- **`SW` writes the 4 bytes at index `i`.** `i` is 4-aligned and the base is
    dword-aligned, so the payload never straddles two cells. -/
theorem bytesRegionOn_sw_at (rs1 rs2 : Reg) (regionBase ptr v_data : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi4 : 4 ∣ i)
    (hlt : i + 4 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SW rs1 rs2 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.SW rs1 rs2 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SW rs1 rs2 offset))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
        bytesRegionOn valid regionBase (setBytes bs i (word32Bytes (v_data.truncate 32)))) := by
  have hi_eq : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  have hr4 : 4 ∣ i % 8 := Nat.dvd_mod_iff (by decide) |>.mpr hi4
  have hr8 : i % 8 + 4 ≤ 8 := by
    obtain ⟨m, hm⟩ := hr4
    have : i % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegionOn_dword_at_setBytes (valid := valid) regionBase bs
      (word32Bytes (v_data.truncate 32)) (i / 8) (i % 8) (by simp [word32Bytes])
      (by rw [length_word32Bytes]; exact hr8) (by rw [length_word32Bytes, hi_eq]; exact hlt)
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have sw := sw_on (st := st) rs1 rs2 ptr v_data offset base dwordAddr wordVal halign' hst
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  have hchunk_len : i % 8 + 4 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, packBytes_setBytes_word32 _ (i % 8) (v_data.truncate 32)
    hr4 hr8 hchunk_len] at sw
  rw [heq, show setBytes bs i (word32Bytes (v_data.truncate 32))
      = setBytes bs (8 * (i / 8) + i % 8) (word32Bytes (v_data.truncate 32))
      from by rw [hi_eq], heqset]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hrst) sw)

/-- **`SH` writes the 2 bytes at index `i`.** `i` is 2-aligned and the base is
    dword-aligned, so the payload never straddles two cells. Upstream proved the
    algebra (`packBytes_setBytes_halfword`) but never stated the region store;
    the emitted `main` has one `sh`. -/
theorem bytesRegionOn_sh_at (rs1 rs2 : Reg) (regionBase ptr v_data : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (halign : regionBase.toNat % 8 = 0) (hi2 : 2 ∣ i)
    (hlt : i + 2 ≤ bs.length)
    (hover : regionBase.toNat + i < 2 ^ 64)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SH rs1 rs2 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 (8 * (i / 8))) = true →
      st.next s = some (execInstrBr s (.SH rs1 rs2 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SH rs1 rs2 offset))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
        bytesRegionOn valid regionBase (setBytes bs i (halfwordBytes (v_data.truncate 16)))) := by
  have hi_eq : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  have hr2 : 2 ∣ i % 8 := Nat.dvd_mod_iff (by decide) |>.mpr hi2
  have hr8 : i % 8 + 2 ≤ 8 := by
    obtain ⟨m, hm⟩ := hr2
    have : i % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegionOn_dword_at_setBytes (valid := valid) regionBase bs
      (halfwordBytes (v_data.truncate 16)) (i / 8) (i % 8) (by simp [halfwordBytes])
      (by rw [length_halfwordBytes]; exact hr8) (by rw [length_halfwordBytes, hi_eq]; exact hlt)
  set dwordAddr := regionBase + BitVec.ofNat 64 (8 * (i / 8)) with hdwa
  set wordVal := packBytes ((bs.drop (8 * (i / 8))).take 8) with hwv
  have halign' : alignToDword (ptr + signExtend12 offset) = dwordAddr := by
    rw [hptr]; exact alignToDword_add_ofNat_of_aligned halign hover
  have sh := sh_on (st := st) rs1 rs2 ptr v_data offset base dwordAddr wordVal halign' hst
  have hbo : byteOffset (ptr + signExtend12 offset) = i % 8 := by
    rw [hptr]; exact byteOffset_add_ofNat_of_aligned halign hover
  have hchunk_len : i % 8 + 2 ≤ ((bs.drop (8 * (i / 8))).take 8).length := by
    rw [List.length_take, List.length_drop]; omega
  rw [hbo, hwv, packBytes_setBytes_halfword _ (i % 8) (v_data.truncate 16)
    hr2 hr8 hchunk_len] at sh
  rw [heq, show setBytes bs i (halfwordBytes (v_data.truncate 16))
      = setBytes bs (8 * (i / 8) + i % 8) (halfwordBytes (v_data.truncate 16))
      from by rw [hi_eq], heqset]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hrst) sh)

/-- **`SD` writes the 8 bytes at index `i`.** `i` is 8-aligned, so the store
    replaces one whole cell: no read-modify-write, and the payload is
    `dwordBytes v_data`. Not stated upstream, though `packBytes_setBytes_dword`
    was proved for it.

    Unlike `SW`, no `halign`/`hover`: the region's cells sit at `regionBase +
    8k` whatever `regionBase` is, and the store hits one of them exactly. The
    cell's validity is read out of the resource, as in `sd_on`. -/
theorem bytesRegionOn_sd_at (rs1 rs2 : Reg) (regionBase ptr v_data : Word)
    (offset : BitVec 12) (base : Word) (bs : List (BitVec 8)) (i : Nat)
    (hptr : ptr + signExtend12 offset = regionBase + BitVec.ofNat 64 i)
    (hi8 : 8 ∣ i) (hlt : i + 8 ≤ bs.length)
    (hst : ∀ s, st.inv s → s.code s.pc = some (.SD rs1 rs2 offset) → s.getReg rs1 = ptr →
      valid (regionBase + BitVec.ofNat 64 i) = true →
      st.next s = some (execInstrBr s (.SD rs1 rs2 offset))) :
    cpsWithin st 1 base (base + 4) (CodeReq.singleton base (.SD rs1 rs2 offset))
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) ** bytesRegionOn valid regionBase bs)
      ((rs1 ↦ᵣ ptr) ** (rs2 ↦ᵣ v_data) **
        bytesRegionOn valid regionBase (setBytes bs i (dwordBytes v_data))) := by
  have hi_eq : 8 * (i / 8) = i := Nat.mul_div_cancel' hi8
  obtain ⟨front, rest, hf, hrst, heq, heqset⟩ :=
    bytesRegionOn_dword_at_setBytes (valid := valid) regionBase bs (dwordBytes v_data)
      (i / 8) 0 (by simp [dwordBytes]) (by simp) (by simp only [length_dwordBytes]; omega)
  rw [hi_eq] at heq heqset
  rw [Nat.add_zero] at heqset
  set wordVal := packBytes ((bs.drop i).take 8) with hwv
  -- `sd_on` states its cell at `ptr + signExtend12 offset`; move it to the region's address.
  have sd := sd_on (st := st) rs1 rs2 ptr v_data wordVal offset base
    (fun s hinv hfetch hreg hv => hst s hinv hfetch hreg (hptr ▸ hv))
  rw [hptr] at sd
  have hpack : v_data = packBytes (setBytes ((bs.drop i).take 8) 0 (dwordBytes v_data)) :=
    packBytes_setBytes_dword _ _ (by rw [List.length_take, List.length_drop]; omega)
  rw [heq, heqset, ← hpack]
  exact cpsWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    (cpsWithin_frameR (front ** rest) (pcFree_sepConj hf hrst) sd)

/-! ## Store, then load

`Region/WideLoad.lean` gives the loads and this file gives the stores. They
were written at different times against the same cells — the stores in
`zip-2005-asm` before the extraction, the loads here on 2026-09-14 — and
from opposite directions of the `packBytes` algebra: the stores splice into a
cell, the loads extract out of one. The lemma below is the check that they
agree about what a cell holds.

It is needed by no proof in either file, and that is why it is here rather than
in a proof: a store whose payload and a load whose result disagreed would
typecheck separately and fail only when someone sequenced them, which is the
two-lemma form of this library's characteristic failure. -/

/-- **The round trip**: what `bytesRegionOn_sd_at` writes at index `i` is what
    `bytesRegionOn_ld_at` reads back there.

    Note what it does *not* need: alignment. `8 ∣ i` is what makes each
    keystone address a single cell; that the eight bytes read at `i` are the
    eight written at `i` is a list fact, true at any index. Stating it with the
    alignment hypothesis would have hidden which half of each keystone's side
    condition is doing which job. -/
theorem packBytes_readback_setBytes_dword (bs : List (BitVec 8)) (v : Word) (i : Nat)
    (hlt : i + 8 ≤ bs.length) :
    packBytes (((setBytes bs i (dwordBytes v)).drop i).take 8) = v := by
  rw [setBytes_drop_of_ge (dwordBytes v) bs i i (Nat.le_refl i), Nat.sub_self,
    setBytes_take_of_le (dwordBytes v) (bs.drop i) 0 8 (by simp),
    ← packBytes_setBytes_dword _ v (by rw [List.length_take, List.length_drop]; omega)]

/-! ## Ownership with forgotten contents -/

/-- Ownership of the `n` bytes at `base` with unspecified contents. Upstream's
    `anyBytes`, over any cell. -/
def anyBytesOn (valid : Word → Bool) (base : Word) (n : Nat) : Assertion :=
  fun h => ∃ bs : List (BitVec 8), bs.length = n ∧ bytesRegionOn valid base bs h

theorem pcFree_anyBytesOn (base : Word) (n : Nat) : (anyBytesOn valid base n).pcFree := by
  rintro h ⟨bs, _, hb⟩
  exact bytesRegionOn_pcFree valid base bs h hb

/-- **The havoc weakening**: concrete contents are forgotten. The only way a
    buffer's ownership crosses a phase boundary. -/
theorem bytesRegionOn_anyBytes (base : Word) (bs : List (BitVec 8))
    (h : PartialState) (hb : bytesRegionOn valid base bs h) :
    anyBytesOn valid base bs.length h :=
  ⟨bs, rfl, hb⟩

end Decomp
