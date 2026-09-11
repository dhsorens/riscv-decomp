/-
  Decomp.Sp1.HintRead

  `HINT_READ` (`t0 = 0xf1`) as a triple, on SP1 with its code confined to a
  window. The one syscall `Decomp/Sp1/Syscalls.lean` left out, and the one
  whose postcondition is easy to get silently wrong.

  **The extent is `n / 8 + 1` doublewords, not `⌈n / 8⌉`.** SP1's executor
  writes a trailing zero-padded word unconditionally, so a 16-byte hint
  touches three doublewords, not two. A `⌈n/8⌉` postcondition would falsely
  preserve a frame cell at `ptr + n`. `hintBytes` is the payload padded to
  exactly that extent and the `#guard`s below pin both residues against the
  model itself.

  The postcondition is a `bytesRegionSp1 ptr (hintBytes n input)`: the shape
  a byte loop over the input reads (`Decomp/Region/`). Getting there needs
  the readback lemma upstream never stated -- `packBytes bs = bytesToWordLE
  bs`, which turns out to be `rfl` after unfolding -- and a way to see the
  model's two-phase write (`writeBytesAsWords` of the payload, then one
  `setMem` of the remainder word) as a single `writeBytesAsWords` of the
  padded payload (`hintRead_eq`). The assertion side is then one induction
  over the region's cells (`holdsFor_sepConj_bytesRegionAuxOn_writeBytesAsWords`),
  each step `holdsFor_sepConj_memIsOn_setMem`.

  The precondition mirrors the model's four checks: `isAligned8 ptr`;
  `hintWindowOk` (window inside `SP1_MAX_MEMORY`, and off the code window,
  the latter from the `Sp1Text` invariant); `a1` equals the front length;
  and enough stream. `hmax` is the one hypothesis the resource could in
  principle supply (the last cell's validity), left explicit because the
  model asks it of the window as a whole.
-/

import Decomp.Sp1.Syscalls
import Decomp.Region.Sp1

namespace Decomp

open RiscvZkvm.Rv64

variable {lo hi : Nat}

/-! ## Readback: `packBytes` is `bytesToWordLE` -/

theorem getByteAt_eq_getD (bs : List (BitVec 8)) (k : Nat) :
    getByteAt bs k = bs[k]?.getD 0 := by
  unfold getByteAt
  split
  · rename_i h; simp [List.getElem?_eq_getElem h]
  · rename_i h; simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt h)]

/-- The logic's dword-of-bytes and the machine's are the same function. -/
theorem packBytes_eq_bytesToWordLE (bs : List (BitVec 8)) :
    packBytes bs = bytesToWordLE bs := by
  simp only [packBytes, packDword, bytesToWordLE, getByteAt_eq_getD]
  rfl

theorem getD_append_replicate_zero (bs : List (BitVec 8)) (pad k : Nat) :
    (bs ++ List.replicate pad (0 : BitVec 8))[k]?.getD 0 = bs[k]?.getD 0 := by
  rw [List.getElem?_append]
  split
  · rfl
  · rw [List.getElem?_replicate]
    split <;> simp_all

/-- Zero padding does not change the packed word: `bytesToWordLE` zero-pads. -/
theorem bytesToWordLE_append_replicate_zero (bs : List (BitVec 8)) (pad : Nat) :
    bytesToWordLE (bs ++ List.replicate pad 0) = bytesToWordLE bs := by
  simp only [bytesToWordLE, getD_append_replicate_zero]

/-! ## `writeBytesAsWords`, in doubleword steps -/

theorem writeBytesAsWords_cons (s : MachineState) (base : Word) (b : BitVec 8)
    (bs : List (BitVec 8)) :
    s.writeBytesAsWords base (b :: bs)
      = (s.setMem base (bytesToWordLE ((b :: bs).take 8))).writeBytesAsWords (base + 8)
          ((b :: bs).drop 8) := by
  rw [MachineState.writeBytesAsWords]

/-- A whole number of doublewords first, then the rest from the next cell. -/
theorem writeBytesAsWords_append_of_length (s : MachineState) (base : Word)
    (xs ys : List (BitVec 8)) (m : Nat) (hxs : xs.length = 8 * m) :
    s.writeBytesAsWords base (xs ++ ys)
      = (s.writeBytesAsWords base xs).writeBytesAsWords (base + BitVec.ofNat 64 (8 * m)) ys := by
  induction m generalizing s base xs with
  | zero =>
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp
  | succ m ih =>
    cases xs with
    | nil => simp at hxs
    | cons b rest =>
      have hlen : (b :: rest).length = 8 * (m + 1) := hxs
      have h8 : 8 ≤ (b :: rest).length := by omega
      rw [List.cons_append, writeBytesAsWords_cons, writeBytesAsWords_cons (bs := rest)]
      rw [← List.cons_append, List.take_append_of_le_length h8, List.drop_append_of_le_length h8]
      rw [ih _ _ _ (by rw [List.length_drop]; omega)]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have h8' : (8 : BitVec 64).toNat = 8 := by decide
      rw [h8']
      omega

/-- At most one doubleword is a single `setMem`. -/
theorem writeBytesAsWords_single (s : MachineState) (base : Word) (rem : List (BitVec 8))
    (hne : rem ≠ []) (h8 : rem.length ≤ 8) :
    s.writeBytesAsWords base rem = s.setMem base (bytesToWordLE rem) := by
  cases rem with
  | nil => exact absurd rfl hne
  | cons b rest =>
    rw [writeBytesAsWords_cons, List.take_of_length_le h8, List.drop_of_length_le h8,
      MachineState.writeBytesAsWords_nil]

theorem setMem_setMem_same (s : MachineState) (a v : Word) :
    (s.setMem a v).setMem a v = s.setMem a v := by
  simp only [MachineState.setMem]
  congr 1
  funext a'
  split <;> simp_all

/-- **The two-phase write is one padded write.** Writing `xs ++ rem` (a whole
    number of doublewords, then a partial one) and then storing the remainder
    word again at the next cell is writing `xs ++ rem`, zero-padded to the
    cell boundary, in one go. When `rem = []` the second phase writes the
    fresh zero cell; otherwise it rewrites the partial cell with its own value. -/
theorem writeBytesAsWords_pad (s : MachineState) (ptr : Word) (xs rem : List (BitVec 8))
    (m : Nat) (hxs : xs.length = 8 * m) (hrem : rem.length < 8) :
    (s.writeBytesAsWords ptr (xs ++ rem)).setMem (ptr + BitVec.ofNat 64 (8 * m)) (bytesToWordLE rem)
      = s.writeBytesAsWords ptr (xs ++ (rem ++ List.replicate (8 - rem.length) 0)) := by
  rw [writeBytesAsWords_append_of_length _ _ xs rem m hxs,
    writeBytesAsWords_append_of_length _ _ xs _ m hxs,
    writeBytesAsWords_single _ _ (rem ++ _)
      (by simp only [ne_eq, List.append_eq_nil_iff, List.replicate_eq_nil_iff]; omega)
      (by simp only [List.length_append, List.length_replicate]; omega),
    bytesToWordLE_append_replicate_zero]
  cases rem with
  | nil => rw [MachineState.writeBytesAsWords_nil]
  | cons b rest =>
    rw [writeBytesAsWords_single _ _ (b :: rest) (List.cons_ne_nil _ _) (Nat.le_of_lt hrem),
      setMem_setMem_same]

/-! ## The padded hint -/

/-- What `HINT_READ` of the front `n`-byte hint leaves in memory: the payload,
    zero-padded to `n / 8 + 1` whole doublewords. -/
def hintBytes (n : Nat) (input : List (BitVec 8)) : List (BitVec 8) :=
  (input.drop 8).take n ++ List.replicate (8 * (n / 8 + 1) - n) 0

theorem length_hintBytes {n : Nat} {input : List (BitVec 8)} (hlen : 8 + n ≤ input.length) :
    (hintBytes n input).length = 8 * (n / 8 + 1) := by
  simp only [hintBytes, List.length_append, List.length_take, List.length_drop,
    List.length_replicate]
  omega

-- The extent, at both residues: 16 bytes take three doublewords, 13 take two.
#guard (hintBytes 16 (List.replicate 40 (1 : BitVec 8))).length == 24
#guard (hintBytes 13 (List.replicate 40 (1 : BitVec 8))).length == 16

/-- A state poised at `HINT_READ` of an `n`-byte hint of ones at `0x1000`, with
    every memory cell holding a sentinel. -/
private def probeState (n : Nat) : MachineState where
  regs := fun r =>
    if r = .x10 then 0x1000 else if r = .x11 then BitVec.ofNat 64 n
    else if r = .x5 then Sp1.HINT_READ else 0
  mem := fun _ => 0xdead
  pc := 0
  privateInput := dwordBytes (BitVec.ofNat 64 n) ++ List.replicate n 1

-- The model itself: with `n = 16` the third doubleword is written (to zero)
-- and the fourth is not. `⌈n/8⌉` would have left `0x1010` at the sentinel.
#guard ((hintRead (probeState 16)).map fun s => s.getMem 0x1010) == some 0
#guard ((hintRead (probeState 16)).map fun s => s.getMem 0x1018) == some 0xdead
#guard ((hintRead (probeState 16)).map fun s => s.getMem 0x1008) == some 0x0101010101010101
-- With `n = 13`: two doublewords, the second zero-padded past the five payload bytes.
#guard ((hintRead (probeState 13)).map fun s => s.getMem 0x1008) == some 0x0000000101010101
#guard ((hintRead (probeState 13)).map fun s => s.getMem 0x1010) == some 0xdead
-- And `hintBytes` agrees with the model, cell by cell.
#guard ((hintRead (probeState 13)).map fun s => s.getMem 0x1008)
  == some (packBytes (((hintBytes 13 (probeState 13).privateInput).drop 8).take 8))

/-! ## The region after a padded write -/

/-- Writing `8k` bytes over a `k`-cell region: cell by cell, each a
    `holdsFor_sepConj_memIsOn_setMem`, the frame carried through. -/
theorem holdsFor_sepConj_bytesRegionAuxOn_writeBytesAsWords {valid : Word → Bool}
    {base : Word} {k : Nat} {old new : List (BitVec 8)} {R : Assertion} {s : MachineState}
    (hnew : new.length = 8 * k)
    (hPR : (bytesRegionAuxOn valid base k old ** R).holdsFor s) :
    (bytesRegionAuxOn valid base k new ** R).holdsFor (s.writeBytesAsWords base new) := by
  induction k generalizing base old new s R with
  | zero =>
    have : new = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [MachineState.writeBytesAsWords_nil]
    exact hPR
  | succ k ih =>
    cases new with
    | nil => simp at hnew
    | cons b rest =>
      rw [writeBytesAsWords_cons]
      simp only [bytesRegionAuxOn] at hPR ⊢
      have h1 := holdsFor_sepConj_assoc.mp hPR
      have h2 := holdsFor_sepConj_memIsOn_setMem (v' := packBytes ((b :: rest).take 8)) h1
      rw [packBytes_eq_bytesToWordLE] at h2 ⊢
      have h3 := holdsFor_sepConj_pull_second.mp (holdsFor_sepConj_assoc.mpr h2)
      have h4 := ih (new := (b :: rest).drop 8)
        (by simp only [List.length_drop, List.length_cons] at hnew ⊢; omega) h3
      exact holdsFor_sepConj_pull_second.mpr h4

theorem holdsFor_sepConj_bytesRegionOn_writeBytesAsWords {valid : Word → Bool}
    {base : Word} {k : Nat} {old new : List (BitVec 8)} {R : Assertion} {s : MachineState}
    (hold : old.length = 8 * k) (hnew : new.length = 8 * k)
    (hPR : (bytesRegionOn valid base old ** R).holdsFor s) :
    (bytesRegionOn valid base new ** R).holdsFor (s.writeBytesAsWords base new) := by
  unfold bytesRegionOn at hPR ⊢
  rw [hnew, show (8 * k + 7) / 8 = k by omega]
  rw [hold, show (8 * k + 7) / 8 = k by omega] at hPR
  exact holdsFor_sepConj_bytesRegionAuxOn_writeBytesAsWords hnew hPR

/-! ## `privateInput` -/

/-- Replacing the stream: the frame keeps holding because it does not own the
    stream. The `privateInput` analogue of `holdsFor_sepConj_regIs_setReg`. -/
theorem holdsFor_sepConj_privateInputIs_set {v v' : List (BitVec 8)} {R : Assertion}
    {s : MachineState} (hPR : (privateInputIs v ** R).holdsFor s) :
    (privateInputIs v' ** R).holdsFor { s with privateInput := v' } := by
  obtain ⟨hp, hcompat, h1, h2, hdisj, hunion, hh1, hh2⟩ := hPR
  rw [privateInputIs] at hh1; subst hh1; rw [← hunion] at hcompat
  have hpi2 : h2.privateInput = none := by
    rcases hdisj.2.2.2.2.2.1 with h | h
    · simp [PartialState.singletonPrivateInput] at h
    · exact h
  have hdisj' : (PartialState.singletonPrivateInput v').Disjoint h2 :=
    ⟨hdisj.1, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2.1, hdisj.2.2.2.2.1, Or.inr hpi2,
      hdisj.2.2.2.2.2.2⟩
  have hc2 := (PartialState.CompatibleWith_union hdisj).mp hcompat |>.2
  have hc1' : (PartialState.singletonPrivateInput v').CompatibleWith
      { s with privateInput := v' } :=
    PartialState.CompatibleWith_singletonPrivateInput.mpr rfl
  have hc2' : h2.CompatibleWith { s with privateInput := v' } := by
    obtain ⟨hr, hm, hc, hpc, hpv, _, hib⟩ := hc2
    exact ⟨hr, hm, hc, hpc, hpv, (fun _ hv => by rw [hpi2] at hv; exact nomatch hv), hib⟩
  exact ⟨(PartialState.singletonPrivateInput v').union h2,
    (PartialState.CompatibleWith_union hdisj').mpr ⟨hc1', hc2'⟩,
    _, h2, hdisj', rfl, rfl, hh2⟩

/-! ## The step -/

theorem stepSp1_hintRead {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.HINT_READ) : stepSp1 s = hintRead s := by
  have h1 : Sp1.HINT_READ ≠ Sp1.HINT_LEN := by decide
  unfold stepSp1; rw [hfetch]
  simp only [sp1Ecall, ht0, Sp1.isAccelId_hint_false.2]
  simp [h1]

/-- **What `hintRead` does**, when its four checks pass: one padded write of
    the front hint at `a0`, the stream advanced past it, `pc + 4`. -/
theorem hintRead_eq {s : MachineState} (input : List (BitVec 8)) (n : Nat) (ptr : Word)
    (hpi : s.privateInput = input)
    (hn : (bytesToWordLE (input.take 8)).toNat = n) (hlen : 8 + n ≤ input.length)
    (hptr : s.getReg .x10 = ptr) (hx11 : s.getReg .x11 = BitVec.ofNat 64 n)
    (halign : isAligned8 ptr = true) (hwin : hintWindowOk s ptr n = true) :
    hintRead s = some (({ s.writeBytesAsWords ptr (hintBytes n input) with
      privateInput := input.drop (8 + n) } : MachineState).setPC (s.pc + 4)) := by
  have hfront : frontHintLen s = some n := by
    simp [frontHintLen, hpi, Nat.not_lt.mpr (show 8 ≤ input.length by omega), hn]
  have hn64 : n < 2 ^ 64 := hn ▸ (bytesToWordLE (input.take 8)).isLt
  have hlen' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn64
  have hstream : ¬ input.length < 8 + n := by omega
  simp only [hintRead, hfront, hptr, hx11, halign, hwin, hlen', hpi, hstream, Bool.not_true,
    Bool.false_eq_true, if_false, ne_eq, not_true_eq_false]
  -- The payload split at its last whole doubleword.
  have hP := List.take_append_drop (8 * (n / 8)) ((input.drop 8).take n)
  have hkey := writeBytesAsWords_pad s ptr (((input.drop 8).take n).take (8 * (n / 8)))
    (((input.drop 8).take n).drop (8 * (n / 8))) (n / 8)
    (by simp only [List.length_take, List.length_drop]; omega)
    (by simp only [List.length_drop, List.length_take]; omega)
  rw [hP] at hkey
  have hhb : hintBytes n input
      = ((input.drop 8).take n).take (8 * (n / 8)) ++
        ((((input.drop 8).take n).drop (8 * (n / 8))) ++
          List.replicate (8 - (((input.drop 8).take n).drop (8 * (n / 8))).length) 0) := by
    unfold hintBytes
    rw [← List.append_assoc, hP]
    congr 2
    simp only [List.length_drop, List.length_take]
    omega
  rw [hhb, ← hkey]
  simp [MachineState.setPC]

/-! ## The triple -/

private theorem holdsFor_of_imp {P Q : Assertion} {s : MachineState}
    (hpq : ∀ h, P h → Q h) (hP : P.holdsFor s) : Q.holdsFor s :=
  let ⟨h, hc, hp⟩ := hP; ⟨h, hc, hpq h hp⟩

/-- **`HINT_READ`.** With `a0` doubleword-aligned at a region of `n / 8 + 1`
    doublewords off the code window and inside SP1's memory, `a1` the front
    hint's length `n`, and the stream holding that hint: the region becomes the
    hint zero-padded to the cell boundary (`hintBytes`), the stream loses its
    framing word and payload, and the registers are untouched. -/
theorem hintRead_sp1Text (input : List (BitVec 8)) (n : Nat) (ptr : Word)
    (old : List (BitVec 8)) (base : Word)
    (hn : (bytesToWordLE (input.take 8)).toNat = n) (hlen : 8 + n ≤ input.length)
    (halign : isAligned8 ptr = true) (hold : old.length = 8 * (n / 8 + 1))
    (hmax : ptr.toNat + 8 * (n / 8 + 1) ≤ SP1_MAX_MEMORY)
    (hoff : OffText lo hi ptr (8 * (n / 8 + 1))) :
    cpsWithin (Sp1Text lo hi) 1 base (base + 4) (CodeReq.singleton base .ECALL)
      ((.x5 ↦ᵣ Sp1.HINT_READ) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ BitVec.ofNat 64 n) **
        privateInputIs input ** bytesRegionSp1 ptr old)
      ((.x5 ↦ᵣ Sp1.HINT_READ) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ BitVec.ofNat 64 n) **
        privateInputIs (input.drop (8 + n)) ** bytesRegionSp1 ptr (hintBytes n input)) := by
  intro R hR s hinv hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some .ECALL := CodeReq.singleton_satisfiedBy.mp hcr
  have hP := holdsFor_sepConj_elim_left hPR
  have ht0 : s.getReg .x5 = Sp1.HINT_READ := holdsFor_regIs.mp (holdsFor_sepConj_elim_left hP)
  have hP2 := holdsFor_sepConj_elim_right hP
  have hx10 : s.getReg .x10 = ptr := holdsFor_regIs.mp (holdsFor_sepConj_elim_left hP2)
  have hP3 := holdsFor_sepConj_elim_right hP2
  have hx11 : s.getReg .x11 = BitVec.ofNat 64 n :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hP3)
  have hpi : s.privateInput = input :=
    holdsFor_privateInputIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hP3))
  have hwin : hintWindowOk s ptr n = true := by
    unfold hintWindowOk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hmax, noCodeAt_of_codeWithin (by omega) hinv hoff⟩
  have hstep := hintRead_eq input n ptr hpi hn hlen hx10 hx11 halign hwin
  refine ⟨1, Nat.le_refl 1, ({ s.writeBytesAsWords ptr (hintBytes n input) with
    privateInput := input.drop (8 + n) } : MachineState).setPC (s.pc + 4), ?_, ?_, ?_⟩
  · show ((Sp1Text lo hi).next s).bind ((Sp1Text lo hi).iter 0) = _
    rw [Sp1Text_next, stepSp1_hintRead hfetch ht0, hstep]
    rfl
  · simp [MachineState.setPC]
  · -- Memory first, then the stream, then the pc.
    have h1 : (bytesRegionSp1 ptr old **
        (((.x5 ↦ᵣ Sp1.HINT_READ) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ BitVec.ofNat 64 n) **
          privateInputIs input) ** R)).holdsFor s :=
      holdsFor_of_imp (fun _ hp => by xperm_hyp hp) hPR
    have h2 := holdsFor_sepConj_bytesRegionOn_writeBytesAsWords hold (length_hintBytes hlen) h1
    have h3 : (privateInputIs input **
        (((.x5 ↦ᵣ Sp1.HINT_READ) ** (.x10 ↦ᵣ ptr) ** (.x11 ↦ᵣ BitVec.ofNat 64 n) **
          bytesRegionSp1 ptr (hintBytes n input)) ** R)).holdsFor
        (s.writeBytesAsWords ptr (hintBytes n input)) :=
      holdsFor_of_imp (fun _ hp => by xperm_hyp hp) h2
    have h4 := holdsFor_sepConj_privateInputIs_set (v' := input.drop (8 + n)) h3
    refine holdsFor_pcFree_setPC ?_ (holdsFor_of_imp (fun _ hp => by xperm_hyp hp) h4)
    exact pcFree_sepConj
      (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs
        (pcFree_sepConj pcFree_privateInputIs (bytesRegionOn_pcFree _ _ _))))) hR

end Decomp
