/-
  Decomp.Examples.FindIndexMachine

  The machine-level half of `FindIndex`: the first proof in which **two
  distinct `inr` branches of one `RecB.body` are discharged** against
  instructions. This is `ROADMAP.md` item 1's acceptance criterion, and the
  first consumer of the half of `cpsTotal_loopB` that a single-exit loop
  cannot reach.

      base+0:   BEQ  x10, x11, +16     -- i == stop  → base+16       exit A
      base+4:   ADDI x10, x10, 1
      base+8:   BNE  x10, x12, -8      -- i != end   → base
      base+12:  JAL  x0,  +4           --            → base+16       exit B
      base+16:  (join)

  Exit A is one instruction from the region's entry and leaves the counter
  where it was. Exit B is four, includes the increment, and reaches the join
  through the `JAL` a compiler emits between a bottom exit and the label the
  top exit already targets. `hExit` below is one obligation, `∀ x y, body x =
  .inr y → …`, and its proof case-splits on which `inr` produced `y`; the two
  cases are two different machine paths with two different lengths, which is
  what `cpsWithin_mono` is for.

  Everything is parametrised by a `PlainAgree` stepper, so `find_found` and
  `find_exhausted` at the bottom hold on ZisK and SP1 from one proof.

  ## What this exercises, and what it does not

  It exercises: two `inr` branches with different code behind them; an exit
  from the top of the body *and* from the bottom; a bottom-guarded continue
  with no do-while rotation; the convergence of two machine exits on one label
  through an intervening `JAL`; `side` demanded at the exit state (the strict
  bound in `runsTo_found`).

  It does not exercise: memory. The body touches three registers and nothing
  else, so there is no region coupling and no `x & 7 = 0 ↔ index % 8 = 0`
  alignment bridge; a compiled alignment loop over a region would owe both.
  And it is hand-written, like `Countdown` -- no compiler emitted
  it, so it says nothing about what LLVM does with a `break`.
-/

module

public import Decomp.Certificate
public import Decomp.Leaf.Sp1Step
public import Decomp.Examples.FindIndex
public import Decomp.Upstream

@[expose] public section

namespace Decomp.Examples.FindIndex

open RiscvZkvm.Rv64

variable {st : Stepper}

/-- The four instructions, at an arbitrary base. -/
def prog : Program := [
  .BEQ .x10 .x11 (16 : BitVec 13),
  .ADDI .x10 .x10 (1 : BitVec 12),
  .BNE .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8)),
  .JAL .x0 (BitVec.ofNat 21 4)
]

def cr (base : Word) : CodeReq := CodeReq.ofProg base prog

/-- The coupling: the index in `x10`, the two range parameters in `x11` and
    `x12`. Grouped so the `BEQ`'s footprint (`x10`, `x11`) is the left
    sub-term; the `BNE` wants (`x10`, `x12`) and gets it by one `ac_rfl`. An
    `abbrev`, so the permutation can see through it. -/
abbrev I (stop e i : Nat) : Assertion :=
  ((.x10 ↦ᵣ BitVec.ofNat 64 i) ** (.x11 ↦ᵣ BitVec.ofNat 64 stop)) **
    (.x12 ↦ᵣ BitVec.ofNat 64 e)

/-- What the join sees, by exit. Exit A leaves the index where the search hit;
    exit B leaves it at the end of the range. -/
def Q (stop e : Nat) : Res → Assertion
  | .found j => I stop e j
  | .exhausted => I stop e e

/-! ## Address arithmetic, evaluated once -/

theorem sext13_sixteen : signExtend13 (16 : BitVec 13) = (16 : Word) := by decide
theorem sext12_one : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
theorem sext13_neg8 : signExtend13 (BitVec.ofNat 13 (2 ^ 13 - 8)) = (-8 : Word) := by decide
theorem sext21_four : signExtend21 (BitVec.ofNat 21 4) = (4 : Word) := by decide

theorem add_4_4 (base : Word) : base + 4 + 4 = base + 8 := by bv_omega
theorem add_8_4 (base : Word) : base + 8 + 4 = base + 12 := by bv_omega
theorem add_12_4 (base : Word) : base + 12 + 4 = base + 16 := by bv_omega
theorem bne_target (base : Word) : base + 8 + (-8 : Word) = base := by bv_omega

theorem setReg_x0 (s : MachineState) (v : Word) : s.setReg .x0 v = s := rfl

/-- The abstract increment is the machine's, with no side condition at all:
    `ofNat` is a ring homomorphism. The side condition is needed one step
    later, when the incremented value is *compared*. -/
theorem ofNat_succ (i : Nat) : BitVec.ofNat 64 i + (1 : Word) = BitVec.ofNat 64 (i + 1) := by
  bv_omega

/-- Two representable naturals are equal iff their `ofNat`s are. This is the
    only place the bounds do any work. -/
theorem ofNat_inj_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  · intro h; rw [h]

/-! ## Code residency -/

theorem beq_sub (base : Word) :
    ∀ a i, CodeReq.singleton base (.BEQ .x10 .x11 (16 : BitVec 13)) a = some i →
      cr base a = some i :=
  CodeReq.singleton_mono (CodeReq.ofProg_lookup_zero base _ _)

theorem addi_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 4) (.ADDI .x10 .x10 (1 : BitVec 12)) a = some i →
      cr base a = some i :=
  CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base prog 1 (base + 4) (by decide) (by decide) (by bv_omega))

theorem bne_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 8) (.BNE .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8))) a
        = some i → cr base a = some i :=
  CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base prog 2 (base + 8) (by decide) (by decide) (by bv_omega))

theorem jal_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 12) (.JAL .x0 (BitVec.ofNat 21 4)) a = some i →
      cr base a = some i :=
  CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base prog 3 (base + 12) (by decide) (by decide) (by bv_omega))

/-! ## The leaves, framed to the coupling

One lemma per instruction, each over an *arbitrary* index so the two exit
paths and the continue path share them. The branch leaves are stated as the
one-instruction triple along the arm the abstract state selects, with the
other arm refuted from the pure guard it carries. -/

section Leaves

variable {stop e : Nat}

/-- `BEQ x10, x11, +16`, taken: `i = stop`, so control leaves for the join. -/
theorem beq_taken (hst : st.PlainAgree) (base : Word) (hstop : stop < 2 ^ 64)
    {i : Nat} (hi : i < 2 ^ 64) (hs : i = stop) :
    cpsWithin st 1 base (base + 16) (cr base) (I stop e i) (I stop e i) := by
  have hbr := cpsBranch_of_zisk_plain hst (CodeReq.singleton_self _ _) rfl (by nofun) (by nofun)
    (generic_beq_spec_within .x10 .x11 (16 : BitVec 13)
      (BitVec.ofNat 64 i) (BitVec.ofNat 64 stop) base)
  rw [sext13_sixteen] at hbr
  refine cpsWithin_extend_code (beq_sub base) ?_
  refine cpsWithin_frameR _ (by pcFree) ?_
  refine cpsWithin_weaken (fun _ hp => hp) ?_ (cpsBranch_takenPath (fun hp hq => ?_) hbr)
  · intro h hq
    exact sepConj_mono_right (fun h' hbc => ((sepConj_pure_right h').mp hbc).1) h hq
  · obtain ⟨_, h2, _, _, _, hbc⟩ := hq
    exact ((sepConj_pure_right h2).mp hbc).2 ((ofNat_inj_iff hi hstop).mpr hs)

/-- `BEQ x10, x11, +16`, not taken: `i ≠ stop`, so control falls into the body. -/
theorem beq_notTaken (hst : st.PlainAgree) (base : Word) (hstop : stop < 2 ^ 64)
    {i : Nat} (hi : i < 2 ^ 64) (hs : i ≠ stop) :
    cpsWithin st 1 base (base + 4) (cr base) (I stop e i) (I stop e i) := by
  have hbr := cpsBranch_of_zisk_plain hst (CodeReq.singleton_self _ _) rfl (by nofun) (by nofun)
    (generic_beq_spec_within .x10 .x11 (16 : BitVec 13)
      (BitVec.ofNat 64 i) (BitVec.ofNat 64 stop) base)
  refine cpsWithin_extend_code (beq_sub base) ?_
  refine cpsWithin_frameR _ (by pcFree) ?_
  refine cpsWithin_weaken (fun _ hp => hp) ?_ (cpsBranch_notTakenPath (fun hp hq => ?_) hbr)
  · intro h hq
    exact sepConj_mono_right (fun h' hbc => ((sepConj_pure_right h').mp hbc).1) h hq
  · obtain ⟨_, h2, _, _, _, hbc⟩ := hq
    exact hs ((ofNat_inj_iff hi hstop).mp ((sepConj_pure_right h2).mp hbc).2)

/-- `ADDI x10, x10, 1`: the index steps, unconditionally. -/
theorem addi_step (hst : st.PlainAgree) (base : Word) (i : Nat) :
    cpsWithin st 1 (base + 4) (base + 8) (cr base) (I stop e i) (I stop e (i + 1)) := by
  have h := cpsWithin_of_zisk_plain hst (CodeReq.singleton_self _ _) rfl (by nofun) (by nofun)
    (addi_spec_same_within .x10 (BitVec.ofNat 64 i) (1 : BitVec 12) (base + 4) (by decide))
  rw [sext12_one, ofNat_succ, add_4_4] at h
  exact cpsWithin_extend_code (addi_sub base)
    (cpsWithin_frameR _ (by pcFree) (cpsWithin_frameR _ (by pcFree) h))

/-- The `BNE`'s footprint is (`x10`, `x12`), which is not a sub-term of `I`.
    One permutation, stated once. -/
theorem I_perm (stop e i : Nat) :
    I stop e i = (((.x10 ↦ᵣ BitVec.ofNat 64 i) ** (.x12 ↦ᵣ BitVec.ofNat 64 e)) **
      (.x11 ↦ᵣ BitVec.ofNat 64 stop)) := by
  simp only [I]; ac_rfl

/-- `BNE x10, x12, -8`, taken: the index has not reached `e`, so back to the top. -/
theorem bne_taken (hst : st.PlainAgree) (base : Word) (he : e < 2 ^ 64)
    {j : Nat} (hj : j < 2 ^ 64) (hne : j ≠ e) :
    cpsWithin st 1 (base + 8) base (cr base) (I stop e j) (I stop e j) := by
  have hbr := cpsBranch_of_zisk_plain hst (CodeReq.singleton_self _ _) rfl (by nofun) (by nofun)
    (generic_bne_spec_within .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8))
      (BitVec.ofNat 64 j) (BitVec.ofNat 64 e) (base + 8))
  rw [sext13_neg8, bne_target] at hbr
  rw [I_perm]
  refine cpsWithin_extend_code (bne_sub base) ?_
  refine cpsWithin_frameR _ (by pcFree) ?_
  refine cpsWithin_weaken (fun _ hp => hp) ?_ (cpsBranch_takenPath (fun hp hq => ?_) hbr)
  · intro h hq
    exact sepConj_mono_right (fun h' hbc => ((sepConj_pure_right h').mp hbc).1) h hq
  · obtain ⟨_, h2, _, _, _, hbc⟩ := hq
    exact hne ((ofNat_inj_iff hj he).mp ((sepConj_pure_right h2).mp hbc).2)

/-- `BNE x10, x12, -8`, not taken: the index is `e`, so on to the `JAL`. -/
theorem bne_notTaken (hst : st.PlainAgree) (base : Word) (he : e < 2 ^ 64)
    {j : Nat} (hj : j < 2 ^ 64) (heq : j = e) :
    cpsWithin st 1 (base + 8) (base + 12) (cr base) (I stop e j) (I stop e j) := by
  have hbr := cpsBranch_of_zisk_plain hst (CodeReq.singleton_self _ _) rfl (by nofun) (by nofun)
    (generic_bne_spec_within .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8))
      (BitVec.ofNat 64 j) (BitVec.ofNat 64 e) (base + 8))
  rw [add_8_4] at hbr
  rw [I_perm]
  refine cpsWithin_extend_code (bne_sub base) ?_
  refine cpsWithin_frameR _ (by pcFree) ?_
  refine cpsWithin_weaken (fun _ hp => hp) ?_ (cpsBranch_notTakenPath (fun hp hq => ?_) hbr)
  · intro h hq
    exact sepConj_mono_right (fun h' hbc => ((sepConj_pure_right h').mp hbc).1) h hq
  · obtain ⟨_, h2, _, _, _, hbc⟩ := hq
    exact ((sepConj_pure_right h2).mp hbc).2 ((ofNat_inj_iff hj he).mpr heq)

/-- `JAL x0, +4`: the join, and nothing else. -/
theorem jal_join (hst : st.PlainAgree) (base : Word) (i : Nat) :
    cpsWithin st 1 (base + 12) (base + 16) (cr base) (I stop e i) (I stop e i) := by
  have hpc : ∀ s : MachineState, s.pc = base + 12 →
      execInstrBr s (.JAL .x0 (BitVec.ofNat 21 4)) = s.setPC (base + 16) := by
    intro s hpc
    simp only [execInstrBr, setReg_x0, hpc, sext21_four, add_12_4]
  have h := cpsWithin_of_zisk_plain hst (CodeReq.singleton_self _ _) rfl (by nofun) (by nofun)
    (generic_nop_spec_within (.JAL .x0 (BitVec.ofNat 21 4))
      (base := base + 12) (exit_ := base + 16) hpc
      (fun s hf => step_non_ecall_non_mem hf (by nofun) (by nofun) rfl))
  refine cpsWithin_extend_code (jal_sub base) ?_
  refine cpsWithin_weaken ?_ ?_ (cpsWithin_frameL (I stop e i) (by pcFree) h)
  · intro h hp; rw [sepConj_emp_right']; exact hp
  · intro h hq; rwa [sepConj_emp_right'] at hq

end Leaves

/-! ## The two obligations of `cpsTotal_loopB` -/

section Obligations

variable {stop e : Nat}

/-- The continue pass: `BEQ` falls through, `ADDI`, `BNE` back to the top. -/
theorem cont (hst : st.PlainAgree) (base : Word) (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    ∀ i i', (find stop e).body i = .inl i' → side i →
      cpsWithin st 3 base base (cr base) (I stop e i) (I stop e i') := by
  intro i i' hb hs
  have hs' : i + 1 < 2 ^ 64 := hs
  by_cases h1 : i = stop
  · rw [body_found h1] at hb; exact absurd hb (by simp)
  by_cases h2 : i + 1 = e
  · rw [body_exhausted h1 h2] at hb; exact absurd hb (by simp)
  rw [body_cont h1 h2] at hb
  cases Sum.inl.inj hb
  exact cpsWithin_seq_same_cr (beq_notTaken hst base hstop (by omega) h1)
    (cpsWithin_seq_same_cr (addi_step hst base i) (bne_taken hst base he hs' h2))

/-- **The exit pass, with both `inr` branches.** The obligation is one
    statement; its proof is two machine paths.

    * `found`: `BEQ` taken. One instruction, the index untouched. Padded to the
      shared bound by `cpsWithin_mono`.
    * `exhausted`: `BEQ` not taken, `ADDI`, `BNE` not taken, `JAL`. Four
      instructions, and the index has become `e`. -/
theorem exit_ (hst : st.PlainAgree) (base : Word) (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    ∀ i y, (find stop e).body i = .inr y → side i →
      cpsWithin st 4 base (base + 16) (cr base) (I stop e i) (Q stop e y) := by
  intro i y hb hs
  have hs' : i + 1 < 2 ^ 64 := hs
  by_cases h1 : i = stop
  · -- Exit A: the search hit, from the top of the body.
    rw [body_found h1] at hb
    cases Sum.inr.inj hb
    exact cpsWithin_mono (by omega) (beq_taken hst base hstop (by omega) h1)
  by_cases h2 : i + 1 = e
  · -- Exit B: the range ran out, from the bottom of the body, via the `JAL`.
    rw [body_exhausted h1 h2] at hb
    cases Sum.inr.inj hb
    show cpsWithin st 4 base (base + 16) (cr base) (I stop e i) (I stop e e)
    rw [show I stop e e = I stop e (i + 1) by rw [h2]]
    exact cpsWithin_seq_same_cr (beq_notTaken hst base hstop (by omega) h1)
      (cpsWithin_seq_same_cr (addi_step hst base i)
        (cpsWithin_seq_same_cr (bne_notTaken hst base he hs' h2) (jal_join hst base (i + 1))))
  rw [body_cont h1 h2] at hb
  exact absurd hb (by simp)

end Obligations

/-! ## The certificate, and the two end-to-end statements -/

/-- `find` as an L2 certificate on any `PlainAgree` stepper. -/
def cert (hst : st.PlainAgree) (base : Word) {stop e : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) : Cert st Nat Res :=
  Cert.ofLoopB (nC := 3) (nE := 4) (f := result stop e)
    (cont hst base hstop he) (exit_ hst base hstop he) runsTo_eq_result

/-- **Exit A, end to end.** From any index at or below `stop`, with `stop`
    inside the range, the loop reaches the join with `x10 = stop`. On both
    backends, with no step bound. -/
theorem find_found (b : Backend) (base : Word) {stop e i : Nat}
    (hse : stop < e) (he : e < 2 ^ 64) (hi : i ≤ stop) :
    cpsTotalOn b base (base + 16) (cr base) (I stop e i) (I stop e stop) :=
  cpsTotal_loopB (cont (Backend.plainAgree b) base (by omega) he)
    (exit_ (Backend.plainAgree b) base (by omega) he)
    (runsTo_found hse he (stop - i) i (by omega))

/-- **Exit B, end to end.** From any index below `e`, if no index in `[i, e)`
    is `stop`, the loop reaches the join with `x10 = e`. -/
theorem find_exhausted (b : Backend) (base : Word) {stop e i : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) (hi : i < e)
    (hno : ∀ j, i ≤ j → j < e → j ≠ stop) :
    cpsTotalOn b base (base + 16) (cr base) (I stop e i) (I stop e e) :=
  cpsTotal_loopB (cont (Backend.plainAgree b) base hstop he)
    (exit_ (Backend.plainAgree b) base hstop he)
    (runsTo_exhausted he (e - 1 - i) i (by omega) hno)

-- The same two facts through the certificate, where the postcondition is
-- `Q (result stop e i)` and the closed form does the case analysis.
example (base : Word) {stop e i : Nat} (hse : stop < e) (he : e < 2 ^ 64) (hi : i ≤ stop) :
    cpsTotalOn .sp1 base (base + 16) (cr base) (I stop e i) (I stop e stop) := by
  have h := (cert (Backend.plainAgree .sp1) base (by omega) he).sound i
    ⟨_, _, runsTo_found hse he (stop - i) i (by omega)⟩
  have hr : result stop e i = .found stop := by simp only [result]; rw [if_pos (by omega)]
  simpa [cert, Cert.ofLoopB, hr, Q] using h

-- What the certificate says about itself.
example (base : Word) {stop e : Nat} (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    (cert (Backend.plainAgree .zisk) base hstop he).fn = result stop e := rfl
example (base : Word) {stop e : Nat} (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    (cert (Backend.plainAgree .sp1) base hstop he).pre = TerminatesB (find stop e) side := rfl

/-! ## The same loop with the join cut off: two exits, two labels

`cpsTotal_loopB_exits` lets the exit label depend on the output. Read the
region as the first three instructions only -- the `JAL` stays resident in
`cr` but is never executed -- and exit A is `base + 16`, exit B is
`base + 12`, with nothing joining them. The obligations are the ones above
minus `jal_join`, and the continue pass is unchanged. This is the consumer for
`ROADMAP.md` item 7's answer: the convergence requirement was never a property
of the machine, only of quantifying the exit before the output. -/

/-- The label each exit lands on when the region ends before the `JAL`. -/
def exitOf (base : Word) : Res → Word
  | .found _ => base + 16
  | .exhausted => base + 12

/-- The exit pass without the `JAL`: exit A in one step, exit B in three, each
    to its own label. -/
theorem exit_div (hst : st.PlainAgree) (base : Word) {stop e : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    ∀ i y, (find stop e).body i = .inr y → side i →
      cpsWithin st 3 base (exitOf base y) (cr base) (I stop e i) (Q stop e y) := by
  intro i y hb hs
  have hs' : i + 1 < 2 ^ 64 := hs
  by_cases h1 : i = stop
  · rw [body_found h1] at hb
    cases Sum.inr.inj hb
    exact cpsWithin_mono (by omega) (beq_taken hst base hstop (by omega) h1)
  by_cases h2 : i + 1 = e
  · rw [body_exhausted h1 h2] at hb
    cases Sum.inr.inj hb
    show cpsWithin st 3 base (base + 12) (cr base) (I stop e i) (I stop e e)
    rw [show I stop e e = I stop e (i + 1) by rw [h2]]
    exact cpsWithin_seq_same_cr (beq_notTaken hst base hstop (by omega) h1)
      (cpsWithin_seq_same_cr (addi_step hst base i) (bne_notTaken hst base he hs' h2))
  rw [body_cont h1 h2] at hb
  exact absurd hb (by simp)

/-- **Exit A, to its own label.** Same statement as `find_found`; the region no
    longer contains the join. -/
theorem find_found_div (b : Backend) (base : Word) {stop e i : Nat}
    (hse : stop < e) (he : e < 2 ^ 64) (hi : i ≤ stop) :
    cpsTotalOn b base (base + 16) (cr base) (I stop e i) (I stop e stop) :=
  cpsTotal_loopB_exits (exitOf := exitOf base)
    (cont (Backend.plainAgree b) base (by omega) he)
    (exit_div (Backend.plainAgree b) base (by omega) he)
    (runsTo_found hse he (stop - i) i (by omega))

/-- **Exit B, to a different label**: `base + 12`, where `find_exhausted` had
    to run on to `base + 16` through the `JAL`. -/
theorem find_exhausted_div (b : Backend) (base : Word) {stop e i : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) (hi : i < e)
    (hno : ∀ j, i ≤ j → j < e → j ≠ stop) :
    cpsTotalOn b base (base + 12) (cr base) (I stop e i) (I stop e e) :=
  cpsTotal_loopB_exits (exitOf := exitOf base)
    (cont (Backend.plainAgree b) base hstop he)
    (exit_div (Backend.plainAgree b) base hstop he)
    (runsTo_exhausted he (e - 1 - i) i (by omega) hno)

end Decomp.Examples.FindIndex
