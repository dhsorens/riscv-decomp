/-
  Decomp.Examples.CountdownMachine

  The machine-level half: `countdown_loop` end to end, as a `Cert`, on every
  backend at once.

  `Decomp/Examples/Countdown.lean` decompiled the loop's abstract half -- the
  `Rec`, its termination, its extracted function -- and stopped. This file
  drives `Cert.ofLoop` against the actual instructions with **no framework
  work**: three existing upstream leaf specs (all proved over ZisK's `step`),
  each entering the `Stepper`-generic world through
  `Decomp.Leaf.Core`'s transfer, framed and composed by the rules in
  `Decomp/Triple.lean`.

  The whole development is parametrised by a `Stepper` and one hypothesis,
  `st.PlainAgree`: the stepper agrees with ZisK on instructions that are not
  memory accesses, `ECALL` or `EBREAK`. `BEQ`, `ADDI` and `JAL` are all such,
  so nothing here knows which backend it is on. `Backend.plainAgree`
  discharges the hypothesis for both, and `countdown_total` at the bottom is
  therefore a theorem about ZisK *and* SP1 from one proof -- the first SP1
  loop triple in this repository, and upstream cannot state it on either
  backend: `WP.loopNatCert` needs `fuel` as a literal, and here the trip count
  is the input. Upstream exercises this program only with `decide` at
  `x10 ∈ {0, 1, 3}`.

  ## What Phase 1 found about the interface

  `cpsTotal_loop`'s header-true hypothesis originally received only
  `r.guard x = true`. Here that is `n ≠ 0`, and the header needs
  `BitVec.ofNat 64 n ≠ 0`, which does not follow without `n < 2^64` -- the
  per-iteration `side`. In the `iter` case of the induction `side x` is
  available from the constructor, so the rule now passes it through at zero
  cost. The `exit` constructor carries no `side`, so `hHeaderFalse` cannot
  receive it -- and does not need it here: `n = 0` gives `ofNat 0 = 0`
  directly. That asymmetry is TR-765's, not ours: the side condition is only
  checked on states the loop *iterates from*.
-/

import Decomp.Certificate
import Decomp.Leaf.Sp1Step
import Decomp.Examples.Countdown
import RiscvZkvm.Rv64.Logic

namespace Decomp.Examples.Countdown

open RiscvZkvm.Rv64

variable {st : Stepper}

/-- Upstream's `RiscvZkvm.Rv64.countdown_loop`, at an arbitrary base:

        base+0:  BEQ  x10, x0, +12    -- header: exit when the counter is zero
        base+4:  ADDI x10, x10, -1    -- body
        base+8:  JAL  x0, -8          -- back to the header

    Restated rather than imported so the offsets are visible next to the
    address arithmetic below. -/
def prog : Program := [
  .BEQ .x10 .x0 (12 : BitVec 13),
  .ADDI .x10 .x10 (BitVec.ofNat 12 (2 ^ 12 - 1)),
  .JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 8))
]

/-- The code requirement: the three instructions, resident at `base`. -/
def cr (base : Word) : CodeReq := CodeReq.ofProg base prog

/-- The coupling. The abstract counter is in `x10`; `x0` is owned as well so the
    BEQ leaf, which compares two registers, can name it. -/
def I (n : Nat) : Assertion := (.x10 ↦ᵣ BitVec.ofNat 64 n) ** (.x0 ↦ᵣ (0 : Word))

/-! ## Address arithmetic

The two offsets, evaluated once. `decide` is kernel-checked; there is no
`native_decide` here. -/

theorem sext13_twelve : signExtend13 (12 : BitVec 13) = (12 : Word) := by decide

theorem sext12_neg1 : signExtend12 (BitVec.ofNat 12 (2 ^ 12 - 1)) = (-1 : Word) := by decide

theorem sext21_neg8 : signExtend21 (BitVec.ofNat 21 (2 ^ 21 - 8)) = (-8 : Word) := by decide

/-- The abstract `n - 1` really is the machine's `x10 - 1`, on the domain the
    side condition carves out. This is the fact `side` exists to license. -/
theorem ofNat_pred {n : Nat} (hne : n ≠ 0) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n + (-1 : Word) = BitVec.ofNat 64 (n - 1) := by
  bv_omega

/-- The backward jump lands on the header: `base + 8 - 8 = base`. -/
theorem jal_target (base : Word) : base + 4 + 4 + (-8 : Word) = base := by bv_omega

/-- Writes to `x0` are dropped, by definition of `setReg`. -/
theorem setReg_x0 (s : MachineState) (v : Word) : s.setReg .x0 v = s := rfl

theorem ofNat_ne_zero {n : Nat} (hne : n ≠ 0) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ (0 : Word) := by
  intro h
  have := congrArg BitVec.toNat h
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
  exact hne this

/-! ## Code residency

Each leaf owns exactly its own instruction; `extend_code` lifts it to the
whole three-instruction `cr`. -/

theorem beq_sub (base : Word) :
    ∀ a i, CodeReq.singleton base (.BEQ .x10 .x0 (12 : BitVec 13)) a = some i →
      cr base a = some i :=
  CodeReq.singleton_mono (CodeReq.ofProg_lookup_zero base _ _)

theorem addi_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 4) (.ADDI .x10 .x10 (BitVec.ofNat 12 (2 ^ 12 - 1))) a
        = some i → cr base a = some i :=
  CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base prog 1 (base + 4) (by decide) (by decide)
      (by bv_omega))

theorem jal_sub (base : Word) :
    ∀ a i, CodeReq.singleton (base + 4 + 4) (.JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 8))) a
        = some i → cr base a = some i :=
  CodeReq.singleton_mono
    (CodeReq.ofProg_lookup_addr base prog 2 (base + 4 + 4) (by decide) (by decide)
      (by bv_omega))

/-! ## The three obligations `Cert.ofLoop` asks for -/

/-- Header, guard true: the counter is nonzero, so `BEQ x10, x0` falls through
    to the body with the coupling intact. Needs `side` for `ofNat n ≠ 0`. -/
theorem headerTrue (hst : st.PlainAgree) (base : Word) :
    ∀ n, countdown.guard n = true → side n →
      cpsWithin st 1 base (base + 4) (cr base) (I n) (I n) := by
  intro n hg hs
  have hne : n ≠ 0 := by simpa [countdown] using hg
  have hbv := ofNat_ne_zero hne hs
  have hbr := cpsBranch_of_zisk_plain hst (CodeReq.singleton_self _ _) rfl (by nofun) (by nofun)
    (generic_beq_spec_within .x10 .x0 (12 : BitVec 13) (BitVec.ofNat 64 n) 0 base)
  refine cpsWithin_extend_code (beq_sub base) ?_
  refine cpsWithin_weaken (fun _ hp => hp) ?_
    (cpsBranch_notTakenPath (fun hp hq => ?_) hbr)
  · -- drop the pure `⌜ofNat n ≠ 0⌝` from the fallthrough post
    intro h hq
    exact sepConj_mono_right (fun h' hbc => ((sepConj_pure_right h').mp hbc).1) h hq
  · -- the taken arm carries `⌜ofNat n = 0⌝`, which `side` rules out
    obtain ⟨_, h2, _, _, _, hbc⟩ := hq
    exact hbv ((sepConj_pure_right h2).mp hbc).2

/-- Header, guard false: the counter is zero, so `BEQ` is taken to the exit. -/
theorem headerFalse (hst : st.PlainAgree) (base : Word) :
    ∀ n, countdown.guard n = false →
      cpsWithin st 1 base (base + 12) (cr base) (I n) (I (countdown.out n)) := by
  intro n hg
  have hz : n = 0 := by simpa [countdown] using hg
  subst hz
  have hbr := cpsBranch_of_zisk_plain hst (CodeReq.singleton_self _ _) rfl (by nofun) (by nofun)
    (generic_beq_spec_within .x10 .x0 (12 : BitVec 13) (BitVec.ofNat 64 0) 0 base)
  rw [sext13_twelve] at hbr
  refine cpsWithin_extend_code (beq_sub base) ?_
  refine cpsWithin_weaken (fun _ hp => hp) ?_
    (cpsBranch_takenPath (fun hp hq => ?_) hbr)
  · intro h hq
    exact sepConj_mono_right (fun h' hbc => ((sepConj_pure_right h').mp hbc).1) h hq
  · obtain ⟨_, h2, _, _, _, hbc⟩ := hq
    exact ((sepConj_pure_right h2).mp hbc).2 rfl

/-- Body: `ADDI x10, x10, -1` then `JAL x0, -8`. Two bounded leaves, framed and
    sequenced; the counter goes from `n` to `n - 1`. -/
theorem body (hst : st.PlainAgree) (base : Word) :
    ∀ n, countdown.guard n = true → side n →
      cpsWithin st 2 (base + 4) base (cr base) (I n) (I (countdown.step n)) := by
  intro n hg hs
  have hne : n ≠ 0 := by simpa [countdown] using hg
  -- ADDI at base+4: x10 := x10 - 1, framed by x0.
  have haddi : cpsWithin st 1 (base + 4) (base + 4 + 4) (cr base)
      (I n) (I (n - 1)) := by
    have h := cpsWithin_of_zisk_plain hst (CodeReq.singleton_self _ _) rfl (by nofun) (by nofun)
      (addi_spec_same_within .x10 (BitVec.ofNat 64 n) (BitVec.ofNat 12 (2 ^ 12 - 1))
        (base + 4) (by decide))
    rw [sext12_neg1, ofNat_pred hne hs] at h
    exact cpsWithin_extend_code (addi_sub base) (cpsWithin_frameR _ (by pcFree) h)
  -- JAL x0 at base+8: pc := base, nothing else. Framed by the whole coupling.
  have hjal : cpsWithin st 1 (base + 4 + 4) base (cr base)
      (I (n - 1)) (I (n - 1)) := by
    have hpc : ∀ s : MachineState, s.pc = base + 4 + 4 →
        execInstrBr s (.JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 8))) = s.setPC base := by
      intro s hpc
      simp only [execInstrBr, setReg_x0, hpc, sext21_neg8, jal_target]
    have h := cpsWithin_of_zisk_plain hst (CodeReq.singleton_self _ _) rfl (by nofun) (by nofun)
      (generic_nop_spec_within (.JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 8)))
        (base := base + 4 + 4) (exit_ := base) hpc
        (fun s hf => step_non_ecall_non_mem hf (by nofun) (by nofun) rfl))
    refine cpsWithin_extend_code (jal_sub base) ?_
    refine cpsWithin_weaken ?_ ?_ (cpsWithin_frameL (I (n - 1)) (by pcFree) h)
    · intro h hp; rw [sepConj_emp_right']; exact hp
    · intro h hq; rwa [sepConj_emp_right'] at hq
  exact cpsWithin_seq_same_cr haddi hjal

/-! ## The certificate -/

/-- `countdown_loop` as an L2 certificate on any `PlainAgree` stepper: the
    extracted function is the constant `0`, the side condition is
    `Terminates countdown side`, and the coupling is `I`. -/
def cert (hst : st.PlainAgree) (base : Word) : Cert st Nat Nat :=
  Cert.ofLoop (nH := 1) (nB := 2) (f := fun _ => 0)
    (headerTrue hst base) (headerFalse hst base) (body hst base) runN_eq_const

/-- **The statement upstream cannot make, on either backend.** For *every*
    representable counter, the loop reaches its exit with `x10 = 0`. No `fuel`,
    no step bound: the trip count is `n` itself, and it is eliminated by
    `TerminatesIn`'s induction. One proof, both backends. -/
theorem countdown_total (b : Backend) (base : Word) {n : Nat} (hn : side n) :
    cpsTotalOn b base (base + 12) (cr base) (I n) (I 0) :=
  (cert (Backend.plainAgree b) base).sound n (terminates hn)

-- The SP1 instance, spelled out: the first SP1 loop triple in this repository.
example (base : Word) {n : Nat} (hn : side n) :
    cpsTotalOn .sp1 base (base + 12) (cr base) (I n) (I 0) :=
  countdown_total .sp1 base hn

-- What the certificate says about itself, checked by `rfl`.
example (base : Word) : (cert (Backend.plainAgree .zisk) base).fn = fun _ => 0 := rfl
example (base : Word) :
    (cert (Backend.plainAgree .sp1) base).pre = Terminates countdown side := rfl
example (base : Word) :
    (cert (Backend.plainAgree .sp1) base).entry = base ∧
      (cert (Backend.plainAgree .sp1) base).exit_ = base + 12 := ⟨rfl, rfl⟩

end Decomp.Examples.Countdown
