/-
  Decomp.Sp1.Syscalls

  SP1's syscalls as triples: the ones this guest's emitted code uses, minus
  `HINT_READ` (`Decomp/Sp1/HintRead.lean`).

  `ECALL` is one of the two instructions the backends disagree on, so nothing
  here transfers from ZisK; each triple is proved against `stepSp1` directly,
  the way `Examples/Sp1Ecall.lean` proves the `HINT_LEN` sentinel. The step
  lemmas (`stepSp1_halt`, `stepSp1_commit_deferred`, `stepSp1_commit`,
  `stepSp1_hintLen`) are the semantic content; the triples are the same
  ten-line wrapper each time.

  * **`HALT`** (`t0 = 0`). `cpsHalt`: the machine cannot step. Under SP1 the id
    is delegated to `step`, which traps -- `stepSp1_ecall_host` then
    `step_ecall_halt`. With `a0 = 0` this *is* the accept observation for a
    decision-procedure guest (README "Observations"), stated at the leaf.
  * **`COMMIT_DEFERRED_PROOFS`** (`0x1a`). A no-op in the pinned executor;
    the model advances the pc. Eight of these sit before every `HALT`.
  * **`COMMIT`** (`0x10`). Appends `(a0, a1)` to `committed` and advances. The
    triple says `pc += 4` and *nothing else observable changed* -- which is
    true and weak: `PartialState` has no `committed` component, so no
    assertion can say what was committed. That gap is in README "Trust";
    it is harmless for a guest that commits nothing, and a real obligation for
    one that does. `holdsFor_sp1Commit` is the lemma that makes
    the weak statement provable: `CompatibleWith` does not mention `committed`.
  * **`HINT_LEN`** (`0xf0`), non-empty stream. `t0` becomes the front hint's
    length -- the little-endian doubleword at the head of `privateInput`. The
    empty-stream case is `Examples/Sp1Ecall.lean`'s sentinel.

  `HINT_READ` is in `Decomp/Sp1/HintRead.lean`. Its postcondition is a
  `bytesRegionSp1` of `n / 8 + 1` doublewords (SP1 always writes a trailing
  zero-padded word), and it needs the `writeBytesAsWords` readback lemmas that
  file supplies; a wrong extent there is silently unsound, so it is pinned
  against the model with `#guard`s.
-/

module

public import Decomp.Leaf.Sp1Text

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64

variable {lo hi : Nat}

/-! ## Lifting a halt triple onto the confined stepper -/

theorem cpsHalt_sp1Text_of_sp1 {entry : Word} {cr : CodeReq} {P Q : Assertion}
    (h : cpsHaltOn .sp1 entry cr P Q) : cpsHalt (Sp1Text lo hi) entry cr P Q := by
  intro R hR s _ hcr hPR hpc
  obtain ⟨k, s', hstep, hhalt, hQR⟩ := h R hR s trivial hcr hPR hpc
  exact ⟨k, s', (Sp1Text_iter lo hi k s).trans hstep, hhalt, hQR⟩

abbrev cpsSyscallHaltOn (b : Backend) (entry : Word) (cr : CodeReq) (P Q : Assertion) :
    Prop := cpsSyscallHalt (Backend.stepper b) entry cr P Q

theorem cpsSyscallHalt_sp1Text_of_sp1 {entry : Word} {cr : CodeReq} {P Q : Assertion}
    (h : cpsSyscallHaltOn .sp1 entry cr P Q) :
    cpsSyscallHalt (Sp1Text lo hi) entry cr P Q := by
  intro R hR s _ hcr hPR hpc
  obtain ⟨k, s', hstep, hhalt, hQR⟩ := h R hR s trivial hcr hPR hpc
  exact ⟨k, s', (Sp1Text_iter lo hi k s).trans hstep, hhalt, hQR⟩

/-! ## HALT -/

/-- `HALT` traps under SP1 as under ZisK: the id is a host id, so `stepSp1`
    delegates to `step`, which returns `none`. -/
theorem stepSp1_halt {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = 0) : stepSp1 s = none := by
  rw [stepSp1_ecall_host hfetch (by rw [ht0]; decide)]
  exact step_ecall_halt hfetch ht0

/-- Every state the ABI calls halted really does stop the SP1 machine. This is
    the backend fact `cpsHalt_of_cpsSyscallHalt` asks for, and it is what makes
    the strong accept observation no weaker than the old one. -/
theorem stepSp1_isNone_of_syscallHalted {s : MachineState} (h : SyscallHalted s) :
    (stepSp1 s).isNone := by
  rw [stepSp1_halt h.1 h.2]; rfl

/-- **The accept observation, at the leaf.** From `t0 = 0` at an `ECALL`, the
    SP1 machine is halted *by the halt syscall* -- not merely unable to step --
    and the registers, in particular `a0`, the exit code, are what they were.
    Zero steps: the halted state is the entry state.

    The reason is in the conclusion rather than only in the precondition
    because that is the difference between this and a trap; README
    "Observations" is the finding that discarding it broke the reject-path
    argument. -/
theorem halt_sp1 (exitCode base : Word) :
    cpsSyscallHaltOn .sp1 base (CodeReq.singleton base .ECALL)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) := by
  intro R hR s _ hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some .ECALL := CodeReq.singleton_satisfiedBy.mp hcr
  have hx5 : s.getReg .x5 = 0 :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  exact ⟨0, s, rfl, ⟨hfetch, hx5⟩, hPR⟩

theorem halt_sp1Text (exitCode base : Word) :
    cpsSyscallHalt (Sp1Text lo hi) base (CodeReq.singleton base .ECALL)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) :=
  cpsSyscallHalt_sp1Text_of_sp1 (halt_sp1 exitCode base)

/-- The old, weaker observation, for callers that only need "the machine stops
    here". Kept so nothing that consumed `halt_sp1Text` at `cpsHalt` is
    stranded by the strengthening. -/
theorem halt_sp1Text_weak (exitCode base : Word) :
    cpsHalt (Sp1Text lo hi) base (CodeReq.singleton base .ECALL)
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)) :=
  cpsHalt_of_cpsSyscallHalt (fun _ h => stepSp1_isNone_of_syscallHalted h)
    (halt_sp1Text exitCode base)

/-! ## COMMIT_DEFERRED_PROOFS -/

theorem stepSp1_commit_deferred {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.COMMIT_DEFERRED_PROOFS) :
    stepSp1 s = some (s.setPC (s.pc + 4)) := by
  have hacc : Sp1.isAccelId Sp1.COMMIT_DEFERRED_PROOFS = false := by decide
  have h1 : Sp1.COMMIT_DEFERRED_PROOFS ≠ Sp1.HINT_LEN := by decide
  have h2 : Sp1.COMMIT_DEFERRED_PROOFS ≠ Sp1.HINT_READ := by decide
  have h3 : Sp1.COMMIT_DEFERRED_PROOFS ≠ Sp1.COMMIT := by decide
  unfold stepSp1; rw [hfetch]
  simp only [sp1Ecall, ht0]
  simp [hacc, h1, h2, h3]

/-- The model's no-op: `pc += 4`, registers untouched. -/
theorem commit_deferred_sp1 (base : Word) :
    cpsWithinOn .sp1 1 base (base + 4) (CodeReq.singleton base .ECALL)
      (.x5 ↦ᵣ Sp1.COMMIT_DEFERRED_PROOFS) (.x5 ↦ᵣ Sp1.COMMIT_DEFERRED_PROOFS) := by
  intro R hR s _ hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some .ECALL := CodeReq.singleton_satisfiedBy.mp hcr
  have ht0 : s.getReg .x5 = Sp1.COMMIT_DEFERRED_PROOFS :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR)
  refine ⟨1, Nat.le_refl 1, s.setPC (s.pc + 4), ?_, ?_, ?_⟩
  · show ((Backend.stepper .sp1).next s).bind ((Backend.stepper .sp1).iter 0) = _
    rw [Backend.stepper_next, stepOn_sp1, stepSp1_commit_deferred hfetch ht0]
    rfl
  · simp [MachineState.setPC]
  · exact holdsFor_pcFree_setPC (pcFree_sepConj pcFree_regIs hR) hPR

/-! ## COMMIT -/

/-- `sp1Commit` changes only `committed`, which no `PartialState` component
    observes. So every assertion survives it. This lemma is the whole reason a
    `COMMIT` triple can be stated at all -- and the reason it says so little. -/
theorem CompatibleWith_sp1Commit {h : PartialState} {s : MachineState}
    (hc : h.CompatibleWith s) : h.CompatibleWith s.sp1Commit := by
  simpa [PartialState.CompatibleWith, MachineState.sp1Commit, MachineState.getReg,
    MachineState.getMem] using hc

theorem holdsFor_sp1Commit {P : Assertion} {s : MachineState} (h : P.holdsFor s) :
    P.holdsFor s.sp1Commit := by
  obtain ⟨hp, hc, hP⟩ := h
  exact ⟨hp, CompatibleWith_sp1Commit hc, hP⟩

theorem stepSp1_commit {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.COMMIT) :
    stepSp1 s = some (s.sp1Commit.setPC (s.pc + 4)) := by
  have hacc : Sp1.isAccelId Sp1.COMMIT = false := by decide
  have h1 : Sp1.COMMIT ≠ Sp1.HINT_LEN := by decide
  have h2 : Sp1.COMMIT ≠ Sp1.HINT_READ := by decide
  unfold stepSp1; rw [hfetch]
  simp only [sp1Ecall, ht0]
  simp [hacc, h1, h2]

/-- `COMMIT`: `pc += 4`, and nothing an assertion can see has changed. The
    pair `(a0, a1)` went to `committed`, about which the assertion language
    is silent -- see the header. -/
theorem commit_sp1 (idx w base : Word) :
    cpsWithinOn .sp1 1 base (base + 4) (CodeReq.singleton base .ECALL)
      ((.x5 ↦ᵣ Sp1.COMMIT) ** (.x10 ↦ᵣ idx) ** (.x11 ↦ᵣ w))
      ((.x5 ↦ᵣ Sp1.COMMIT) ** (.x10 ↦ᵣ idx) ** (.x11 ↦ᵣ w)) := by
  intro R hR s _ hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some .ECALL := CodeReq.singleton_satisfiedBy.mp hcr
  have ht0 : s.getReg .x5 = Sp1.COMMIT :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_left hPR))
  refine ⟨1, Nat.le_refl 1, s.sp1Commit.setPC (s.pc + 4), ?_, ?_, ?_⟩
  · show ((Backend.stepper .sp1).next s).bind ((Backend.stepper .sp1).iter 0) = _
    rw [Backend.stepper_next, stepOn_sp1, stepSp1_commit hfetch ht0]
    rfl
  · simp [MachineState.setPC, MachineState.sp1Commit]
  · exact holdsFor_pcFree_setPC
      (pcFree_sepConj (pcFree_sepConj pcFree_regIs (pcFree_sepConj pcFree_regIs pcFree_regIs)) hR)
      (holdsFor_sp1Commit hPR)

/-! ## HINT_LEN, non-empty stream -/

theorem stepSp1_hintLen {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.HINT_LEN) : stepSp1 s = some (hintLen s) := by
  unfold stepSp1; rw [hfetch]
  simp only [sp1Ecall, ht0, Sp1.isAccelId_hint_false.1]
  simp

/-- The front hint's length, as the guest reads it: the little-endian
    doubleword at the head of the stream. -/
def frontLen (input : List (BitVec 8)) : Word :=
  BitVec.ofNat 64 (bytesToWordLE (input.take 8)).toNat

/-- `HINT_LEN` with at least one framed hint in the stream: `t0` becomes the
    front vector's length; the stream is not consumed. -/
theorem hintLen_sp1 (input : List (BitVec 8)) (hlen : 8 ≤ input.length) (base : Word) :
    cpsWithinOn .sp1 1 base (base + 4) (CodeReq.singleton base .ECALL)
      ((.x5 ↦ᵣ Sp1.HINT_LEN) ** privateInputIs input)
      ((.x5 ↦ᵣ frontLen input) ** privateInputIs input) := by
  intro R hR s _ hcr hPR hpc; subst hpc
  have hfetch : s.code s.pc = some .ECALL := CodeReq.singleton_satisfiedBy.mp hcr
  have hPR' := holdsFor_sepConj_assoc.mp hPR
  have ht0 : s.getReg .x5 = Sp1.HINT_LEN :=
    holdsFor_regIs.mp (holdsFor_sepConj_elim_left hPR')
  have hpi : s.privateInput = input :=
    holdsFor_privateInputIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right hPR'))
  have hfront : frontHintLen s = some (bytesToWordLE (input.take 8)).toNat := by
    simp [frontHintLen, hpi, Nat.not_lt.mpr hlen]
  have hhl : hintLen s = (s.setReg .x5 (frontLen input)).setPC (s.pc + 4) := by
    simp [hintLen, hfront, frontLen]
  refine ⟨1, Nat.le_refl 1, (s.setReg .x5 (frontLen input)).setPC (s.pc + 4), ?_, ?_, ?_⟩
  · show ((Backend.stepper .sp1).next s).bind ((Backend.stepper .sp1).iter 0) = _
    rw [Backend.stepper_next, stepOn_sp1, stepSp1_hintLen hfetch ht0, hhl]
    rfl
  · simp [MachineState.setPC]
  · exact holdsFor_sepConj_assoc.mpr
      (holdsFor_pcFree_setPC (pcFree_sepConj (by pcFree) (pcFree_sepConj (by pcFree) hR))
        (holdsFor_sepConj_regIs_setReg (by simp) hPR'))

end Decomp
