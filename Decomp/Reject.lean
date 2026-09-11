/-
  Decomp.Reject

  The reject path: showing a region *cannot* accept.

  A soundness statement about a decision-procedure guest is quantified over
  every input, so it owes an argument for the code it does *not* verify
  functionally: those regions cannot reach the accept observation. For a Rust
  guest that is the `core`/`alloc`/`fmt`/panic machinery -- typically a
  substantial fraction of the image, which needs no functional proof at all if
  this argument exists and cannot be dropped for any reason if it does not.

  ## What had to change first

  The argument does not go through against `cpsHalt`, whose observation is
  `(st.next s').isNone`. That is true of a real `HALT` *and* of every trap, so
  a state with no code at its pc and `a0 = 0` satisfies it exactly as an
  accepting halt does -- and the cheapest case, an `unimp` word the loader left
  undecoded, would then need a proof that `a0 ≠ 0` at them rather than a definitional one.
  `Decomp/Triple.lean`'s `SyscallHalted` is the fix, and
  `cpsHalt_of_cpsSyscallHalt` shows nothing was lost by pinning the reason.
  README "Observations" has the finding in full.

  ## The shape of the argument here

  Two facts, and nothing else:

  * a state whose pc has no code cannot be `SyscallHalted`, because
    `SyscallHalted` demands an `ECALL` there; and
  * a state the machine cannot leave is the only state its own continuations
    reach, so "does not accept" propagates from that state to the whole run.

  The second needs `iter`'s determinism *both ways* -- a run that accepts at
  step `k` and gets stuck at step `j` forces `j = k` -- which is why
  `not_accepts_of_reaches_stuck` takes the backend fact that an accepting halt
  is itself stuck. Without it the run could be imagined to accept *before*
  reaching the stuck state.

  ## The halting half

  Panic machinery generally does not trap -- it reaches the `HALT` syscall with
  a **nonzero** `a0`, so it *is* `SyscallHalted`, and the two facts above say
  nothing about it. `Accepted` (halted by the syscall, *and* `a0 = 0`) is the
  observation that separates the two -- by the **host-ABI convention** that
  `a0` is the exit code, which the machine model does not know; see its
  docstring -- and the second half of this file refutes it two ways: from a `cpsSyscallHalt` whose postcondition pins `a0`
  (`not_accepted_of_cpsSyscallHalt`, composing with the halt leaf), and from an
  invariant that survives every step (`not_accepted_of_invariant`). Both have
  their run-induction done once here. Neither has a consumer yet: the `a0 ↦ᵣ 1`
  at a guest's panic halt is a fact that guest owes.

  ## What this does not do

  It does not say where a *particular* image has an undecodable word. That is
  the instantiating guest's job, and it is a measurement rather than a theorem:
  `Interpreter.load` builds `code` with an `Id.run do` loop over `HashMap`s
  (`Interpreter/Run.lean:123`), so there is nothing to prove a theorem about.
  What is kernel-checkable is everything downstream of `s.code s.pc = none`,
  which is what is here.
-/

module

public import Decomp.Sp1.Syscalls

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64

/-! ## Stuck states -/

/-- A state the machine cannot leave is the only state its own continuations
    reach. -/
theorem iter_eq_self_of_next_none {st : Stepper} {s s' : MachineState} {k : Nat}
    (hnext : st.next s = none) (h : st.iter k s = some s') : s' = s := by
  cases k with
  | zero => exact (Option.some.inj h).symm
  | succ k => rw [Stepper.iter_succ, hnext] at h; simp at h

/-- No code at the pc is not a halt. `SyscallHalted` demands an `ECALL` there,
    which is the whole point of pinning the reason. -/
theorem not_syscallHalted_of_code_none {s : MachineState} (h : s.code s.pc = none) :
    ¬ SyscallHalted s := by
  intro hh
  rw [hh.1] at h
  exact absurd h (by simp)

/-- **The reject-path foothold, in general form.** If a run reaches a state the
    machine cannot leave and which is not itself an accepting halt, then *no*
    state the run reaches is an accepting halt -- not just the states after it.

    `htrap` is what rules out the run accepting *earlier* than it gets stuck:
    an accepting halt is stuck too, so the two events cannot be ordered, and
    determinism collapses them. It is a fact about the backend
    (`Decomp/Sp1/Syscalls.lean`'s `stepSp1_isNone_of_syscallHalted` for SP1),
    deliberately not a `Stepper` field. -/
theorem not_reaches_of_reaches_stuck {st : Stepper} {Acc : MachineState → Prop}
    {s₀ t : MachineState} {j : Nat}
    (hreach : st.iter j s₀ = some t)
    (hstuck : st.next t = none) (hnt : ¬ Acc t)
    (hAcc : ∀ u, Acc u → (st.next u).isNone) :
    ∀ k s', st.iter k s₀ = some s' → ¬ Acc s' := by
  intro k s' hk hacc
  rcases Nat.le_total j k with hle | hle
  · -- The run got stuck first, so `s'` is that stuck state.
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    subst hd
    rw [Stepper.iter_add, hreach, Option.bind] at hk
    exact hnt (iter_eq_self_of_next_none hstuck hk ▸ hacc)
  · -- The run accepted first -- but an accepting state is stuck, so the state
    -- reached later is that same state, and it is not accepting.
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    subst hd
    rw [Stepper.iter_add, hk, Option.bind] at hreach
    have hs'stuck : st.next s' = none := Option.isNone_iff_eq_none.mp (hAcc s' hacc)
    exact hnt (iter_eq_self_of_next_none hs'stuck hreach ▸ hacc)

/-- The trapping half's instance: `Acc := SyscallHalted`. -/
theorem not_accepts_of_reaches_stuck {st : Stepper} {s₀ t : MachineState} {j : Nat}
    (hreach : st.iter j s₀ = some t)
    (hstuck : st.next t = none) (hns : ¬ SyscallHalted t)
    (htrap : ∀ u, SyscallHalted u → (st.next u).isNone) :
    ∀ k s', st.iter k s₀ = some s' → ¬ SyscallHalted s' :=
  not_reaches_of_reaches_stuck hreach hstuck hns htrap

/-! ## The halting half: halted, but with the wrong exit code

Panic machinery does not trap. It runs through formatting and reaches the
`HALT` syscall with a **nonzero** `a0`, so it *is* `SyscallHalted`, and the
argument above says nothing about it. What rules it out is a fact about a
*value*: the exit code the halt carries.

`Accepted` is the observation a soundness theorem's accepting-run antecedent
should have: halted by the halt syscall, exit code zero. The two rules below
are the two ways to refute it -- from a triple whose halt postcondition pins
`a0`, or from an invariant that survives every step -- with the induction over
the run done once here rather than per guest. -/

/-- **Accepted, as a convention**: halted by the halt syscall, with `a0 = 0`.

    `SyscallHalted` is the machine's own event -- `stepSp1` stops on `t0 = 0`.
    That `a0` is the *exit code*, and that zero means the host accepts, is the
    **host ABI**, not the step relation: `Program.lean`'s `HALT` macro puts the
    exit code in `a0`, and the interpreter reports `a0` as the guest's exit
    value, but the machine model assigns `a0` no meaning at a halt. So every
    `¬ Accepted` below is a theorem about this convention. Whether it is the
    *verifier's* acceptance event -- whether a run with `a0 ≠ 0` here can still
    be accepted by the prover, or one with `a0 = 0` rejected -- is the owed
    adversarial pass in `ROADMAP.md`; until it runs, read `Accepted` as "the
    host-ABI accept", not as "the prover accepted". -/
def Accepted (s : MachineState) : Prop :=
  SyscallHalted s ∧ s.getReg .x10 = 0

theorem Accepted.syscallHalted {s : MachineState} (h : Accepted s) : SyscallHalted s := h.1

/-- **From a halt triple.** If a region's run halts by the syscall with `Q`
    holding, and `Q` says `a0 ≠ 0`, then no state of that run -- before or
    after the halt -- is `Accepted`.

    This is the judgement that composes with `cpsSyscallHalt`: a panic path is
    `cpsTotal` to the halt site, then `halt_sp1Text exitCode`, then this. `hQ`
    is the block-local fact; `htrap` is the backend's "a halt is stuck". -/
theorem not_accepted_of_cpsSyscallHalt {st : Stepper} {entry : Word} {cr : CodeReq}
    {P Q : Assertion}
    (h : cpsSyscallHalt st entry cr P Q)
    (hQ : ∀ s, Q.holdsFor s → s.getReg .x10 ≠ 0)
    (htrap : ∀ u, SyscallHalted u → (st.next u).isNone) :
    ∀ R : Assertion, R.pcFree → ∀ s, st.inv s → cr.SatisfiedBy s → (P ** R).holdsFor s →
      s.pc = entry → ∀ k s', st.iter k s = some s' → ¬ Accepted s' := by
  intro R hR s hinv hcr hPR hpc
  obtain ⟨j, t, hreach, hhalt, hQR⟩ := h R hR s hinv hcr hPR hpc
  exact not_reaches_of_reaches_stuck hreach
    (Option.isNone_iff_eq_none.mp (htrap t hhalt))
    (fun hacc => hQ t (holdsFor_sepConj_elim_left hQR) hacc.2)
    (fun u hu => htrap u hu.1)

/-- The shape the `HALT` leaf produces: `(x5 ↦ᵣ 0) ** (x10 ↦ᵣ exitCode)`. A
    nonzero exit code is the whole block-local fact. -/
theorem not_accepted_of_cpsSyscallHalt_exitCode {st : Stepper} {entry : Word} {cr : CodeReq}
    {P : Assertion} {exitCode : Word}
    (h : cpsSyscallHalt st entry cr P ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode)))
    (hne : exitCode ≠ 0)
    (htrap : ∀ u, SyscallHalted u → (st.next u).isNone) :
    ∀ R : Assertion, R.pcFree → ∀ s, st.inv s → cr.SatisfiedBy s → (P ** R).holdsFor s →
      s.pc = entry → ∀ k s', st.iter k s = some s' → ¬ Accepted s' :=
  not_accepted_of_cpsSyscallHalt h
    (fun _ hQ => by
      rw [holdsFor_regIs.mp (holdsFor_sepConj_elim_right hQ)]; exact hne)
    htrap

/-- **From an invariant.** If `J` holds at the start, survives every step, and
    excludes acceptance, no state of the run is `Accepted`. The induction over
    the run, done once; a guest supplies `J` ("`a0` is nonzero and stays so",
    say) and the three block-local facts. -/
theorem not_accepted_of_invariant {st : Stepper} {J : MachineState → Prop} {s₀ : MachineState}
    (h0 : J s₀)
    (hstep : ∀ s s', J s → st.next s = some s' → J s')
    (hns : ∀ s, J s → ¬ Accepted s) :
    ∀ k s', st.iter k s₀ = some s' → ¬ Accepted s' := by
  intro k
  induction k generalizing s₀ with
  | zero => intro s' h; cases h; exact hns _ h0
  | succ k ih =>
    intro s' h
    rw [Stepper.iter_succ] at h
    cases hn : st.next s₀ with
    | none => rw [hn] at h; simp at h
    | some s₁ => rw [hn] at h; exact ih (hstep _ _ h0 hn) s' h

/-! ## The SP1 instance -/

variable {lo hi : Nat}

/-- The halting half on the confined SP1 stepper: a region that reaches the
    `HALT` leaf with a nonzero exit code never accepts. `hreach` is the
    region's own `cpsTotal` to the halt site, with the halt leaf's precondition
    as its postcondition. -/
theorem not_accepted_of_halt_sp1Text {entry haltSite : Word} {cr : CodeReq} {P : Assertion}
    {exitCode : Word} (hne : exitCode ≠ 0)
    (hcr : cr haltSite = some .ECALL)
    (hreach : cpsTotal (Sp1Text lo hi) entry haltSite cr P
      ((.x5 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ exitCode))) :
    ∀ R : Assertion, R.pcFree → ∀ s, CodeWithin lo hi s → cr.SatisfiedBy s →
      (P ** R).holdsFor s → s.pc = entry →
      ∀ k s', (Sp1Text lo hi).iter k s = some s' → ¬ Accepted s' :=
  not_accepted_of_cpsSyscallHalt_exitCode
    (cpsTotal_seq_cpsSyscallHalt_same_cr hreach
      (cpsSyscallHalt_extend_code (CodeReq.singleton_mono hcr) (halt_sp1Text exitCode haltSite)))
    hne
    (fun _ h => by rw [Sp1Text_next]; exact stepSp1_isNone_of_syscallHalted h)

/-- An address the loader left undecoded traps: `stepSp1` matches on
    `s.code s.pc` first. -/
theorem stepSp1_of_code_none {s : MachineState} (h : s.code s.pc = none) :
    stepSp1 s = none := by unfold stepSp1; rw [h]

/-- **A run that reaches an undecoded word does not accept.** On the confined
    SP1 stepper, so it composes with everything else in `Decomp/`.

    Every region a run can only enter at an undecoded word is discharged by
    this, modulo the measured fact that the image really holds such a word
    there -- see this file's header. -/
theorem not_accepts_of_reaches_code_none {s₀ t : MachineState} {j : Nat}
    (hreach : (Sp1Text lo hi).iter j s₀ = some t) (hcode : t.code t.pc = none) :
    ∀ k s', (Sp1Text lo hi).iter k s₀ = some s' → ¬ SyscallHalted s' :=
  not_accepts_of_reaches_stuck hreach
    (by rw [Sp1Text_next]; exact stepSp1_of_code_none hcode)
    (not_syscallHalted_of_code_none hcode)
    (fun _ h => by rw [Sp1Text_next]; exact stepSp1_isNone_of_syscallHalted h)

/-- The same statement on the unconfined SP1 stepper, for a caller that has not
    established `CodeWithin`. -/
theorem not_accepts_of_reaches_code_none_sp1 {s₀ t : MachineState} {j : Nat}
    (hreach : (Backend.stepper .sp1).iter j s₀ = some t) (hcode : t.code t.pc = none) :
    ∀ k s', (Backend.stepper .sp1).iter k s₀ = some s' → ¬ SyscallHalted s' :=
  not_accepts_of_reaches_stuck hreach
    (by rw [Backend.stepper_next]; exact stepSp1_of_code_none hcode)
    (not_syscallHalted_of_code_none hcode)
    (fun _ h => by rw [Backend.stepper_next]; exact stepSp1_isNone_of_syscallHalted h)

end Decomp
