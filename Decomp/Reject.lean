/-
  Decomp.Reject

  The reject path: showing a region *cannot* accept.

  A soundness statement about a decision-procedure guest is quantified over
  every input, so it owes an argument for the code it does *not* verify
  functionally: those regions cannot reach the accept observation. For a Rust
  guest that is the `core`/`alloc`/`fmt`/panic machinery -- in the project this
  library was extracted from, 14% of the image, 5,857 instructions that need no
  functional proof at all if this argument exists and cannot be dropped for any
  reason if it does not.

  ## What had to change first

  The argument does not go through against `cpsHalt`, whose observation is
  `(st.next s').isNone`. That is true of a real `HALT` *and* of every trap, so
  a state with no code at its pc and `a0 = 0` satisfies it exactly as an
  accepting halt does -- and the cheapest case, the three `unimp` words, would
  then need a proof that `a0 ≠ 0` at them rather than a definitional one.
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

  ## What this does not do

  It discharges the **trapping** half only: an address the loader left
  undecoded. Panic machinery generally does not trap -- it reaches the `HALT`
  syscall with a **nonzero** `a0`, so it *is* `SyscallHalted`, and no argument
  in this file touches it. That case needs `a0 ≠ 0` at those halts, which is a
  proof about values rather than about control, and this library has no
  vocabulary for it yet (ROADMAP, "The halting half of the reject path").

  Nor does it say where a *particular* image has an undecodable word. That is
  the downstream instance's job, and it is a measurement rather than a theorem:
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
theorem not_accepts_of_reaches_stuck {st : Stepper} {s₀ t : MachineState} {j : Nat}
    (hreach : st.iter j s₀ = some t)
    (hstuck : st.next t = none) (hns : ¬ SyscallHalted t)
    (htrap : ∀ u, SyscallHalted u → (st.next u).isNone) :
    ∀ k s', st.iter k s₀ = some s' → ¬ SyscallHalted s' := by
  intro k s' hk hhalt
  rcases Nat.le_total j k with hle | hle
  · -- The run got stuck first, so `s'` is that stuck state.
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    subst hd
    rw [Stepper.iter_add, hreach, Option.bind] at hk
    exact hns (iter_eq_self_of_next_none hstuck hk ▸ hhalt)
  · -- The run accepted first -- but an accepting halt is stuck, so the state
    -- reached later is that same state, and it is not a halt.
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    subst hd
    rw [Stepper.iter_add, hk, Option.bind] at hreach
    have hs'stuck : st.next s' = none := Option.isNone_iff_eq_none.mp (htrap s' hhalt)
    exact hns (iter_eq_self_of_next_none hs'stuck hreach ▸ hhalt)

/-! ## The SP1 instance -/

variable {lo hi : Nat}

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
