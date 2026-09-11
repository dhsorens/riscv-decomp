/-
  Decomp.Examples.Countdown

  The abstract half of a decompiled loop, on a real backward-branch program.

  `RiscvZkvm.Rv64.Logic.ControlFlow` carries `countdown_loop`:

      BEQ  x10, x0, +12   -- header: leave when the counter is zero
      ADDI x10, x10, -1   -- body
      JAL  x0,  -8        -- back to the header

  and exercises it only with `decide` on three concrete initial values
  (`x10 = 0`, `1`, `3`). That is the shape of the gap this library closes: the
  bounded rule cannot state a triple for *arbitrary* `x10`, because
  `loopNatCert`'s `fuel` -- and hence `loopBound`, the step budget the resulting
  triple carries -- must be a literal at proof-construction time, and the trip
  count here is the input.

  This file decompiles that loop's abstract half: the `Rec`, its termination,
  and its extracted function. Everything below is machine-free, and it is what
  a downstream correctness proof does its induction over.

  ## The machine-level half

  Lives in `Decomp/Examples/CountdownMachine.lean`, which discharges
  `cpsTotal_loop`'s three hypotheses from upstream's own leaf specs, transferred
  to any backend that agrees with ZisK on plain instructions, and packages the
  result as a `Cert`. `countdown_total` there is the end-to-end statement, on
  ZisK and SP1 from one proof. This file stays machine-free on purpose: it is what a
  downstream correctness proof does its induction over, and nothing in it
  should have to know there is a machine.
-/

import Decomp.Certificate

namespace Decomp.Examples.Countdown

/-- The abstract state is the counter, as a `Nat`. Coupling it to the machine
    is `fun n => .x10 ↦ᵣ BitVec.ofNat 64 n`, which is why `side` below is a
    no-wraparound bound rather than `True`. -/
def countdown : Rec Nat Nat where
  guard n := n != 0
  step n := n - 1
  out n := n

/-- The per-iteration side condition: the counter is representable, so the
    machine's `ADDI x10, x10, -1` really is the abstract `n - 1` and not a
    wraparound.

    This is TR-765's returned `cond` in miniature -- a genuine domain fact that
    a verification using the extracted function has to discharge, not a
    bookkeeping artefact. -/
def side (n : Nat) : Prop := n < 2 ^ 64

/-- The loop terminates from any representable counter, after exactly `n`
    iterations. Ordinary `Nat` induction -- no variant invented, and the trip
    count is the index rather than a supplied bound. -/
theorem terminatesIn : ∀ n : Nat, side n → TerminatesIn countdown side n n := by
  intro n
  induction n with
  | zero => intro _; exact .exit (by decide)
  | succ n ih =>
    intro hs
    exact .iter (by simp [countdown]) hs (ih (by simp only [side] at hs ⊢; omega))

theorem terminates {n : Nat} (h : side n) : Terminates countdown side n :=
  ⟨n, terminatesIn n h⟩

/-- The extracted function: the loop counts down to zero. This is the
    `heq` obligation `Decomp.Cert.ofLoop` asks for -- "prove the extracted
    tail-recursive function equals something you would rather reason with" --
    and it is four lines of ordinary induction. -/
theorem runN_eq_zero : ∀ n : Nat, countdown.runN n n = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [Rec.runN_succ_of_guard (by simp [countdown])]; exact ih

/-- Wherever the loop exits, it exits at zero. -/
theorem iterate_eq_zero :
    ∀ n x, TerminatesIn countdown side n x → countdown.iterate n x = 0 := by
  intro n x h
  induction h with
  | exit hx => simpa [countdown] using hx
  | iter _ _ _ ih => simpa using ih

/-- The form `Cert.ofLoop` consumes: the extracted function is the constant `0`
    on every state the loop is known to exit from. -/
theorem runN_eq_const :
    ∀ n x, TerminatesIn countdown side n x → countdown.runN n x = 0 := by
  intro n x h
  rw [h.runN_eq, iterate_eq_zero n x h]
  rfl

/-! ## The trip count is not a choice

`TerminatesIn.unique` says the index is determined by the loop, and
`TerminatesIn.runN_stable` says the extracted function does not depend on it.
Together they are why quoting `runN n` in `cpsTotal_loop`'s conclusion costs no
generality -- and why nothing here plays the role `loopNatCert`'s `fuel` does. -/

example {n m : Nat} (hn : TerminatesIn countdown side n 7)
    (hm : TerminatesIn countdown side m 7) : n = m := hn.unique hm

example {m : Nat} (hle : 7 ≤ m) : countdown.runN m 7 = countdown.runN 7 7 :=
  (terminatesIn 7 (by simp [side])).runN_stable hle

/-! ## Build-time checks

`#guard` evaluates and produces no proof term, so unlike `native_decide` it adds
nothing to the axiom base. These pin the extracted function against upstream's
own three `decide` cases. -/

-- `x10 = 0`: the header exits immediately.
#guard countdown.guard 0 == false
#guard countdown.runN 0 0 == 0

-- `x10 = 1` and `x10 = 3`: upstream's other two cases.
#guard countdown.runN 1 1 == 0
#guard countdown.runN 3 3 == 0

-- Above the exit point the answer is stable, and the intermediate states are
-- the counter running down.
#guard countdown.runN 99 3 == 0
#guard (List.range 4).map (countdown.iterate · 3) == [3, 2, 1, 0]

end Decomp.Examples.Countdown
