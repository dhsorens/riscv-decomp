/-
  Decomp.Examples.CountdownThenFind

  Two regions, one certificate, one composite spec: the consumer for
  `Cert.Refines.seq` and, through it, for `Nres.bind_refine`.

  The program is `Countdown` followed immediately by `FindIndex`:

      base+0  .. base+8    countdown x10 to zero          (Countdown.prog)
      base+12 .. base+24   search from x10 for x11 in [x10, x12)   (FindIndex.prog)
      base+28              join

  Each half already has its L2 certificate and its L3 refinement, proved in
  its own file against its own code requirement and its own coupling. This
  file does only the gluing, and the point is how little that is:

  * `Cert.extendCode` lifts each certificate to the combined program's
    `CodeReq`, with upstream's `ofProg_mono_append_left/right`.
  * `Cert.frameR` gives each the other's registers: the countdown carries the
    search's parameters untouched, the search carries `x0`.
  * `Cert.seq` joins them at `base + 12`, with one `ac_rfl` for the coupling.
  * `Cert.Refines.seq` composes the two refinements into a refinement of
    `pipelineSpec`, which is `bind countSpec searchSpec` -- and that is where
    `bind_refine` gets its first consumer, and where `Cert.seq`'s side
    condition `c₁.pre x ∧ c₂.pre (c₁.fn x)` is seen to be exactly what `bind`
    asks of the continuation.

  `pipelineSpec_ok_iff` (abstract correctness, on the `DecompRefine` side) and
  `cert_refines` (refinement) stay two theorems, and `pipeline_meets_spec`
  composes them with the machine.
-/

module

public import Decomp.Refine
public import Decomp.Examples.CountdownMachine
public import Decomp.Examples.FindIndexRefine
public import DecompRefine.Examples.Search

@[expose] public section

namespace Decomp.Examples.Pipeline

open RiscvZkvm.Rv64 DecompRefine DecompRefine.Examples.Search

variable {st : Stepper}

/-- The two programs, back to back. -/
def prog : Program := Countdown.prog ++ FindIndex.prog

def cr (base : Word) : CodeReq := CodeReq.ofProg base prog

/-- The search's parameters: what the countdown carries untouched. -/
abbrev F (stop e : Nat) : Assertion :=
  (.x11 ↦ᵣ BitVec.ofNat 64 stop) ** (.x12 ↦ᵣ BitVec.ofNat 64 e)

/-- The countdown, on the combined code, carrying the search's parameters. -/
def c₁ (hst : st.PlainAgree) (base : Word) (stop e : Nat) : Cert st Nat Nat :=
  ((Countdown.cert hst base).extendCode
    (CodeReq.ofProg_mono_append_left base Countdown.prog FindIndex.prog)).frameR
    (F stop e) (by pcFree)

/-- The search, at `base + 12`, on the combined code, carrying `x0`. -/
def c₂ (hst : st.PlainAgree) (base : Word) {stop e : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) : Cert st Nat FindIndex.Res :=
  ((FindIndex.cert hst (base + BitVec.ofNat 64 (4 * Countdown.prog.length)) hstop he).extendCode
    (CodeReq.ofProg_mono_append_right base Countdown.prog FindIndex.prog (by decide))).frameR
    (.x0 ↦ᵣ (0 : Word)) pcFree_regIs

/-- The two couplings are the same four atoms. -/
theorem link (stop e y : Nat) :
    (Countdown.I y ** F stop e) = (FindIndex.I stop e y ** (.x0 ↦ᵣ (0 : Word))) := by
  simp only [Countdown.I, FindIndex.I, F]; ac_rfl

/-- **The two-region certificate.** Entry `base`, exit `base + 28`, side
    condition `Terminates countdown side n ∧ TerminatesB (find stop e) side 0`
    -- `Cert.seq`'s propagation rule, with the countdown's output `0` fed to
    the search's precondition. -/
def cert (hst : st.PlainAgree) (base : Word) {stop e : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) : Cert st Nat FindIndex.Res :=
  (c₁ hst base stop e).seq (c₂ hst base hstop he) rfl rfl
    (fun y hp h => by
      show (FindIndex.I stop e y ** (.x0 ↦ᵣ (0 : Word))) hp
      rw [← link]; exact h)

/-- What the certificate says about itself: the composite function is the
    search from `0`, and the side condition is the conjunction. -/
example (hst : st.PlainAgree) (base : Word) {stop e : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    (cert hst base hstop he).fn = fun _ => FindIndex.result stop e 0 := rfl
example (hst : st.PlainAgree) (base : Word) {stop e : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    (cert hst base hstop he).pre =
      fun n => Terminates Countdown.countdown Countdown.side n ∧
        TerminatesB (FindIndex.find stop e) FindIndex.side 0 := rfl

/-! ## Refinement, composed -/

/-- The countdown refines `countSpec`: its extracted function is the constant
    `0`, and the spec accepts exactly `0` on its domain. -/
theorem c₁_refines (hst : st.PlainAgree) (base : Word) (stop e : Nat) :
    (c₁ hst base stop e).Refines countSpec Eq := by
  intro n _
  show Nres.ret 0 ≤ Nres.assert (n < 2 ^ 64) (Nres.conc Eq (Nres.ret 0))
  exact Nres.le_assert_of_pre fun _ => Nres.ret_le_conc rfl rfl

/-- **`Cert.seq` refines `bind`.** The composite certificate refines the
    composite spec, from the two halves' own refinement theorems and nothing
    else. -/
theorem cert_refines (hst : st.PlainAgree) (base : Word) {stop e : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    (cert hst base hstop he).Refines (fun n => pipelineSpec n stop e) FindIndex.R :=
  Cert.Refines.seq (c₁_refines hst base stop e)
    (fun y z hyz _ => by subst hyz; exact FindIndex.result_refines stop e y)

/-- The search from `0` terminates on a non-empty range: it finds `stop` if
    `stop < e` and runs out otherwise. -/
theorem find_terminates_zero {stop e : Nat} (he : e < 2 ^ 64) (he0 : 0 < e) :
    TerminatesB (FindIndex.find stop e) FindIndex.side 0 := by
  by_cases hse : stop < e
  · exact ⟨_, _, FindIndex.runsTo_found hse he stop 0 (by omega)⟩
  · exact ⟨_, _, FindIndex.runsTo_exhausted he (e - 1) 0 (by omega)
      (fun j _ hje hjs => hse (hjs ▸ hje))⟩

/-- **L2 meets L3, across two regions.** From any representable counter and
    any non-empty range, on either backend, the machine runs the countdown and
    the search and ends at the join in a state some acceptable answer of the
    composite spec describes. Neither `result` nor the constant `0` appears. -/
theorem pipeline_meets_spec (b : Backend) (base : Word) {n stop e : Nat}
    (hn : n < 2 ^ 64) (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) (he0 : 0 < e) :
    cpsTotalOn b base (base + 12 + 16) (cr base)
      (Countdown.I n ** F stop e)
      (specPost (fun r => FindIndex.Q stop e r ** (.x0 ↦ᵣ (0 : Word))) FindIndex.R
        (pipelineSpec n stop e)) :=
  (cert (Backend.plainAgree b) base hstop he).refines_sound
    (cert_refines (Backend.plainAgree b) base hstop he) n
    ⟨Countdown.terminates hn, find_terminates_zero he he0⟩
    (pipelineSpec_not_fails hn he0)

/-! ## Against the nondeterministic spec

Same certificate, same second-stage refinement, a looser first-stage spec:
`countSpecLe` accepts any value at or below the start, so `pipelineSpecLe`
admits several answers (`pipelineSpecLe_two_answers`) and the machine's one
run is related to one of them. Nothing about the certificate changes; only
`c₁`'s refinement theorem is restated against the larger set. -/

/-- The countdown refines the loose spec too: `0 ≤ n`. -/
theorem c₁_refines_le (hst : st.PlainAgree) (base : Word) (stop e : Nat) :
    (c₁ hst base stop e).Refines countSpecLe Eq := by
  intro n _
  show Nres.ret 0 ≤ Nres.assert (n < 2 ^ 64) (Nres.conc Eq (Nres.spec (· ≤ n)))
  exact Nres.le_assert_of_pre fun _ => Nres.ret_le_conc (Nat.zero_le n) rfl

theorem cert_refines_le (hst : st.PlainAgree) (base : Word) {stop e : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    (cert hst base hstop he).Refines (fun n => pipelineSpecLe n stop e) FindIndex.R :=
  Cert.Refines.seq (c₁_refines_le hst base stop e)
    (fun y z hyz _ => by subst hyz; exact FindIndex.result_refines stop e y)

/-- The end-to-end statement against the nondeterministic spec. The domain
    condition is now `n < e`: every start the spec allows must lie below the
    end of the range. -/
theorem pipeline_meets_specLe (b : Backend) (base : Word) {n stop e : Nat}
    (hn : n < 2 ^ 64) (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) (hne : n < e) :
    cpsTotalOn b base (base + 12 + 16) (cr base)
      (Countdown.I n ** F stop e)
      (specPost (fun r => FindIndex.Q stop e r ** (.x0 ↦ᵣ (0 : Word))) FindIndex.R
        (pipelineSpecLe n stop e)) :=
  (cert (Backend.plainAgree b) base hstop he).refines_sound
    (cert_refines_le (Backend.plainAgree b) base hstop he) n
    ⟨Countdown.terminates hn, find_terminates_zero he (by omega)⟩
    (pipelineSpecLe_not_fails hn hne)

end Decomp.Examples.Pipeline
