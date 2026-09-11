/-
  Decomp.Triple

  The machine-code Hoare triples, over an abstract `Stepper`.

  Two judgements, deliberately:

  * `cpsWithin` carries a step bound, and is kept for leaves and straight-line
    blocks where the bound is free and genuinely informative.
  * `cpsTotal` is Myreen's `∃k` -- total correctness with no bound at all. Use
    it from the point where loops enter.

  Compare Myreen's machine-code triple (UCAM-CL-TR-765), which is the reference
  design for this shape:

      {p} c {q}  =  ∀s r. (p * code c * r) (arm2set s) ⇒
                          ∃k. (q * code c * r) (arm2set (run (k,s)))

  `cpsTotal` is the same judgement up to one choice: code residency is a
  persistent side condition `cr` rather than a consumed separating conjunct
  `code c`. Three systems make three
  different choices there and that `CodeReq` is the pragmatic one.

  ## Why the existential goes inside `∀ s`

  `cpsTotal` is *exactly* `cpsWithin` with the `k ≤ n` conjunct deleted, so
  `cpsTotal_of_cpsWithin` is immediate for every `n`. It is emphatically **not**
  `∃ n, cpsWithin st n …`: that would place the existential outside `∀ s`,
  asserting a bound uniform in the input state, which is strictly stronger than
  Myreen's judgement and false for any loop whose trip count depends on the
  data -- which is most of them. README "Why no fuel" is the argument.

  ## Scope

  Upstream's `Logic/CPSSpec.lean` carries roughly sixty lemmas. Restated here
  are the 26 the decompilation recipe actually consumes. The rest are
  fixed-arity WP frontends (`join2/3/4`, `weakenPosts2/3/4`,
  `takenStripPure2/3`) shaped for a four-way RLP classifier in another project;
  porting them before something needs them would be waste. Add on demand.
-/

module

public import Decomp.Stepper

@[expose] public section

namespace Decomp

open RiscvZkvm.Rv64

variable {st : Stepper}

/-! ## The judgements -/

/-- Step-bounded triple: from `entry`, within `n` steps, reach `exit_` with `Q`.

    The frame rule is baked into the `∀ R, R.pcFree` quantifier rather than
    stated separately, so `cpsTotal_frameR` below is derived, not axiomatic. -/
def cpsWithin (st : Stepper) (n : Nat) (entry exit_ : Word) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ R : Assertion, R.pcFree → ∀ s, st.inv s → cr.SatisfiedBy s → (P ** R).holdsFor s →
    s.pc = entry →
    ∃ k, k ≤ n ∧ ∃ s', st.iter k s = some s' ∧ s'.pc = exit_ ∧ (Q ** R).holdsFor s'

/-- Step-bounded two-exit branch. -/
def cpsBranch (st : Stepper) (n : Nat) (entry : Word) (cr : CodeReq) (P : Assertion)
    (exit_t : Word) (Q_t : Assertion) (exit_f : Word) (Q_f : Assertion) : Prop :=
  ∀ R : Assertion, R.pcFree → ∀ s, st.inv s → cr.SatisfiedBy s → (P ** R).holdsFor s →
    s.pc = entry →
    ∃ k, k ≤ n ∧ ∃ s', st.iter k s = some s' ∧
      ((s'.pc = exit_t ∧ (Q_t ** R).holdsFor s') ∨
       (s'.pc = exit_f ∧ (Q_f ** R).holdsFor s'))

/-- Total-correctness triple: Myreen's `∃k`, with `CodeReq` and the frame
    preserved. No step bound appears anywhere in this statement, which is the
    point. -/
def cpsTotal (st : Stepper) (entry exit_ : Word) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ R : Assertion, R.pcFree → ∀ s, st.inv s → cr.SatisfiedBy s → (P ** R).holdsFor s →
    s.pc = entry →
    ∃ k s', st.iter k s = some s' ∧ s'.pc = exit_ ∧ (Q ** R).holdsFor s'

/-- Total-correctness halt triple: run to a state from which the machine cannot
    step.

    **This does not say the machine halted.** `(st.next s').isNone` is true in
    five distinct situations under `stepSp1` -- no code at the pc, a `.CSRS`, an
    `.EBREAK`, a memory access failing `memOkSp1`, and `sp1Ecall s = none`,
    which is where the real `HALT` lives -- and the postcondition records none
    of them. So a *trap* with `a0 = 0` satisfies this judgement exactly as a
    `HALT` with exit code `0` does, which is why the reject-path argument cannot
    be stated over it (README "Observations"). Use `cpsSyscallHalt` below for
    anything that has to distinguish the two; this one remains the right shape
    for "the machine stops here", and `cpsHalt_of_cpsSyscallHalt` recovers it. -/
def cpsHalt (st : Stepper) (entry : Word) (cr : CodeReq) (P Q : Assertion) : Prop :=
  ∀ R : Assertion, R.pcFree → ∀ s, st.inv s → cr.SatisfiedBy s → (P ** R).holdsFor s →
    s.pc = entry →
    ∃ k s', st.iter k s = some s' ∧ (st.next s').isNone ∧ (Q ** R).holdsFor s'

/-- **Halted, with the reason pinned**: the pc is at an `ECALL` whose syscall id
    is the ABI's `HALT` (`t0 = 0`). This is what SP1's prover actually observes
    -- the public values come out of the halt syscall, and an illegal
    instruction yields no proof rather than a proof with `a0 = 0` -- so it is
    both stronger than `(st.next s).isNone` and closer to the machine.

    It is deliberately a predicate on the *state* rather than on the step
    function: that is what makes it disjoint from a trap, since a state with no
    code at its pc cannot satisfy the first conjunct. -/
def SyscallHalted (s : MachineState) : Prop :=
  s.code s.pc = some .ECALL ∧ s.getReg .x5 = 0

/-- The accept-path judgement: run to a state that is halted *by the halt
    syscall*. `cpsHalt` with the reason pinned, and the shape the top-level
    accepting-run antecedent of a soundness theorem should have. -/
def cpsSyscallHalt (st : Stepper) (entry : Word) (cr : CodeReq) (P Q : Assertion) : Prop :=
  ∀ R : Assertion, R.pcFree → ∀ s, st.inv s → cr.SatisfiedBy s → (P ** R).holdsFor s →
    s.pc = entry →
    ∃ k s', st.iter k s = some s' ∧ SyscallHalted s' ∧ (Q ** R).holdsFor s'

/-! ## Dropping the bound -/

/-- The bounded triple implies the total one, for every bound. This direction is
    the whole reason to keep both, and it is the acceptance criterion recorded
    keeping both. -/
theorem cpsTotal_of_cpsWithin {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} (h : cpsWithin st n entry exit_ cr P Q) :
    cpsTotal st entry exit_ cr P Q := by
  intro R hR s hinv hcr hPR hpc
  obtain ⟨k, _, s', hstep, hpc', hQR⟩ := h R hR s hinv hcr hPR hpc
  exact ⟨k, s', hstep, hpc', hQR⟩

/-- Monotonicity in the step bound. There is no `cpsTotal` analogue, because
    `cpsTotal` has no bound to move. -/
theorem cpsWithin_mono {n n' : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} (hle : n ≤ n') (h : cpsWithin st n entry exit_ cr P Q) :
    cpsWithin st n' entry exit_ cr P Q := by
  intro R hR s hinv hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s hinv hcr hPR hpc
  exact ⟨k, Nat.le_trans hk hle, s', hstep, hpc', hQR⟩

/-! ## Rule of consequence -/

/-- Strengthening the pre and weakening the post, under `**` with any frame. -/
private theorem holdsFor_mono {P P' R : Assertion} {s : MachineState}
    (hmono : ∀ h, P h → P' h) (h : (P ** R).holdsFor s) : (P' ** R).holdsFor s := by
  obtain ⟨hp, hcompat, hpq⟩ := h
  exact ⟨hp, hcompat, sepConj_mono_left hmono hp hpq⟩

theorem cpsWithin_weaken {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P P' Q Q' : Assertion}
    (hpre : ∀ h, P' h → P h) (hpost : ∀ h, Q h → Q' h)
    (h : cpsWithin st n entry exit_ cr P Q) :
    cpsWithin st n entry exit_ cr P' Q' := by
  intro R hR s hinv hcr hP'R hpc
  obtain ⟨k, hk, s', hstep, hpc', hQR⟩ :=
    h R hR s hinv hcr (holdsFor_mono hpre hP'R) hpc
  exact ⟨k, hk, s', hstep, hpc', holdsFor_mono hpost hQR⟩

theorem cpsTotal_weaken {entry exit_ : Word} {cr : CodeReq} {P P' Q Q' : Assertion}
    (hpre : ∀ h, P' h → P h) (hpost : ∀ h, Q h → Q' h)
    (h : cpsTotal st entry exit_ cr P Q) :
    cpsTotal st entry exit_ cr P' Q' := by
  intro R hR s hinv hcr hP'R hpc
  obtain ⟨k, s', hstep, hpc', hQR⟩ :=
    h R hR s hinv hcr (holdsFor_mono hpre hP'R) hpc
  exact ⟨k, s', hstep, hpc', holdsFor_mono hpost hQR⟩

theorem cpsBranch_weaken {n : Nat} {entry : Word} {cr : CodeReq}
    {P P' : Assertion} {exit_t : Word} {Q_t Q_t' : Assertion}
    {exit_f : Word} {Q_f Q_f' : Assertion}
    (hpre : ∀ h, P' h → P h)
    (hpost_t : ∀ h, Q_t h → Q_t' h) (hpost_f : ∀ h, Q_f h → Q_f' h)
    (h : cpsBranch st n entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch st n entry cr P' exit_t Q_t' exit_f Q_f' := by
  intro R hR s hinv hcr hP'R hpc
  obtain ⟨k, hk, s', hstep, hcase⟩ :=
    h R hR s hinv hcr (holdsFor_mono hpre hP'R) hpc
  refine ⟨k, hk, s', hstep, ?_⟩
  rcases hcase with ⟨hpc', hQ⟩ | ⟨hpc', hQ⟩
  · exact Or.inl ⟨hpc', holdsFor_mono hpost_t hQ⟩
  · exact Or.inr ⟨hpc', holdsFor_mono hpost_f hQ⟩

theorem cpsSyscallHalt_weaken {entry : Word} {cr : CodeReq} {P P' Q Q' : Assertion}
    (hpre : ∀ h, P' h → P h) (hpost : ∀ h, Q h → Q' h)
    (h : cpsSyscallHalt st entry cr P Q) :
    cpsSyscallHalt st entry cr P' Q' := by
  intro R hR s hinv hcr hP'R hpc
  obtain ⟨k, s', hstep, hhalt, hQR⟩ := h R hR s hinv hcr (holdsFor_mono hpre hP'R) hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_mono hpost hQR⟩

/-- Nothing is lost by pinning the reason: on a stepper that really does stop at
    a halt syscall -- SP1 does, `Decomp/Sp1/Syscalls.lean`'s `stepSp1_halt` --
    the strong judgement implies the weak one. The hypothesis is a fact about
    the backend, which is why it is not a `Stepper` field: a backend that
    modelled `HALT` as a pc advance would fail it, and should. -/
theorem cpsHalt_of_cpsSyscallHalt {entry : Word} {cr : CodeReq} {P Q : Assertion}
    (htrap : ∀ s, SyscallHalted s → (st.next s).isNone)
    (h : cpsSyscallHalt st entry cr P Q) : cpsHalt st entry cr P Q := by
  intro R hR s hinv hcr hPR hpc
  obtain ⟨k, s', hstep, hhalt, hQR⟩ := h R hR s hinv hcr hPR hpc
  exact ⟨k, s', hstep, htrap s' hhalt, hQR⟩

theorem cpsHalt_weaken {entry : Word} {cr : CodeReq} {P P' Q Q' : Assertion}
    (hpre : ∀ h, P' h → P h) (hpost : ∀ h, Q h → Q' h)
    (h : cpsHalt st entry cr P Q) : cpsHalt st entry cr P' Q' := by
  intro R hR s hinv hcr hP'R hpc
  obtain ⟨k, s', hstep, hhalt, hQR⟩ :=
    h R hR s hinv hcr (holdsFor_mono hpre hP'R) hpc
  exact ⟨k, s', hstep, hhalt, holdsFor_mono hpost hQR⟩

/-! ## Sequential composition -/

/-- Sequencing two total triples. Note there is no bound to add -- which is
    exactly what makes this compose without a human tracking arithmetic. -/
theorem cpsTotal_seq_same_cr {l1 l2 l3 : Word} {cr : CodeReq} {P Q R : Assertion}
    (h1 : cpsTotal st l1 l2 cr P Q) (h2 : cpsTotal st l2 l3 cr Q R) :
    cpsTotal st l1 l3 cr P R := by
  intro F hF s hinv hcr hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hinv hcr hPF hpc
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ :=
    h2 F hF s1 (Stepper.inv_iter hinv hstep1) (Stepper.satisfiedBy_iter hstep1 hcr) hQF hpc1
  exact ⟨k1 + k2, s2, Stepper.iter_add_eq hstep1 hstep2, hpc2, hRF⟩

/-- Sequencing across disjoint code requirements, which then union. -/
theorem cpsTotal_seq {l1 l2 l3 : Word} {cr1 cr2 : CodeReq} {P Q R : Assertion}
    (hd : cr1.Disjoint cr2)
    (h1 : cpsTotal st l1 l2 cr1 P Q) (h2 : cpsTotal st l2 l3 cr2 Q R) :
    cpsTotal st l1 l3 (cr1.union cr2) P R := by
  intro F hF s hinv hcr hPF hpc
  rw [CodeReq.union_satisfiedBy hd] at hcr
  obtain ⟨hcr1, hcr2⟩ := hcr
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hinv hcr1 hPF hpc
  obtain ⟨k2, s2, hstep2, hpc2, hRF⟩ :=
    h2 F hF s1 (Stepper.inv_iter hinv hstep1) (Stepper.satisfiedBy_iter hstep1 hcr2) hQF hpc1
  exact ⟨k1 + k2, s2, Stepper.iter_add_eq hstep1 hstep2, hpc2, hRF⟩

/-- A bounded block followed by a total tail. The common shape: leaves keep
    their bounds, the composite loses it. -/
theorem cpsWithin_seq_cpsTotal_same_cr {n : Nat} {l1 l2 l3 : Word} {cr : CodeReq}
    {P Q R : Assertion}
    (h1 : cpsWithin st n l1 l2 cr P Q) (h2 : cpsTotal st l2 l3 cr Q R) :
    cpsTotal st l1 l3 cr P R :=
  cpsTotal_seq_same_cr (cpsTotal_of_cpsWithin h1) h2

/-- A total triple followed by a halt. -/
theorem cpsTotal_seq_cpsSyscallHalt_same_cr {l1 l2 : Word} {cr : CodeReq}
    {P Q R : Assertion}
    (h1 : cpsTotal st l1 l2 cr P Q) (h2 : cpsSyscallHalt st l2 cr Q R) :
    cpsSyscallHalt st l1 cr P R := by
  intro F hF s hinv hcr hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hinv hcr hPF hpc
  obtain ⟨k2, s2, hstep2, hhalt, hRF⟩ :=
    h2 F hF s1 (Stepper.inv_iter hinv hstep1) (Stepper.satisfiedBy_iter hstep1 hcr) hQF hpc1
  exact ⟨k1 + k2, s2, Stepper.iter_add_eq hstep1 hstep2, hhalt, hRF⟩

theorem cpsTotal_seq_cpsHalt_same_cr {l1 l2 : Word} {cr : CodeReq} {P Q R : Assertion}
    (h1 : cpsTotal st l1 l2 cr P Q) (h2 : cpsHalt st l2 cr Q R) :
    cpsHalt st l1 cr P R := by
  intro F hF s hinv hcr hPF hpc
  obtain ⟨k1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hinv hcr hPF hpc
  obtain ⟨k2, s2, hstep2, hhalt, hRF⟩ :=
    h2 F hF s1 (Stepper.inv_iter hinv hstep1) (Stepper.satisfiedBy_iter hstep1 hcr) hQF hpc1
  exact ⟨k1 + k2, s2, Stepper.iter_add_eq hstep1 hstep2, hhalt, hRF⟩

/-- Sequencing two bounded blocks. Bounds add. -/
theorem cpsWithin_seq_same_cr {n1 n2 : Nat} {l1 l2 l3 : Word} {cr : CodeReq}
    {P Q R : Assertion}
    (h1 : cpsWithin st n1 l1 l2 cr P Q) (h2 : cpsWithin st n2 l2 l3 cr Q R) :
    cpsWithin st (n1 + n2) l1 l3 cr P R := by
  intro F hF s hinv hcr hPF hpc
  obtain ⟨k1, hk1, s1, hstep1, hpc1, hQF⟩ := h1 F hF s hinv hcr hPF hpc
  obtain ⟨k2, hk2, s2, hstep2, hpc2, hRF⟩ :=
    h2 F hF s1 (Stepper.inv_iter hinv hstep1) (Stepper.satisfiedBy_iter hstep1 hcr) hQF hpc1
  exact ⟨k1 + k2, Nat.add_le_add hk1 hk2, s2,
    Stepper.iter_add_eq hstep1 hstep2, hpc2, hRF⟩

/-- Sequencing two bounded blocks across a midpoint permutation. This is the
    shape leaf composition produces -- the first block's post and the second's
    pre are the same atoms in a different order -- and it is on the hot path of
    every framing tactic upstream (`seqFrameWithinCore`). -/
theorem cpsWithin_seq_perm_same_cr {n1 n2 : Nat} {l1 l2 l3 : Word} {cr : CodeReq}
    {P Q1 Q2 R : Assertion}
    (hperm : ∀ h, Q1 h → Q2 h)
    (h1 : cpsWithin st n1 l1 l2 cr P Q1) (h2 : cpsWithin st n2 l2 l3 cr Q2 R) :
    cpsWithin st (n1 + n2) l1 l3 cr P R :=
  cpsWithin_seq_same_cr (cpsWithin_weaken (fun _ hp => hp) hperm h1) h2

/-- Zero-step triple, at any code requirement. -/
theorem cpsWithin_refl {addr : Word} {cr : CodeReq} {P Q : Assertion}
    (h : ∀ hp, P hp → Q hp) : cpsWithin st 0 addr addr cr P Q := by
  intro R _hR s _hinv _hcr hPR hpc
  exact ⟨0, Nat.le_refl 0, s, rfl, hpc, holdsFor_mono h hPR⟩

theorem cpsTotal_refl {addr : Word} {cr : CodeReq} {P Q : Assertion}
    (h : ∀ hp, P hp → Q hp) : cpsTotal st addr addr cr P Q :=
  cpsTotal_of_cpsWithin (cpsWithin_refl h)

/-- An unsatisfiable precondition proves anything. This is how a branch arm the
    abstract state rules out is discharged, rather than by reasoning about code
    that cannot be reached. -/
theorem cpsTotal_of_pre_false {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (hfalse : ∀ hp, P hp → False) : cpsTotal st entry exit_ cr P Q := by
  intro R _hR s _hinv _hcr hPR _hpc
  obtain ⟨_, _, hpq⟩ := hPR
  obtain ⟨h1, _, _, _, hP1, _⟩ := hpq
  exact (hfalse h1 hP1).elim

/-! ## Branching -/

/-- The join rule: a bounded branch whose two arms both continue, by total
    triples, to a common exit. This is what the loop rule is built from. -/
theorem cpsBranch_merge_total_same_cr {n : Nat} {entry l_t l_f exit_ : Word}
    {cr : CodeReq} {P Q_t Q_f R : Assertion}
    (hbr : cpsBranch st n entry cr P l_t Q_t l_f Q_f)
    (h_t : cpsTotal st l_t exit_ cr Q_t R)
    (h_f : cpsTotal st l_f exit_ cr Q_f R) :
    cpsTotal st entry exit_ cr P R := by
  intro F hF s hinv hcr hPF hpc
  obtain ⟨k1, _, s1, hstep1, hcase⟩ := hbr F hF s hinv hcr hPF hpc
  have hcr' := Stepper.satisfiedBy_iter hstep1 hcr
  have hinv' := Stepper.inv_iter hinv hstep1
  rcases hcase with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_t F hF s1 hinv' hcr' hQ_t hpc_t
    exact ⟨k1 + k2, s2, Stepper.iter_add_eq hstep1 hstep2, hpc2, hR⟩
  · obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_f F hF s1 hinv' hcr' hQ_f hpc_f
    exact ⟨k1 + k2, s2, Stepper.iter_add_eq hstep1 hstep2, hpc2, hR⟩

/-! ### The two-exit total judgement

`cpsBranch` with the bound deleted, exactly as `cpsTotal` is `cpsWithin` with
the bound deleted. It is here for the caller who knows a region leaves by one
of two labels but not which -- the loop rule `cpsTotal_loopB_exits` produces a
*single* exit whenever the derivation is in hand, so this is the derived,
weaker form (`cpsTotalBranch_of_loopB`). -/

/-- Total two-exit branch: from `entry`, eventually reach `exit_t` with `Q_t` or
    `exit_f` with `Q_f`. -/
def cpsTotalBranch (st : Stepper) (entry : Word) (cr : CodeReq) (P : Assertion)
    (exit_t : Word) (Q_t : Assertion) (exit_f : Word) (Q_f : Assertion) : Prop :=
  ∀ R : Assertion, R.pcFree → ∀ s, st.inv s → cr.SatisfiedBy s → (P ** R).holdsFor s →
    s.pc = entry →
    ∃ k s', st.iter k s = some s' ∧
      ((s'.pc = exit_t ∧ (Q_t ** R).holdsFor s') ∨
       (s'.pc = exit_f ∧ (Q_f ** R).holdsFor s'))

theorem cpsTotalBranch_of_cpsBranch {n : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (h : cpsBranch st n entry cr P exit_t Q_t exit_f Q_f) :
    cpsTotalBranch st entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hinv hcr hPR hpc
  obtain ⟨k, _, s', hstep, hcase⟩ := h R hR s hinv hcr hPR hpc
  exact ⟨k, s', hstep, hcase⟩

/-- A total triple to the first label is a two-exit judgement whose second arm
    is never taken. -/
theorem cpsTotalBranch_of_cpsTotal_t {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (h : cpsTotal st entry exit_t cr P Q_t) :
    cpsTotalBranch st entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hinv hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQ⟩ := h R hR s hinv hcr hPR hpc
  exact ⟨k, s', hstep, Or.inl ⟨hpc', hQ⟩⟩

theorem cpsTotalBranch_of_cpsTotal_f {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (h : cpsTotal st entry exit_f cr P Q_f) :
    cpsTotalBranch st entry cr P exit_t Q_t exit_f Q_f := by
  intro R hR s hinv hcr hPR hpc
  obtain ⟨k, s', hstep, hpc', hQ⟩ := h R hR s hinv hcr hPR hpc
  exact ⟨k, s', hstep, Or.inr ⟨hpc', hQ⟩⟩

theorem cpsTotalBranch_weaken {entry : Word} {cr : CodeReq}
    {P P' : Assertion} {exit_t : Word} {Q_t Q_t' : Assertion}
    {exit_f : Word} {Q_f Q_f' : Assertion}
    (hpre : ∀ h, P' h → P h)
    (hpost_t : ∀ h, Q_t h → Q_t' h) (hpost_f : ∀ h, Q_f h → Q_f' h)
    (h : cpsTotalBranch st entry cr P exit_t Q_t exit_f Q_f) :
    cpsTotalBranch st entry cr P' exit_t Q_t' exit_f Q_f' := by
  intro R hR s hinv hcr hP'R hpc
  obtain ⟨k, s', hstep, hcase⟩ := h R hR s hinv hcr (holdsFor_mono hpre hP'R) hpc
  refine ⟨k, s', hstep, ?_⟩
  rcases hcase with ⟨hpc', hQ⟩ | ⟨hpc', hQ⟩
  · exact Or.inl ⟨hpc', holdsFor_mono hpost_t hQ⟩
  · exact Or.inr ⟨hpc', holdsFor_mono hpost_f hQ⟩

/-- The join rule for the total two-exit judgement: both arms continue to a
    common exit. -/
theorem cpsTotalBranch_merge_same_cr {entry l_t l_f exit_ : Word}
    {cr : CodeReq} {P Q_t Q_f R : Assertion}
    (hbr : cpsTotalBranch st entry cr P l_t Q_t l_f Q_f)
    (h_t : cpsTotal st l_t exit_ cr Q_t R)
    (h_f : cpsTotal st l_f exit_ cr Q_f R) :
    cpsTotal st entry exit_ cr P R := by
  intro F hF s hinv hcr hPF hpc
  obtain ⟨k1, s1, hstep1, hcase⟩ := hbr F hF s hinv hcr hPF hpc
  have hcr' := Stepper.satisfiedBy_iter hstep1 hcr
  have hinv' := Stepper.inv_iter hinv hstep1
  rcases hcase with ⟨hpc_t, hQ_t⟩ | ⟨hpc_f, hQ_f⟩
  · obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_t F hF s1 hinv' hcr' hQ_t hpc_t
    exact ⟨k1 + k2, s2, Stepper.iter_add_eq hstep1 hstep2, hpc2, hR⟩
  · obtain ⟨k2, s2, hstep2, hpc2, hR⟩ := h_f F hF s1 hinv' hcr' hQ_f hpc_f
    exact ⟨k1 + k2, s2, Stepper.iter_add_eq hstep1 hstep2, hpc2, hR⟩

/-! ## Reading a branch leaf's post through a left frame

A branch leaf reports the guard it took as a pure conjunct at the end of its
postcondition, `(rs1 ↦ᵣ v1) ** (rs2 ↦ᵣ v2) ** ⌜v1 = v2⌝`. Framing on the left
-- which is what a caller does when the branch's two registers sit at the end
of the block's footprint -- puts that conjunct three levels in. These two say
"give me the guard" and "drop it again", so the obligations at a `cpsBranch`
read as control flow rather than as separation-logic bookkeeping. -/

/-- Extract a framed branch leaf's guard from its postcondition. -/
theorem pure_of_branch_post {A B C : Assertion} {p : Prop} {h : PartialState}
    (hq : (A ** (B ** (C ** ⌜p⌝))) h) : p := by
  obtain ⟨_, h2, _, _, _, hBC⟩ := hq
  obtain ⟨_, h4, _, _, _, hC⟩ := hBC
  exact ((sepConj_pure_right h4).mp hC).2

/-- Drop a framed branch leaf's guard again, once it has been read. -/
theorem drop_branch_pure {A B C : Assertion} {p : Prop} :
    ∀ h, (A ** (B ** (C ** ⌜p⌝))) h → (A ** (B ** C)) h :=
  fun h hq =>
    sepConj_mono_right
      (fun h' hq' =>
        sepConj_mono_right
          (fun h'' hq'' => ((sepConj_pure_right h'').mp hq'').1) h' hq')
      h hq

/-- When one arm's postcondition is unsatisfiable, the branch is really a
    triple along the other arm. Upstream's `cpsBranchWithin_takenPath` idiom. -/
theorem cpsBranch_takenPath {n : Nat} {entry l_t l_f : Word} {cr : CodeReq}
    {P Q_t Q_f : Assertion}
    (hfalse : ∀ hp, Q_f hp → False)
    (hbr : cpsBranch st n entry cr P l_t Q_t l_f Q_f) :
    cpsWithin st n entry l_t cr P Q_t := by
  intro R hR s hinv hcr hPR hpc
  obtain ⟨k, hk, s', hstep, hcase⟩ := hbr R hR s hinv hcr hPR hpc
  rcases hcase with ⟨hpc', hQ⟩ | ⟨_, hQ⟩
  · exact ⟨k, hk, s', hstep, hpc', hQ⟩
  · obtain ⟨_, _, h1, _, _, _, hQ1, _⟩ := hQ
    exact (hfalse h1 hQ1).elim

theorem cpsBranch_notTakenPath {n : Nat} {entry l_t l_f : Word} {cr : CodeReq}
    {P Q_t Q_f : Assertion}
    (hfalse : ∀ hp, Q_t hp → False)
    (hbr : cpsBranch st n entry cr P l_t Q_t l_f Q_f) :
    cpsWithin st n entry l_f cr P Q_f :=
  cpsBranch_takenPath hfalse (by
    intro R hR s hinv hcr hPR hpc
    obtain ⟨k, hk, s', hstep, hcase⟩ := hbr R hR s hinv hcr hPR hpc
    exact ⟨k, hk, s', hstep, hcase.symm⟩)

/-! ## Framing

The frame is already quantified in every judgement, so these are theorems about
that quantifier rather than new rules. -/

/-- Frame on the right of a bounded block. The bound is unchanged. This and
    `cpsWithin_seq_perm_same_cr` are what every leaf-composition step reaches
    for -- upstream's `frameFirstSpecWithin` builds on exactly this rule. -/
theorem cpsWithin_frameR {n : Nat} {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (F : Assertion) (hF : F.pcFree) (h : cpsWithin st n entry exit_ cr P Q) :
    cpsWithin st n entry exit_ cr (P ** F) (Q ** F) := by
  intro R hR s hinv hcr hPFR hpc
  obtain ⟨k, hk, s', hstep, hpc', hpost⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hinv hcr (holdsFor_sepConj_assoc.mp hPFR) hpc
  exact ⟨k, hk, s', hstep, hpc', holdsFor_sepConj_assoc.mpr hpost⟩

theorem cpsWithin_frameL {n : Nat} {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (F : Assertion) (hF : F.pcFree) (h : cpsWithin st n entry exit_ cr P Q) :
    cpsWithin st n entry exit_ cr (F ** P) (F ** Q) := by
  intro R hR s hinv hcr hFPR hpc
  obtain ⟨k, hk, s', hstep, hpc', hpost⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hinv hcr
      (holdsFor_sepConj_pull_second.mp hFPR) hpc
  exact ⟨k, hk, s', hstep, hpc', holdsFor_sepConj_pull_second.mpr hpost⟩

theorem cpsTotal_frameR {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (F : Assertion) (hF : F.pcFree) (h : cpsTotal st entry exit_ cr P Q) :
    cpsTotal st entry exit_ cr (P ** F) (Q ** F) := by
  intro R hR s hinv hcr hPFR hpc
  obtain ⟨k, s', hstep, hpc', hpost⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hinv hcr (holdsFor_sepConj_assoc.mp hPFR) hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_assoc.mpr hpost⟩

theorem cpsTotal_frameL {entry exit_ : Word} {cr : CodeReq} {P Q : Assertion}
    (F : Assertion) (hF : F.pcFree) (h : cpsTotal st entry exit_ cr P Q) :
    cpsTotal st entry exit_ cr (F ** P) (F ** Q) := by
  intro R hR s hinv hcr hFPR hpc
  obtain ⟨k, s', hstep, hpc', hpost⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hinv hcr
      (holdsFor_sepConj_pull_second.mp hFPR) hpc
  exact ⟨k, s', hstep, hpc', holdsFor_sepConj_pull_second.mpr hpost⟩

theorem cpsBranch_frameR {n : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (F : Assertion) (hF : F.pcFree)
    (h : cpsBranch st n entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch st n entry cr (P ** F) exit_t (Q_t ** F) exit_f (Q_f ** F) := by
  intro R hR s hinv hcr hPFR hpc
  obtain ⟨k, hk, s', hstep, hcase⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hinv hcr (holdsFor_sepConj_assoc.mp hPFR) hpc
  exact ⟨k, hk, s', hstep, hcase.elim
    (fun hc => Or.inl ⟨hc.1, holdsFor_sepConj_assoc.mpr hc.2⟩)
    (fun hc => Or.inr ⟨hc.1, holdsFor_sepConj_assoc.mpr hc.2⟩)⟩

/-- The mirror of `cpsBranch_frameR`, added for a loop whose coupling puts the
    a real loop header's branch leaf owns the counter, and the pointer and the
    memory region sit to its *left* in the coupling. Without this the coupling
    would have to be permuted at every header step. -/
theorem cpsBranch_frameL {n : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (F : Assertion) (hF : F.pcFree)
    (h : cpsBranch st n entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch st n entry cr (F ** P) exit_t (F ** Q_t) exit_f (F ** Q_f) := by
  intro R hR s hinv hcr hFPR hpc
  obtain ⟨k, hk, s', hstep, hcase⟩ :=
    h (F ** R) (pcFree_sepConj hF hR) s hinv hcr
      (holdsFor_sepConj_pull_second.mp hFPR) hpc
  exact ⟨k, hk, s', hstep, hcase.elim
    (fun hc => Or.inl ⟨hc.1, holdsFor_sepConj_pull_second.mpr hc.2⟩)
    (fun hc => Or.inr ⟨hc.1, holdsFor_sepConj_pull_second.mpr hc.2⟩)⟩

/-! ## Growing the code requirement

This is the lift from a per-function `CodeReq.ofProg` to the whole image.
`CodeReq.ofProg_sub_ofEntries_of_extentsOk` produces a `hmono` of exactly this
shape, and an image's `entries_ok` discharges its hypothesis by `decide`. -/

theorem cpsTotal_extend_code {entry exit_ : Word} {cr cr' : CodeReq} {P Q : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsTotal st entry exit_ cr P Q) :
    cpsTotal st entry exit_ cr' P Q := fun R hR s hinv hcr' hPR hpc =>
  h R hR s hinv (CodeReq.SatisfiedBy_mono hmono hcr') hPR hpc

theorem cpsWithin_extend_code {n : Nat} {entry exit_ : Word} {cr cr' : CodeReq}
    {P Q : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsWithin st n entry exit_ cr P Q) :
    cpsWithin st n entry exit_ cr' P Q := fun R hR s hinv hcr' hPR hpc =>
  h R hR s hinv (CodeReq.SatisfiedBy_mono hmono hcr') hPR hpc

theorem cpsBranch_extend_code {n : Nat} {entry : Word} {cr cr' : CodeReq}
    {P : Assertion} {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsBranch st n entry cr P exit_t Q_t exit_f Q_f) :
    cpsBranch st n entry cr' P exit_t Q_t exit_f Q_f := fun R hR s hinv hcr' hPR hpc =>
  h R hR s hinv (CodeReq.SatisfiedBy_mono hmono hcr') hPR hpc

theorem cpsHalt_extend_code {entry : Word} {cr cr' : CodeReq} {P Q : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsHalt st entry cr P Q) :
    cpsHalt st entry cr' P Q := fun R hR s hinv hcr' hPR hpc =>
  h R hR s hinv (CodeReq.SatisfiedBy_mono hmono hcr') hPR hpc

theorem cpsSyscallHalt_extend_code {entry : Word} {cr cr' : CodeReq} {P Q : Assertion}
    (hmono : ∀ a i, cr a = some i → cr' a = some i)
    (h : cpsSyscallHalt st entry cr P Q) :
    cpsSyscallHalt st entry cr' P Q := fun R hR s hinv hcr' hPR hpc =>
  h R hR s hinv (CodeReq.SatisfiedBy_mono hmono hcr') hPR hpc

/-! ## The `Backend`-indexed instances

Thin abbreviations for this project's own use. The theory above is stated over
`Stepper`, so a third backend needs no addition here -- it supplies its own
`Stepper` and gets every rule.

**Footgun.** `Backend.stepper .sp1` has `inv := True`, so a `cpsWithinOn .sp1`
triple ranges over states with arbitrary code at any address -- and on those
`stepSp1` traps at every store (`memOkSp1`'s `noCodeAt`). A block containing a
store, stated as `cpsWithinOn .sp1`, is therefore a *false* theorem, not a
vacuous one. State SP1 triples about code that stores on
`Decomp.Sp1Text` (`Decomp/Leaf/Sp1Text.lean`) and use `cpsWithinOn .sp1` as a
lifting source (`cpsWithin_sp1Text_of_sp1`), never as the target. -/

/-- Step-bounded triple under a named backend. -/
abbrev cpsWithinOn (b : Backend) (n : Nat) (entry exit_ : Word) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  cpsWithin (Backend.stepper b) n entry exit_ cr P Q

/-- Total-correctness triple under a named backend. -/
abbrev cpsTotalOn (b : Backend) (entry exit_ : Word) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  cpsTotal (Backend.stepper b) entry exit_ cr P Q

/-- Step-bounded branch under a named backend. -/
abbrev cpsBranchOn (b : Backend) (n : Nat) (entry : Word) (cr : CodeReq) (P : Assertion)
    (exit_t : Word) (Q_t : Assertion) (exit_f : Word) (Q_f : Assertion) : Prop :=
  cpsBranch (Backend.stepper b) n entry cr P exit_t Q_t exit_f Q_f

/-- Total-correctness halt triple under a named backend. -/
abbrev cpsHaltOn (b : Backend) (entry : Word) (cr : CodeReq) (P Q : Assertion) : Prop :=
  cpsHalt (Backend.stepper b) entry cr P Q

/-! ### Agreement with the ZisK-only judgement upstream

`RiscvZkvm.Rv64.Logic.cpsTripleWithin` is stated over `stepN`, i.e. over
`stepOn .zisk`. These say the `.zisk` instance of `cpsWithin` is that same
judgement, so no existing proof is invalidated -- and, read the other way, that
`cpsWithinOn .sp1` is a genuinely different statement, which is the whole
reason this file exists. -/

theorem cpsWithinOn_zisk_iff {n : Nat} {entry exit_ : Word} {cr : CodeReq}
    {P Q : Assertion} :
    cpsWithinOn .zisk n entry exit_ cr P Q ↔ cpsTripleWithin n entry exit_ cr P Q := by
  constructor
  · intro h R hR s hcr hPR hpc
    obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s trivial hcr hPR hpc
    exact ⟨k, hk, s', (Backend.stepper_iter_zisk k s).symm.trans hstep, hpc', hQR⟩
  · intro h R hR s _hinv hcr hPR hpc
    obtain ⟨k, hk, s', hstep, hpc', hQR⟩ := h R hR s hcr hPR hpc
    exact ⟨k, hk, s', (Backend.stepper_iter_zisk k s).trans hstep, hpc', hQR⟩

/-- The branch judgement agrees with upstream's on ZisK, both ways. Every
    upstream branch leaf (`generic_beq_spec_within` and friends) enters the
    `Stepper`-generic world through `.mpr`. -/
theorem cpsBranchOn_zisk_iff {n : Nat} {entry : Word} {cr : CodeReq} {P : Assertion}
    {exit_t : Word} {Q_t : Assertion} {exit_f : Word} {Q_f : Assertion} :
    cpsBranchOn .zisk n entry cr P exit_t Q_t exit_f Q_f ↔
      cpsBranchWithin n entry cr P exit_t Q_t exit_f Q_f := by
  constructor
  · intro h R hR s hcr hPR hpc
    obtain ⟨k, hk, s', hstep, hcase⟩ := h R hR s trivial hcr hPR hpc
    exact ⟨k, hk, s', (Backend.stepper_iter_zisk k s).symm.trans hstep, hcase⟩
  · intro h R hR s _hinv hcr hPR hpc
    obtain ⟨k, hk, s', hstep, hcase⟩ := h R hR s hcr hPR hpc
    exact ⟨k, hk, s', (Backend.stepper_iter_zisk k s).trans hstep, hcase⟩

/-- Every existing upstream triple lifts to a total one on the ZisK backend, so
    nothing already proved is stranded by the move to `∃k`. -/
theorem cpsTotalOn_zisk_of_cpsTripleWithin {n : Nat} {entry exit_ : Word}
    {cr : CodeReq} {P Q : Assertion} (h : cpsTripleWithin n entry exit_ cr P Q) :
    cpsTotalOn .zisk entry exit_ cr P Q :=
  cpsTotal_of_cpsWithin (cpsWithinOn_zisk_iff.mpr h)

/-- Upstream's halt triple lifts to the ZisK instance of `cpsHalt`.

    One direction only, like `cpsTotalOn_zisk_of_cpsTripleWithin`: upstream's
    `cpsHaltTripleWithin` carries a step bound and `cpsHalt` does not. Note that
    upstream's halt condition `isHalted s' = (step s').isNone` is hard-wired to
    ZisK -- under SP1, `stepSp1` traps on an unmodelled ecall where `step`
    silently advances the pc, so the two predicates genuinely disagree there.
    `cpsHalt` uses `st.next`, which is why it is the right shape for the accept
    path and this bridge is stated at `.zisk` only. -/
theorem cpsHaltOn_zisk_of_cpsHaltTripleWithin {n : Nat} {entry : Word}
    {cr : CodeReq} {P Q : Assertion} (h : cpsHaltTripleWithin n entry cr P Q) :
    cpsHaltOn .zisk entry cr P Q := by
  intro R hR s _hinv hcr hPR hpc
  obtain ⟨k, _, s', hstep, hhalt, hQR⟩ := h R hR s hcr hPR hpc
  refine ⟨k, s', (Backend.stepper_iter_zisk k s).trans hstep, ?_, hQR⟩
  simpa [isHalted, Backend.stepper_next, stepOn_zisk] using hhalt

end Decomp
