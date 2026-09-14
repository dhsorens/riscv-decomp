/-
  Decomp.Extract.Cert

  The extractor's third step (M2): the certificate for an emitted body.

  `Decomp/Extract/Body.lean` emits, for one loop, a total function
  `body : RegFile → RegFile ⊕ Exit`. This file proves it correct against the
  machine -- once, for every loop the emitter accepts -- so that the L2
  statement for an extracted loop is a *corollary* (`emitBody_sound`) rather
  than something to be proved per loop:

      RunsTo body (fun _ => True) n x y  ⟹
      cpsTotal st header y.label cr (regsAssn rs x) (regsAssn rs y.regs)

  The coupling `regsAssn rs r` is the separating conjunction of `x ↦ᵣ r.get x`
  over a list `rs` of registers that covers the loop's footprint. The side
  condition is `True`: a register file is an exact abstraction of the
  registers, so there is nothing to ask of the abstract state -- the
  representability facts the hand proofs carried (`i + 1 < 2 ^ 64`) were the
  price of abstracting to `Nat`, and an extracted certificate does not pay it.

  ## How it is built

  Two generic leaves, proved directly from the stepper's semantics rather than
  transferred from upstream's per-instruction specs:

  * `cpsWithin_alu`: an in-scope ALU instruction, on any `PlainAgree` stepper,
    takes `regsAssn rs r` to `regsAssn rs r'` where `execPlain` says
    `r' = r.set rd v`. The proof is `execInstrBr_alu` (the machine does the
    write `aluOf` names) plus upstream's frame-preserving register update
    `holdsFor_sepConj_regIs_setReg`, after the destination atom is pulled to
    the front of the conjunction (`holdsFor_regsAssn_setReg`).
  * `cpsWithin_terminal`: a branch or `JAL x0` leaves the registers alone and
    lands where `nextPc` says (`execInstrBr_terminal`).

  Then the walk `runPass` is followed by induction on the loop's block list
  (`runPass_sound`), each block by induction on its instructions
  (`stepBlock_sound`), and the exit-label resolution through pure-jump blocks
  by induction on its fuel (`resolveJumps_sound`). The fallback in `runPass`
  -- `inr` at the current pc -- turns out to be *sound*, not merely
  unreachable: it claims control is at `pc` with the registers unchanged,
  which is true in zero steps. So nothing here uses `wellFormed`:
  `runPass_sound` is stated over the raw walk without it, and `emitBody_sound`
  reaches it only through `emitBody`'s own check, whose result the proof never
  looks at. `wellFormed` is what makes the emitted body *useful* -- its exits
  are outside the loop -- not what makes it correct.

  ## What the theorem asks of the caller

  Two facts about the program, both `Bool`s and both checked by `decide` on
  the examples at the bottom: `passOk` (every block of the loop is resident in
  `cr` and names only registers in `rs`) and `jumpsOk` (every pure-jump block
  is resident and jumps where its successor says). A `Nodup rs`. Nothing about
  the shape of the loop.

  ## What it does not do

  It does not relate the extracted body to a hand-written one, so it does not
  yet *reproduce* `FindIndexMachine.lean`'s certificate (M3); it states a new
  one over the register file. It does not package the result as a `Cert`,
  because `Cert.exit_` is one label and an extracted loop's exit is
  `Exit.label`, a function of the output (`ROADMAP.md` item 7 noted a
  `Cert` with `exit_ : β → Word` had no consumer; now one is waiting). And the
  two program facts are hypotheses discharged by `decide` at a concrete base,
  not lemmas about `blocks`; a lemma that `blocks base prog` always satisfies
  them against `CodeReq.ofProg base prog` is the piece that would make the
  result base-generic.
-/

module

public import Decomp.Extract.Body
public import Decomp.Loop
public import Decomp.Leaf.Core
public import Decomp.Leaf.Sp1Step
-- The checks at the bottom evaluate the emission on the two example programs.

@[expose] public section

namespace Decomp.Extract

open RiscvZkvm.Rv64

/-! ## The coupling -/

/-- The registers in `rs`, at the values `r` gives them. -/
def regsAssn : List Reg → RegFile → Assertion
  | [], _ => empAssertion
  | x :: xs, r => (x ↦ᵣ r.get x) ** regsAssn xs r

theorem regsAssn_pcFree (rs : List Reg) (r : RegFile) : (regsAssn rs r).pcFree := by
  induction rs with
  | nil => exact pcFree_emp
  | cons x xs ih => exact pcFree_sepConj pcFree_regIs ih

/-- The coupling sees the register file only through the registers it names. -/
theorem regsAssn_congr {rs : List Reg} {r r' : RegFile}
    (h : ∀ x ∈ rs, r.get x = r'.get x) : regsAssn rs r = regsAssn rs r' := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    simp only [regsAssn]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Reading a coupled register off the machine. -/
theorem holdsFor_regsAssn_get {rs : List Reg} {r : RegFile} {R : Assertion} {s : MachineState}
    {x : Reg} (hx : x ∈ rs) (h : (regsAssn rs r ** R).holdsFor s) :
    s.getReg x = r.get x := by
  induction rs generalizing R with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [regsAssn] at h
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact holdsFor_regIs.mp (holdsFor_sepConj_elim_left (holdsFor_sepConj_assoc.mp h))
    · exact ih hx' (holdsFor_sepConj_pull_second.mp h)

/-- Writing a coupled register on the machine: the frame is untouched, the
    coupling follows the register file. -/
theorem holdsFor_regsAssn_setReg {rs : List Reg} (hnd : rs.Nodup) {x : Reg} (hx : x ∈ rs)
    (hx0 : x ≠ .x0) {r : RegFile} {v : Word} {R : Assertion} {s : MachineState}
    (h : (regsAssn rs r ** R).holdsFor s) :
    (regsAssn rs (r.set x v) ** R).holdsFor (s.setReg x v) := by
  induction rs generalizing R with
  | nil => simp at hx
  | cons a xs ih =>
    have hnd' := List.nodup_cons.mp hnd
    simp only [regsAssn] at h ⊢
    rcases List.mem_cons.mp hx with rfl | hx'
    · have h2 := holdsFor_sepConj_regIs_setReg (v' := v) hx0 (holdsFor_sepConj_assoc.mp h)
      have hxs : regsAssn xs (r.set x v) = regsAssn xs r :=
        regsAssn_congr fun y hy =>
          RegFile.get_set_ne r (fun hyx => hnd'.1 (by rw [← hyx]; exact hy)) v
      rw [hxs, RegFile.get_set_self r hx0]
      exact holdsFor_sepConj_assoc.mpr h2
    · have hne : a ≠ x := fun hax => hnd'.1 (hax ▸ hx')
      have h2 := ih hnd'.2 hx' (holdsFor_sepConj_pull_second.mp h)
      rw [RegFile.get_set_ne r hne]
      exact holdsFor_sepConj_pull_second.mpr h2

/-! ## The two generic leaves -/

/-- An in-scope ALU instruction, on the register-file coupling. -/
theorem cpsWithin_alu {st : Stepper} (hst : st.PlainAgree) {rs : List Reg} (hnd : rs.Nodup)
    {pc : Word} {i : Instr} {cr : CodeReq} (hcr : cr pc = some i)
    (hsub : ∀ x ∈ regsOf i, x ∈ rs) {r r' : RegFile} (h : execPlain pc i r = some r') :
    cpsWithin st 1 pc (pc + 4) cr (regsAssn rs r) (regsAssn rs r') := by
  intro R hR s hinv hcrS hPR hpc
  subst hpc
  obtain ⟨⟨rd, v⟩, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  have hfetch : s.code s.pc = some i := hcrS _ _ hcr
  obtain ⟨hmem, hne, hnb⟩ := aluOf_plain ha
  have hgets : ∀ x ∈ regsOf i, RegFile.get s.regs x = r.get x := fun x hx => by
    rw [← getReg_eq]; exact holdsFor_regsAssn_get (hsub x hx) hPR
  have ha' : aluOf s.pc i s.regs = some (rd, v) := by rw [aluOf_congr hgets]; exact ha
  have hexec := execInstrBr_alu s ha'
  have hstep : st.next s = some (execInstrBr s i) := by
    rw [hst s i hfetch hmem hne hnb]; exact step_non_ecall_non_mem hfetch hne hnb hmem
  refine ⟨1, Nat.le_refl 1, execInstrBr s i, ?_, ?_, ?_⟩
  · rw [Stepper.iter_one]; exact hstep
  · rw [hexec]; rfl
  · rw [hexec]
    apply holdsFor_pcFree_setPC (pcFree_sepConj (regsAssn_pcFree _ _) hR)
    by_cases hrd : rd = .x0
    · subst hrd; rw [RegFile.set_x0]; exact hPR
    · rcases aluOf_dest ha with h0 | hmem'
      · exact absurd h0 hrd
      · exact holdsFor_regsAssn_setReg hnd (hsub rd hmem') hrd hPR

/-- A terminal -- a conditional branch or `JAL x0` -- on the register-file
    coupling: registers unchanged, pc to where `nextPc` says. -/
theorem cpsWithin_terminal {st : Stepper} (hst : st.PlainAgree) {rs : List Reg}
    {pc : Word} {i : Instr} {cr : CodeReq} (hcr : cr pc = some i)
    (hsub : ∀ x ∈ regsOf i, x ∈ rs) (ht : isTerminal i = true)
    {r : RegFile} {t : Word} (hn : nextPc pc i r = some t) :
    cpsWithin st 1 pc t cr (regsAssn rs r) (regsAssn rs r) := by
  intro R hR s hinv hcrS hPR hpc
  subst hpc
  have hfetch : s.code s.pc = some i := hcrS _ _ hcr
  obtain ⟨hmem, hne, hnb⟩ := terminal_plain ht
  have hgets : ∀ x ∈ regsOf i, RegFile.get s.regs x = r.get x := fun x hx => by
    rw [← getReg_eq]; exact holdsFor_regsAssn_get (hsub x hx) hPR
  have hn' : nextPc s.pc i s.regs = some t := by rw [nextPc_congr hgets]; exact hn
  have hexec := execInstrBr_terminal s ht hn'
  have hstep : st.next s = some (execInstrBr s i) := by
    rw [hst s i hfetch hmem hne hnb]; exact step_non_ecall_non_mem hfetch hne hnb hmem
  refine ⟨1, Nat.le_refl 1, execInstrBr s i, ?_, ?_, ?_⟩
  · rw [Stepper.iter_one]; exact hstep
  · rw [hexec]; rfl
  · rw [hexec]
    exact holdsFor_pcFree_setPC (pcFree_sepConj (regsAssn_pcFree _ _) hR) hPR

/-! ## Blocks -/

/-- The instructions sit consecutively in `cr` from `pc`. A `Bool`, so a
    caller can `decide` it on a concrete program. -/
def codeAt (cr : CodeReq) : Word → List Instr → Bool
  | _, [] => true
  | pc, i :: is => decide (cr pc = some i) && codeAt cr (pc + 4) is

/-- Every register the instructions name is in `rs`. -/
def footIn (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => (regsOf i).all fun x => decide (x ∈ rs)

theorem codeAt_cons {cr : CodeReq} {pc : Word} {i : Instr} {is : List Instr}
    (h : codeAt cr pc (i :: is) = true) : cr pc = some i ∧ codeAt cr (pc + 4) is = true := by
  simpa [codeAt] using h

theorem footIn_spec {rs : List Reg} {is : List Instr} (h : footIn rs is = true) :
    ∀ i ∈ is, ∀ x ∈ regsOf i, x ∈ rs := by
  simpa [footIn] using h

theorem footIn_cons {rs : List Reg} {i : Instr} {is : List Instr}
    (h : footIn rs (i :: is) = true) : footIn rs is = true := by
  simp only [footIn, List.all_cons, Bool.and_eq_true] at h
  exact h.2

theorem stepBlock_go_sound {st : Stepper} (hst : st.PlainAgree) {rs : List Reg}
    (hnd : rs.Nodup) {cr : CodeReq} :
    ∀ (is : List Instr) (pc : Word) (r : RegFile) {n : Word} {r' : RegFile},
      codeAt cr pc is = true → footIn rs is = true → stepBlock.go pc is r = some (n, r') →
      cpsWithin st is.length pc n cr (regsAssn rs r) (regsAssn rs r')
  | [], pc, r, n, r', _, _, h => by
    simp only [stepBlock.go, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact cpsWithin_refl (fun _ hp => hp)
  | i :: is, pc, r, n, r', hcode, hfoot, h => by
    obtain ⟨hcr, hrest⟩ := codeAt_cons hcode
    have hfoot' := footIn_spec hfoot
    simp only [stepBlock.go] at h
    split at h
    · rename_i r₁ he
      have h1 := cpsWithin_alu hst hnd hcr (hfoot' i (List.mem_cons_self ..)) he
      have h2 := stepBlock_go_sound hst hnd is (pc + 4) r₁ hrest (footIn_cons hfoot) h
      exact cpsWithin_mono (by simp only [List.length_cons]; omega) (cpsWithin_seq_same_cr h1 h2)
    · split at h
      · split at h
        · rename_i ht
          obtain ⟨t, hn, hp⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact cpsWithin_mono (by simp only [List.length_cons, List.length_nil]; omega)
            (cpsWithin_terminal hst hcr (hfoot' i (List.mem_cons_self ..)) ht hn)
        · cases h
      · cases h

/-- One block, from its entry to where `stepBlock` says, within its length. -/
theorem stepBlock_sound {st : Stepper} (hst : st.PlainAgree) {rs : List Reg} (hnd : rs.Nodup)
    {cr : CodeReq} {b : Block} (hcode : codeAt cr b.entry b.instrs = true)
    (hfoot : footIn rs b.instrs = true)
    {r : RegFile} {n : Word} {r' : RegFile} (h : stepBlock b r = some (n, r')) :
    cpsWithin st b.instrs.length b.entry n cr (regsAssn rs r) (regsAssn rs r') :=
  stepBlock_go_sound hst hnd b.instrs b.entry r hcode hfoot h

/-! ## The walk -/

/-- What one pass claims, read off its result: back to the header with the
    new registers, or out to the exit label with the exit registers. -/
def PassClaim (st : Stepper) (N : Nat) (pc header : Word) (cr : CodeReq) (rs : List Reg)
    (r : RegFile) : RegFile ⊕ Exit → Prop
  | .inl r' => cpsWithin st N pc header cr (regsAssn rs r) (regsAssn rs r')
  | .inr y => cpsWithin st N pc y.label cr (regsAssn rs r) (regsAssn rs y.regs)

theorem PassClaim.mono {st : Stepper} {N N' : Nat} {pc header : Word} {cr : CodeReq}
    {rs : List Reg} {r : RegFile} {o : RegFile ⊕ Exit} (hle : N ≤ N')
    (h : PassClaim st N pc header cr rs r o) : PassClaim st N' pc header cr rs r o := by
  cases o <;> exact cpsWithin_mono hle h

theorem PassClaim.seq {st : Stepper} {n N : Nat} {pc pc' header : Word} {cr : CodeReq}
    {rs : List Reg} {r r₁ : RegFile} {o : RegFile ⊕ Exit}
    (h1 : cpsWithin st n pc pc' cr (regsAssn rs r) (regsAssn rs r₁))
    (h2 : PassClaim st N pc' header cr rs r₁ o) : PassClaim st (n + N) pc header cr rs r o := by
  cases o <;> exact cpsWithin_seq_same_cr h1 h2

/-- The fallback claim: at `pc` with the same registers, in no steps. -/
theorem PassClaim.stay {st : Stepper} (N : Nat) (pc header : Word) (cr : CodeReq) (rs : List Reg)
    (r : RegFile) : PassClaim st N pc header cr rs r (.inr ⟨pc, r⟩) :=
  cpsWithin_mono (Nat.zero_le N) (cpsWithin_refl (fun _ hp => hp))

/-- Every block is resident and names only coupled registers. -/
def passOk (cr : CodeReq) (rs : List Reg) (bs : List Block) : Bool :=
  bs.all fun b => codeAt cr b.entry b.instrs && footIn rs b.instrs

theorem passOk_spec {cr : CodeReq} {rs : List Reg} {bs : List Block} (h : passOk cr rs bs = true) :
    ∀ b ∈ bs, codeAt cr b.entry b.instrs = true ∧ footIn rs b.instrs = true := by
  simpa [passOk] using h

/-- The step budget of a list of blocks. -/
def budget (bs : List Block) : Nat := (bs.map (·.instrs.length)).sum

theorem runPass_sound {st : Stepper} (hst : st.PlainAgree) {rs : List Reg} (hnd : rs.Nodup)
    {cr : CodeReq} {header : Word} {loop : List Block} {resolve : Word → Word} {K : Nat}
    (hres : ∀ (l : Word) (r : RegFile),
      cpsWithin st K l (resolve l) cr (regsAssn rs r) (regsAssn rs r)) :
    ∀ (blks : List Block) (pc : Word) (r : RegFile), passOk cr rs blks = true →
      PassClaim st (budget blks + K) pc header cr rs r (runPass header loop resolve blks pc r)
  | [], pc, r, _ => PassClaim.stay _ _ _ _ _ _
  | b :: rest, pc, r, hok => by
    have hb := passOk_spec hok b (List.mem_cons_self ..)
    have hrest : passOk cr rs rest = true := by
      simp only [passOk, List.all_cons, Bool.and_eq_true] at hok
      exact hok.2
    have hbud : budget (b :: rest) = b.instrs.length + budget rest := by
      simp [budget]
    simp only [runPass]
    split
    · rename_i hpc
      have hpc' : b.entry = pc := by simpa using hpc
      subst hpc'
      split
      · exact PassClaim.stay _ _ _ _ _ _
      · rename_i n r₁ hstep
        have h1 := stepBlock_sound hst hnd hb.1 hb.2 hstep
        split
        · rename_i hn
          have hn' : n = header := by simpa using hn
          subst hn'
          exact cpsWithin_mono (by omega) h1
        · split
          · have h2 := runPass_sound (header := header) (loop := loop) hst hnd hres rest n r₁ hrest
            rw [hbud, Nat.add_assoc]
            exact PassClaim.seq h1 h2
          · show cpsWithin st _ b.entry (resolve n) cr _ _
            exact cpsWithin_mono (by omega) (cpsWithin_seq_same_cr h1 (hres n r₁))
    · exact PassClaim.mono (by omega)
        (runPass_sound (header := header) (loop := loop) hst hnd hres rest pc r hrest)

/-! ## The exit-label resolution -/

/-- Every pure-jump block is resident and jumps where its successor says. -/
def jumpsOk (cr : CodeReq) (bs : List Block) : Bool :=
  bs.all fun b =>
    match b.instrs, b.succ with
    | [.JAL .x0 off], .jump t =>
      decide (cr b.entry = some (.JAL .x0 off)) && decide (t = b.entry + signExtend21 off)
    | _, _ => true

theorem jumpsOk_spec {cr : CodeReq} {bs : List Block} (h : jumpsOk cr bs = true) :
    ∀ b ∈ bs, ∀ (off : BitVec 21) (t : Word), b.instrs = [.JAL .x0 off] → b.succ = .jump t →
      cr b.entry = some (.JAL .x0 off) ∧ t = b.entry + signExtend21 off := by
  intro b hb off t hi hs
  have := (List.all_eq_true.mp h) b hb
  simp only [hi, hs, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

theorem blockAt_mem {bs : List Block} {l : Word} {b : Block} (h : blockAt bs l = some b) :
    b ∈ bs ∧ b.entry = l := by
  simp only [blockAt] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem isPureJump_instrs {b : Block} (h : b.isPureJump = true) :
    ∃ off t, b.instrs = [.JAL .x0 off] ∧ b.succ = .jump t := by
  simp only [Block.isPureJump] at h
  split at h
  · rename_i off t _ _
    exact ⟨off, t, ‹_›, ‹_›⟩
  · cases h

theorem resolveJumps_sound {st : Stepper} (hst : st.PlainAgree) {rs : List Reg}
    {cr : CodeReq} {bs : List Block} (hj : jumpsOk cr bs = true) :
    ∀ (fuel : Nat) (l : Word) (r : RegFile),
      cpsWithin st fuel l (resolveJumps bs fuel l).1 cr (regsAssn rs r) (regsAssn rs r)
  | 0, l, r => cpsWithin_refl (fun _ hp => hp)
  | fuel + 1, l, r => by
    simp only [resolveJumps]
    split
    · rename_i b hb
      obtain ⟨hmem, hl⟩ := blockAt_mem hb
      split
      · rename_i hpure
        obtain ⟨off, t, hinstrs, hsucc⟩ := isPureJump_instrs hpure
        rw [hsucc]
        simp only
        obtain ⟨hcr, ht⟩ := jumpsOk_spec hj b hmem off t hinstrs hsucc
        have h1 : cpsWithin st 1 l t cr (regsAssn rs r) (regsAssn rs r) :=
          cpsWithin_terminal hst (hl ▸ hcr) (by simp [regsOf]) rfl
            (by simp [nextPc, succOf, ht, hl])
        exact cpsWithin_mono (by omega)
          (cpsWithin_seq_same_cr h1 (resolveJumps_sound hst hj fuel t r))
      · exact cpsWithin_mono (Nat.zero_le _) (cpsWithin_refl (fun _ hp => hp))
    · exact cpsWithin_mono (Nat.zero_le _) (cpsWithin_refl (fun _ hp => hp))

/-! ## The certificate -/

/-- **The emitted body is sound.** For any loop the emitter accepts, on any
    `PlainAgree` stepper, with the loop's blocks resident and its footprint
    coupled: a run of the abstract body that returns `y` is a total triple
    from the header to `y.label`, taking the coupling from `x` to `y.regs`.
    No side condition, and no `wellFormed` (see the header). -/
theorem emitBody_sound {st : Stepper} (hst : st.PlainAgree) {rs : List Reg} (hnd : rs.Nodup)
    {cr : CodeReq} {bs : List Block} {info : LoopInfo} {body : RecB RegFile Exit}
    (hbody : emitBody bs info = some body)
    (hpass : passOk cr rs (intervalLoop bs info.backEdge) = true) (hj : jumpsOk cr bs = true)
    {n : Nat} {x : RegFile} {y : Exit} (h : RunsTo body (fun _ => True) n x y) :
    cpsTotal st info.header y.label cr (regsAssn rs x) (regsAssn rs y.regs) := by
  simp only [emitBody] at hbody
  split at hbody
  · cases hbody
    have hres := resolveJumps_sound (rs := rs) hst hj bs.length
    refine cpsTotal_loopB_exits (exitOf := Exit.label) (I := regsAssn rs)
      (Q := fun y => regsAssn rs y.regs)
      (nC := budget (intervalLoop bs info.backEdge) + bs.length)
      (nE := budget (intervalLoop bs info.backEdge) + bs.length) ?_ ?_ h
    · intro x x' hb _
      have := runPass_sound (header := info.header) (loop := intervalLoop bs info.backEdge)
        hst hnd hres (intervalLoop bs info.backEdge) info.header x hpass
      simp only at hb
      rw [hb] at this
      exact this
    · intro x y hb _
      have := runPass_sound (header := info.header) (loop := intervalLoop bs info.backEdge)
        hst hnd hres (intervalLoop bs info.backEdge) info.header x hpass
      simp only at hb
      rw [hb] at this
      exact this
  · cases hbody

/-! ## The two examples, as corollaries

Both program facts are decided; the rest is `emitBody_sound`. Stated on the
`Backend`-indexed steppers so the instance is what a caller would use, and
about `Body.lean`'s `bodyOf`, the definition its `#guard`s pin. -/

/-- `Countdown`, extracted: from the header, a run of the emitted body that
    returns `y` reaches `y.label` with the registers `y.regs`. (Which label
    that is, `+12`, is what `Body.lean`'s `#guard`s show on the checked
    inputs; this theorem does not pin it.) The coupling names `x10` and `x0`
    -- the `BEQ x10, x0` reads both, and `CountdownMachine.I` carries
    `x0 ↦ᵣ 0` for the same reason. -/
theorem countdown_extracted (b : Backend) {n : Nat} {x : RegFile} {y : Exit}
    (h : RunsTo (bodyOf countdownProg) (fun _ => True) n x y) :
    cpsTotal (Backend.stepper b) b0 y.label (CodeReq.ofProg b0 countdownProg)
      (regsAssn [.x10, .x0] x) (regsAssn [.x10, .x0] y.regs) :=
  emitBody_sound (Backend.plainAgree b) (by decide) (bodyOf_eq (by decide))
    (by decide) (by decide) h

/-- `FindIndex`, extracted: the coupling names `x10`, `x11`, `x12`, the exit
    label is whatever the run returned in `y.label`, and there is no side
    condition. Compare `FindIndexMachine.find_found`: same program, the
    coupling over `Nat` instead of the register file, and a side condition
    `i + 1 < 2 ^ 64` that this statement does not need. -/
theorem findIndex_extracted (b : Backend) {n : Nat} {x : RegFile} {y : Exit}
    (h : RunsTo (bodyOf findIndexProg) (fun _ => True) n x y) :
    cpsTotal (Backend.stepper b) b0 y.label (CodeReq.ofProg b0 findIndexProg)
      (regsAssn [.x10, .x11, .x12] x) (regsAssn [.x10, .x11, .x12] y.regs) :=
  emitBody_sound (Backend.plainAgree b) (by decide) (bodyOf_eq (by decide))
    (by decide) (by decide) h

/-- The same with the `JAL` cut off: two labels, one theorem. -/
theorem findIndex_div_extracted (b : Backend) {n : Nat} {x : RegFile} {y : Exit}
    (h : RunsTo (bodyOf (findIndexProg.take 3)) (fun _ => True) n x y) :
    cpsTotal (Backend.stepper b) b0 y.label (CodeReq.ofProg b0 (findIndexProg.take 3))
      (regsAssn [.x10, .x11, .x12] x) (regsAssn [.x10, .x11, .x12] y.regs) :=
  emitBody_sound (Backend.plainAgree b) (by decide) (bodyOf_eq (by decide))
    (by decide) (by decide) h

end Decomp.Extract
