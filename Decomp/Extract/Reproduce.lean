/-
  Decomp.Extract.Reproduce

  The extractor reproduces the hand certificate (M3, first half).

  `Examples/FindIndexMachine.lean` proves `find_found` and `find_exhausted` by
  hand: five leaves framed to a coupling over `Nat`, sequenced by hand, fed to
  the loop rule. `Extract/Cert.lean` proves `findIndex_extracted` with no
  per-instruction work at all, but about the *emitted* body over a register
  file. This file closes the gap: it relates the emitted body to the
  hand-written `find` under the coupling

      x10 = i,  x11 = stop,  x12 = e

  (`runsTo_lift`), and then `find_found` and `find_exhausted` at the base the
  emitter was run at fall out of `findIndex_extracted` in a few lines each
  (`find_found_extracted`, `find_exhausted_extracted`). Same program, same
  coupling `I`, same conclusion; the hand proof's five leaves and three
  compositions are not needed.

  ## What "relates" means here

  Three equations say what the emitted body does on a register file,
  case-split on the two branch conditions (`body_hit`, `body_miss_end`,
  `body_miss_cont`). They are proved by running the emitter's walk
  symbolically: the control-flow facts are closed terms and are `decide`d
  (`blocks_fi`, `theLoop_fi`, `loop_fi`, and the label facts); what remains is
  the body's own `if`s, which the hypotheses settle. The simulation is then an
  induction on the hand body's `RunsTo`, one case per equation.

  The hand body's side condition `i + 1 < 2 ^ 64` reappears -- not because the
  machine needs it, but because relating a `Nat` abstraction to the register
  file needs `BitVec.ofNat` to be injective on the values in play. The
  extracted certificate itself (`findIndex_extracted`) has no side condition.

  ## What this is not

  It is at the emitter's base `0x1000`, where the hand theorems are for every
  base; the control-flow facts are `decide`d, not proved for `blocks base
  prog` in general. And the three equations are written by hand: the emitter
  produces a function, and reading the function back as equations is a
  human step here. A `simp` set that does it for any single-loop program is
  the obvious next automation.
-/

module

public import Decomp.Extract.Cert
public import Decomp.Examples.FindIndexMachine

@[expose] public section

namespace Decomp.Extract

open RiscvZkvm.Rv64
open Decomp.Examples.FindIndex (find side I Q Res prog cr result runsTo_found runsTo_exhausted
  body_found body_exhausted body_cont ofNat_succ ofNat_inj_iff sext12_one sext13_sixteen)

/-! ## The control-flow facts, decided -/

theorem findIndexProg_eq : findIndexProg = prog := rfl

/-- The three blocks the CFG pass finds, as named literals -- named so the
    walk below can be unfolded over them without unfolding them. -/
def blk1 : Block := ⟨b0, [.BEQ .x10 .x11 (16 : BitVec 13)], .branch (b0 + 16) (b0 + 4)⟩
def blk2 : Block :=
  ⟨b0 + 4, [.ADDI .x10 .x10 (1 : BitVec 12), .BNE .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8))],
    .branch b0 (b0 + 12)⟩
def blk3 : Block := ⟨b0 + 12, [.JAL .x0 (BitVec.ofNat 21 4)], .jump (b0 + 16)⟩

def fiBlocks : List Block := [blk1, blk2, blk3]

/-- The loop's two blocks. -/
def fiLoop : List Block := [blk1, blk2]

/-- The exit-label resolution the emitter installs. -/
def fiResolve (l : Word) : Word := (resolveJumps fiBlocks fiBlocks.length l).1

theorem blocks_fi : blocks b0 findIndexProg = fiBlocks := by decide
theorem theLoop_fi : theLoop findIndexProg =
    ⟨b0, ⟨b0, b0 + 4⟩, [b0, b0 + 4], [(b0, b0 + 16), (b0 + 4, b0 + 12)],
      .bodyExitsConverge (b0 + 16) [b0 + 12], false⟩ := by decide
theorem loop_fi : intervalLoop fiBlocks ⟨b0, b0 + 4⟩ = fiLoop := by decide
theorem wf_fi : wellFormed b0 fiLoop = true := by decide

/-- The emitted body, unfolded to the walk over the two blocks. -/
theorem bodyOf_fi : bodyOf findIndexProg = ⟨fun r => runPass b0 fiLoop fiResolve fiLoop b0 r⟩ := by
  unfold bodyOf
  rw [blocks_fi, theLoop_fi]
  simp only [emitBody, loop_fi, wf_fi, if_true, Option.getD_some]
  rfl

-- The block fields, and the label facts the walk consults.
theorem blk1_entry : blk1.entry = b0 := rfl
theorem blk1_instrs : blk1.instrs = [.BEQ .x10 .x11 (16 : BitVec 13)] := rfl
theorem blk2_entry : blk2.entry = b0 + 4 := rfl
theorem blk2_instrs : blk2.instrs =
    [.ADDI .x10 .x10 (1 : BitVec 12), .BNE .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8))] := rfl
theorem lbl1 : (b0 + 16 == b0) = false := by decide
theorem lbl2 : (b0 + 4 == b0) = false := by decide
theorem lbl3 : (b0 + 12 == b0) = false := by decide
theorem lbl4 : inLoop [blk1, blk2] (b0 + 16) = false := by decide
theorem lbl5 : inLoop [blk1, blk2] (b0 + 4) = true := by decide
theorem lbl6 : inLoop [blk1, blk2] (b0 + 12) = false := by decide
theorem res1 : fiResolve (b0 + 16) = b0 + 16 := by decide
theorem res2 : fiResolve (b0 + 12) = b0 + 16 := by decide
theorem sext_one : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide

/-! ## The emitted body, as three equations -/

/-- `BEQ` taken: leave at once, to `+16`, registers untouched. -/
theorem body_hit (r : RegFile) (h : r.get .x10 = r.get .x11) :
    (bodyOf findIndexProg).body r = .inr ⟨b0 + 16, r⟩ := by
  rw [bodyOf_fi]
  show runPass b0 fiLoop fiResolve fiLoop b0 r = _
  have e1 : execPlain b0 (.BEQ .x10 .x11 (16 : BitVec 13)) r = none := rfl
  have t1 : nextPc b0 (.BEQ .x10 .x11 (16 : BitVec 13)) r = some (b0 + 16) := by
    simp [nextPc, succOf, branchTaken, h] <;> decide
  simp only [fiLoop, runPass, blk1_entry, blk1_instrs, stepBlock, stepBlock.go, e1, isTerminal, t1,
    Option.map_some, beq_self_eq_true, if_true, lbl1, lbl4, Bool.false_eq_true, if_false, res1]

/-- `BEQ` not taken, `BNE` not taken: through the `ADDI` and the `JAL` to
    `+16`, with `x10` stepped. -/
theorem body_miss_end (r : RegFile) (h1 : r.get .x10 ≠ r.get .x11)
    (h2 : r.get .x10 + 1 = r.get .x12) :
    (bodyOf findIndexProg).body r = .inr ⟨b0 + 16, r.set .x10 (r.get .x10 + 1)⟩ := by
  rw [bodyOf_fi]
  show runPass b0 fiLoop fiResolve fiLoop b0 r = _
  have e1 : execPlain b0 (.BEQ .x10 .x11 (16 : BitVec 13)) r = none := rfl
  have t1 : nextPc b0 (.BEQ .x10 .x11 (16 : BitVec 13)) r = some (b0 + 4) := by
    simp [nextPc, succOf, branchTaken, h1]
  have e2 : execPlain (b0 + 4) (.ADDI .x10 .x10 (1 : BitVec 12)) r =
      some (r.set .x10 (r.get .x10 + 1)) := by
    show some (r.set .x10 (r.get .x10 + signExtend12 (1 : BitVec 12))) = _
    rw [sext_one]
  set r' := r.set .x10 (r.get .x10 + 1) with hr'
  have g10 : r'.get .x10 = r.get .x10 + 1 := RegFile.get_set_self r (by decide) _
  have g12 : r'.get .x12 = r.get .x12 := RegFile.get_set_ne r (by decide) _
  have e3 : execPlain (b0 + 4 + 4) (.BNE .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8))) r' = none := rfl
  have hc : ((r.get .x10 + 1) != r.get .x12) = false := by rw [h2, bne_self_eq_false]
  have t3 : nextPc (b0 + 4 + 4) (.BNE .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8))) r' =
      some (b0 + 12) := by
    simp only [nextPc, succOf, branchTaken, g10, g12, hc, Bool.false_eq_true, if_false]
    decide
  simp only [fiLoop, runPass, blk1_entry, blk1_instrs, blk2_entry, blk2_instrs, stepBlock,
    stepBlock.go, e1, isTerminal, t1, Option.map_some, beq_self_eq_true, if_true, lbl2, lbl5,
    Bool.false_eq_true, if_false, e2, e3, t3, lbl3, lbl6, res2]

/-- `BEQ` not taken, `BNE` taken: back to the header with `x10` stepped. -/
theorem body_miss_cont (r : RegFile) (h1 : r.get .x10 ≠ r.get .x11)
    (h2 : r.get .x10 + 1 ≠ r.get .x12) :
    (bodyOf findIndexProg).body r = .inl (r.set .x10 (r.get .x10 + 1)) := by
  rw [bodyOf_fi]
  show runPass b0 fiLoop fiResolve fiLoop b0 r = _
  have e1 : execPlain b0 (.BEQ .x10 .x11 (16 : BitVec 13)) r = none := rfl
  have t1 : nextPc b0 (.BEQ .x10 .x11 (16 : BitVec 13)) r = some (b0 + 4) := by
    simp [nextPc, succOf, branchTaken, h1]
  have e2 : execPlain (b0 + 4) (.ADDI .x10 .x10 (1 : BitVec 12)) r =
      some (r.set .x10 (r.get .x10 + 1)) := by
    show some (r.set .x10 (r.get .x10 + signExtend12 (1 : BitVec 12))) = _
    rw [sext_one]
  set r' := r.set .x10 (r.get .x10 + 1) with hr'
  have g10 : r'.get .x10 = r.get .x10 + 1 := RegFile.get_set_self r (by decide) _
  have g12 : r'.get .x12 = r.get .x12 := RegFile.get_set_ne r (by decide) _
  have e3 : execPlain (b0 + 4 + 4) (.BNE .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8))) r' = none := rfl
  have hc : ((r.get .x10 + 1) != r.get .x12) = true := bne_iff_ne.mpr h2
  have t3 : nextPc (b0 + 4 + 4) (.BNE .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8))) r' = some b0 := by
    simp only [nextPc, succOf, branchTaken, g10, g12, hc, if_true]
    decide
  simp only [fiLoop, runPass, blk1_entry, blk1_instrs, blk2_entry, blk2_instrs, stepBlock,
    stepBlock.go, e1, isTerminal, t1, Option.map_some, beq_self_eq_true, if_true, lbl2, lbl5,
    Bool.false_eq_true, if_false, e2, e3, t3]

/-! ## The coupling, and the simulation -/

/-- The register file the hand coupling `I stop e i` describes. -/
def rf (i stop e : Nat) : RegFile := fun x =>
  match x with
  | .x10 => BitVec.ofNat 64 i
  | .x11 => BitVec.ofNat 64 stop
  | .x12 => BitVec.ofNat 64 e
  | _ => 0

@[simp] theorem rf_get10 (i stop e : Nat) : (rf i stop e).get .x10 = BitVec.ofNat 64 i := rfl
@[simp] theorem rf_get11 (i stop e : Nat) : (rf i stop e).get .x11 = BitVec.ofNat 64 stop := rfl
@[simp] theorem rf_get12 (i stop e : Nat) : (rf i stop e).get .x12 = BitVec.ofNat 64 e := rfl

theorem rf_set10 (i j stop e : Nat) :
    (rf i stop e).set .x10 (BitVec.ofNat 64 j) = rf j stop e := by
  funext x; cases x <;> rfl

/-- The hand body's output, as the emitted body's `Exit`. Both exits land on
    `+16`; the registers are `I`'s at the returned index. -/
def lift (stop e : Nat) : Res → Exit
  | .found j => ⟨b0 + 16, rf j stop e⟩
  | .exhausted => ⟨b0 + 16, rf e stop e⟩

/-- **The simulation.** Every run of the hand-written `find` is a run of the
    emitted body, step for step, under the coupling. Structural recursion on
    the derivation; one case per body equation. -/
theorem runsTo_lift {stop e : Nat} (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) :
    ∀ {n : Nat} {i : Nat} {y : Res}, RunsTo (find stop e) side n i y →
      RunsTo (bodyOf findIndexProg) (fun _ => True) n (rf i stop e) (lift stop e y)
  | _, i, y, .exit hb hs => by
    have hs' : i + 1 < 2 ^ 64 := hs
    refine RunsTo.exit ?_ trivial
    by_cases h1 : i = stop
    · rw [body_found h1] at hb
      cases hb
      rw [body_hit _ (by simp [h1])]
      rfl
    · by_cases h2 : i + 1 = e
      · rw [body_exhausted h1 h2] at hb
        cases hb
        have hi : i < 2 ^ 64 := by omega
        rw [body_miss_end (rf i stop e) (fun h => h1 ((ofNat_inj_iff hi hstop).mp h))
          (by show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 e; rw [ofNat_succ, h2])]
        show Sum.inr (Exit.mk (b0 + 16) ((rf i stop e).set .x10 (BitVec.ofNat 64 i + 1))) = _
        rw [ofNat_succ, rf_set10, h2]
        rfl
      · rw [body_cont h1 h2] at hb
        cases hb
  | _, i, y, .iter hb hs h' => by
    have hs' : i + 1 < 2 ^ 64 := hs
    have ih := runsTo_lift hstop he h'
    by_cases h1 : i = stop
    · rw [body_found h1] at hb; cases hb
    by_cases h2 : i + 1 = e
    · rw [body_exhausted h1 h2] at hb; cases hb
    rw [body_cont h1 h2] at hb
    cases hb
    refine RunsTo.iter ?_ trivial ih
    have hi : i < 2 ^ 64 := by omega
    rw [body_miss_cont (rf i stop e) (fun h => h1 ((ofNat_inj_iff hi hstop).mp h))
      (by show BitVec.ofNat 64 i + 1 ≠ BitVec.ofNat 64 e
          rw [ofNat_succ]; exact fun h => h2 ((ofNat_inj_iff hs' he).mp h))]
    show (Sum.inl ((rf i stop e).set .x10 (BitVec.ofNat 64 i + 1)) : RegFile ⊕ Exit) = _
    rw [ofNat_succ, rf_set10]

/-! ## The hand certificate, reproduced -/

/-- The register-file coupling over `x10, x11, x12` *is* the hand coupling. -/
theorem regsAssn_eq_I (i stop e : Nat) :
    regsAssn [.x10, .x11, .x12] (rf i stop e) = I stop e i := by
  simp only [regsAssn, rf_get10, rf_get11, rf_get12, sepConj_emp_right', I]
  ac_rfl

/-- `find_found`, at the emitter's base, from the extracted certificate. -/
theorem find_found_extracted (b : Backend) {stop e i : Nat}
    (hse : stop < e) (he : e < 2 ^ 64) (hi : i ≤ stop) :
    cpsTotalOn b b0 (b0 + 16) (cr b0) (I stop e i) (I stop e stop) := by
  have h := findIndex_extracted b
    (runsTo_lift (by omega) he (runsTo_found hse he (stop - i) i (by omega)))
  simpa [cpsTotalOn, cr, findIndexProg_eq, lift, regsAssn_eq_I] using h

/-- `find_exhausted`, at the emitter's base, from the extracted certificate. -/
theorem find_exhausted_extracted (b : Backend) {stop e i : Nat}
    (hstop : stop < 2 ^ 64) (he : e < 2 ^ 64) (hi : i < e)
    (hno : ∀ j, i ≤ j → j < e → j ≠ stop) :
    cpsTotalOn b b0 (b0 + 16) (cr b0) (I stop e i) (I stop e e) := by
  have h := findIndex_extracted b
    (runsTo_lift hstop he (runsTo_exhausted he (e - 1 - i) i (by omega) hno))
  simpa [cpsTotalOn, cr, findIndexProg_eq, lift, regsAssn_eq_I] using h

end Decomp.Extract
