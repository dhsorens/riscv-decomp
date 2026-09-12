/-
  Decomp.Extract.SumDown

  A second function nobody wrote by hand (M3, second half).

  Four instructions that add `x10, x10 - 1, …, 1` into `x11`:

      loop:  BEQ  x10, x0, +16     -- while x10 ≠ 0
             ADD  x11, x11, x10    --   x11 += x10
             ADDI x10, x10, -1     --   x10 -= 1
             JAL  x0, -12          -- back to loop

  There is no `SumDownMachine.lean`: no leaf is framed, no block is composed,
  no loop rule is applied by hand. The machine-level certificate is
  `emitBody_sound` at this program (`sumDown_extracted`), with the two program
  facts `decide`d. What a user then proves is about the emitted body alone --
  two equations read off it (`sd_exit`, `sd_cont`), then an ordinary
  induction on the counter (`sd_runsTo`) -- and the machine theorem is a
  corollary (`sumDown_correct`): from `x10 = n`, `x11 = acc`, the loop reaches
  `+16` with `x10 = 0` and `x11 = acc + (1 + 2 + ⋯ + n)`, for every
  representable `n`, on both backends. The word arithmetic is exact; the only
  hypothesis is that `n` fits in a register, which is what makes the countdown
  terminate.

  The two equations are still written by hand from the emitted function, as
  in `Reproduce.lean`; the pattern is the same and is the thing to automate.
-/

module

public import Decomp.Extract.Cert

@[expose] public section

namespace Decomp.Extract

open RiscvZkvm.Rv64

/-- `BEQ x10, x0, +16; ADD x11, x11, x10; ADDI x10, x10, -1; JAL x0, -12`. -/
def sumDownProg : Program := [
  .BEQ .x10 .x0 (16 : BitVec 13),
  .ADD .x11 .x11 .x10,
  .ADDI .x10 .x10 (BitVec.ofNat 12 (2 ^ 12 - 1)),
  .JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 12))
]

/-! ## The certificate, for free -/

/-- The extracted certificate: no hand proof anywhere behind it. -/
theorem sumDown_extracted (b : Backend) {n : Nat} {x : RegFile} {y : Exit}
    (h : RunsTo (bodyOf sumDownProg) (fun _ => True) n x y) :
    cpsTotal (Backend.stepper b) b0 y.label (CodeReq.ofProg b0 sumDownProg)
      (regsAssn [.x10, .x11, .x0] x) (regsAssn [.x10, .x11, .x0] y.regs) :=
  emitBody_sound (Backend.plainAgree b) (by decide) (bodyOf_eq (by decide))
    (by decide) (by decide) h

/-! ## The emitted body, as two equations -/

def sblk1 : Block := ⟨b0, [.BEQ .x10 .x0 (16 : BitVec 13)], .branch (b0 + 16) (b0 + 4)⟩
def sblk2 : Block :=
  ⟨b0 + 4, [.ADD .x11 .x11 .x10, .ADDI .x10 .x10 (BitVec.ofNat 12 (2 ^ 12 - 1)),
    .JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 12))], .jump b0⟩

def sdLoop : List Block := [sblk1, sblk2]
def sdResolve (l : Word) : Word := (resolveJumps sdLoop sdLoop.length l).1

theorem sd_blocks : blocks b0 sumDownProg = sdLoop := by decide
theorem sd_header : (theLoop sumDownProg).header = b0 := by decide
theorem sd_backEdge : (theLoop sumDownProg).backEdge = ⟨b0, b0 + 4⟩ := by decide
theorem sd_loop : intervalLoop sdLoop ⟨b0, b0 + 4⟩ = sdLoop := by decide
theorem sd_wf : wellFormed b0 sdLoop = true := by decide

theorem bodyOf_sd : bodyOf sumDownProg = ⟨fun r => runPass b0 sdLoop sdResolve sdLoop b0 r⟩ := by
  unfold bodyOf
  rw [sd_blocks]
  simp only [emitBody, sd_header, sd_backEdge, sd_loop, sd_wf, if_true, Option.getD_some]
  rfl

theorem sblk1_entry : sblk1.entry = b0 := rfl
theorem sblk1_instrs : sblk1.instrs = [.BEQ .x10 .x0 (16 : BitVec 13)] := rfl
theorem sblk2_entry : sblk2.entry = b0 + 4 := rfl
theorem sblk2_instrs : sblk2.instrs =
    [.ADD .x11 .x11 .x10, .ADDI .x10 .x10 (BitVec.ofNat 12 (2 ^ 12 - 1)),
      .JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 12))] := rfl
theorem sd_lbl1 : (b0 + 16 == b0) = false := by decide
theorem sd_lbl2 : (b0 + 4 == b0) = false := by decide
theorem sd_lbl3 : inLoop [sblk1, sblk2] (b0 + 16) = false := by decide
theorem sd_lbl4 : inLoop [sblk1, sblk2] (b0 + 4) = true := by decide
theorem sd_res : sdResolve (b0 + 16) = b0 + 16 := by decide
theorem sext_m1 : signExtend12 (BitVec.ofNat 12 (2 ^ 12 - 1)) = (-1 : Word) := by decide
theorem sd_sext16 : signExtend13 (16 : BitVec 13) = (16 : Word) := by decide
theorem sd_jal : b0 + 4 + 4 + 4 + signExtend21 (BitVec.ofNat 21 (2 ^ 21 - 12)) = b0 := by decide

/-- `x10 = 0`: leave to `+16`, registers untouched. -/
theorem sd_exit (r : RegFile) (h : r.get .x10 = 0) :
    (bodyOf sumDownProg).body r = .inr ⟨b0 + 16, r⟩ := by
  rw [bodyOf_sd]
  show runPass b0 sdLoop sdResolve sdLoop b0 r = _
  have e1 : execPlain b0 (.BEQ .x10 .x0 (16 : BitVec 13)) r = none := rfl
  have hc : (r.get .x10 == r.get .x0) = true := by rw [h]; rfl
  have t1 : nextPc b0 (.BEQ .x10 .x0 (16 : BitVec 13)) r = some (b0 + 16) := by
    simp only [nextPc, succOf, branchTaken, hc, if_true, sd_sext16]
  simp only [sdLoop, runPass, sblk1_entry, sblk1_instrs, stepBlock, stepBlock.go, e1, isTerminal,
    t1, Option.map_some, beq_self_eq_true, if_true, sd_lbl1, sd_lbl3, Bool.false_eq_true, if_false,
    sd_res]

/-- `x10 ≠ 0`: one pass, back to the header, `x11 += x10` then `x10 -= 1`. -/
theorem sd_cont (r : RegFile) (h : r.get .x10 ≠ 0) :
    (bodyOf sumDownProg).body r =
      .inl ((r.set .x11 (r.get .x11 + r.get .x10)).set .x10 (r.get .x10 + (-1))) := by
  rw [bodyOf_sd]
  show runPass b0 sdLoop sdResolve sdLoop b0 r = _
  have e1 : execPlain b0 (.BEQ .x10 .x0 (16 : BitVec 13)) r = none := rfl
  have hc : (r.get .x10 == r.get .x0) = false := by
    rw [RegFile.get_x0]; exact beq_eq_false_iff_ne.mpr h
  have t1 : nextPc b0 (.BEQ .x10 .x0 (16 : BitVec 13)) r = some (b0 + 4) := by
    simp only [nextPc, succOf, branchTaken, hc, Bool.false_eq_true, if_false]
  have e2 : execPlain (b0 + 4) (.ADD .x11 .x11 .x10) r =
      some (r.set .x11 (r.get .x11 + r.get .x10)) := rfl
  set r₁ := r.set .x11 (r.get .x11 + r.get .x10) with hr₁
  have g10 : r₁.get .x10 = r.get .x10 := RegFile.get_set_ne r (by decide) _
  have e3 : execPlain (b0 + 4 + 4) (.ADDI .x10 .x10 (BitVec.ofNat 12 (2 ^ 12 - 1))) r₁ =
      some (r₁.set .x10 (r.get .x10 + (-1))) := by
    show some (r₁.set .x10 (r₁.get .x10 + signExtend12 (BitVec.ofNat 12 (2 ^ 12 - 1)))) = _
    rw [sext_m1, g10]
  set r₂ := r₁.set .x10 (r.get .x10 + (-1)) with hr₂
  have e4 : execPlain (b0 + 4 + 4 + 4) (.JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 12))) r₂ = none := rfl
  have t4 : nextPc (b0 + 4 + 4 + 4) (.JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 12))) r₂ = some b0 := by
    simp only [nextPc, succOf, sd_jal]
  -- Staged: one `simp only` over both blocks hands the kernel a term it
  -- cannot check (deep recursion); block by block it is immediate.
  simp only [sdLoop, runPass, sblk1_entry, sblk1_instrs, stepBlock, stepBlock.go, e1, isTerminal,
    t1, Option.map_some, beq_self_eq_true, if_true, sd_lbl2, sd_lbl4, Bool.false_eq_true, if_false]
  simp only [sblk2_entry, sblk2_instrs, stepBlock.go, e2, beq_self_eq_true, if_true]
  simp only [e3]
  simp only [e4]
  simp only [isTerminal]
  simp only [t4, Option.map_some]
  simp only [if_true, beq_self_eq_true]

/-! ## The abstract theorem, and the machine theorem it buys -/

/-- The register file with `x10 = a`, `x11 = b`, everything else zero. -/
def rf2 (a b : Word) : RegFile := fun x =>
  match x with
  | .x10 => a
  | .x11 => b
  | _ => 0

@[simp] theorem rf2_get10 (a b : Word) : (rf2 a b).get .x10 = a := rfl
@[simp] theorem rf2_get11 (a b : Word) : (rf2 a b).get .x11 = b := rfl
theorem rf2_set11 (a b v : Word) : (rf2 a b).set .x11 v = rf2 a v := by
  funext x; cases x <;> rfl
theorem rf2_set10 (a b v : Word) : (rf2 a b).set .x10 v = rf2 v b := by
  funext x; cases x <;> rfl

/-- `1 + 2 + ⋯ + n`, as a word. -/
def tri : Nat → Word
  | 0 => 0
  | n + 1 => tri n + BitVec.ofNat 64 (n + 1)

theorem ofNat_pred (n : Nat) :
    BitVec.ofNat 64 (n + 1) + (-1 : Word) = BitVec.ofNat 64 n := by
  bv_omega

theorem ofNat_succ_ne_zero (n : Nat) (hn : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 (n + 1) ≠ 0 := by
  intro h
  bv_omega

/-- The abstract theorem: from `x10 = n`, the emitted body runs `n` passes and
    leaves with `x10 = 0`, `x11 = acc + tri n`. Ordinary induction on `n`; no
    machine in sight. -/
theorem sd_runsTo (acc : Word) : ∀ n : Nat, n < 2 ^ 64 →
    RunsTo (bodyOf sumDownProg) (fun _ => True) n (rf2 (BitVec.ofNat 64 n) acc)
      ⟨b0 + 16, rf2 0 (acc + tri n)⟩
  | 0, _ => by
    refine RunsTo.exit ?_ trivial
    rw [sd_exit (rf2 (BitVec.ofNat 64 0) acc) rfl]
    simp [tri]
  | n + 1, hn => by
    have ih := sd_runsTo (acc + BitVec.ofNat 64 (n + 1)) n (by omega)
    have hb : (bodyOf sumDownProg).body (rf2 (BitVec.ofNat 64 (n + 1)) acc) =
        .inl (rf2 (BitVec.ofNat 64 n) (acc + BitVec.ofNat 64 (n + 1))) := by
      rw [sd_cont (rf2 (BitVec.ofNat 64 (n + 1)) acc) (ofNat_succ_ne_zero n hn)]
      rw [rf2_get11, rf2_get10, rf2_set11, rf2_set10, ofNat_pred n]
    have hacc : acc + BitVec.ofNat 64 (n + 1) + tri n = acc + tri (n + 1) := by
      simp only [tri]; bv_omega
    rw [hacc] at ih
    exact RunsTo.iter hb trivial ih

/-- **The machine theorem, with no hand proof behind it.** On either backend,
    from `x10 = n` and `x11 = acc`, the four instructions reach `+16` with
    `x10 = 0` and `x11 = acc + (1 + ⋯ + n)`. -/
theorem sumDown_correct (b : Backend) (n : Nat) (acc : Word) (hn : n < 2 ^ 64) :
    cpsTotalOn b b0 (b0 + 16) (CodeReq.ofProg b0 sumDownProg)
      (regsAssn [.x10, .x11, .x0] (rf2 (BitVec.ofNat 64 n) acc))
      (regsAssn [.x10, .x11, .x0] (rf2 0 (acc + tri n))) :=
  sumDown_extracted b (sd_runsTo acc n hn)

end Decomp.Extract
