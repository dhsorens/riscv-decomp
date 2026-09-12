/-
  Decomp.Extract.Body

  The extractor's second step (M1): from a loop's blocks, emit the abstract body.

  `Decomp/Extract/CFG.lean` finds the loops and says which rule each wants. This
  file turns one such loop into the `RecB` that rule takes: a total function

      body : RegFile → RegFile ⊕ Exit

  on a register-file abstraction, where a pass that comes back to the header is
  `inl` of the new registers and a pass that leaves is `inr` of the exit label
  and the registers at the exit. The branch conditions decide the split; each
  block's register-only instructions are evaluated symbolically, one function
  on `Reg → Word` per instruction, with exactly the semantics `execInstrBr`
  gives them (`execInstrBr_alu`, `execInstrBr_terminal` and their corollaries
  below are the evidence -- theorems about the generator's *model* of the
  instructions, not about any program).

  Still the generator, so still outside the trusted base: what it emits is a
  candidate that `Decomp/Extract/Cert.lean` (M2) checks against the stepper --
  once, for every body this file can emit. The body is *total* by
  construction: where the walk cannot continue -- an instruction outside the
  supported set, a backward jump that is not the back edge -- it returns `inr`
  at the current pc. That fallback is *sound* (control is indeed at that pc
  with the registers unchanged, in zero steps) but useless: the "exit" it
  names is inside the loop. `wellFormed` is the static check that no path
  reaches it, and `emitBody` refuses a loop that fails it, so that what it
  does emit has real exits.

  ## What is in scope

  * Registers only. The RV64I ALU instructions on full words (register-register
    and register-immediate), `LUI`, `AUIPC`, and the pseudo-instructions `MV`,
    `LI`, `NOP`. Loads, stores, `ECALL`, `EBREAK`, `JALR`, a `JAL` that writes
    a register (a call), the `*W` forms and the M extension are out, and a
    block containing one fails `wellFormed`. Memory is M2's problem at the
    earliest.
  * One loop, no nesting. The loop's blocks are walked in address order and a
    transfer must go to the header (continue), to a *later* block of the loop,
    or out of the loop. A backward transfer to a non-header block is a nested
    loop and fails `wellFormed`.
  * An exit label is resolved through the pure-jump blocks a compiler puts
    between an exit and its join (`resolveJumps`), so a loop whose exits
    converge gets one label and a loop whose exits do not gets several -- the
    body does not care, and neither does `cpsTotal_loopB_exits`.

  Run on the two hand-proved programs, the emitted bodies agree with the
  hand-written `Countdown.countdown` and `FindIndex.find` on every checked
  input, under the couplings their machine files use (`#guard`s at the bottom).
  `Cert.lean` proves the emitted bodies correct against the machine; relating
  them to the hand-written ones is M3.
-/

module

public import Decomp.Extract.CFG
public import Decomp.Tailrec
-- The `#guard`s below *run* the emission on the two example programs.
meta import RiscvZkvm.Rv64.Basic
meta import RiscvZkvm.Rv64.Instructions
meta import Decomp.Extract.CFG

@[expose] public section

namespace Decomp.Extract

open RiscvZkvm.Rv64

/-! ## The register-file abstraction -/

/-- The abstract state: a register file. `x0` reads as zero and ignores writes,
    exactly as `MachineState.getReg` / `setReg` have it. -/
abbrev RegFile := Reg → Word

def RegFile.get (r : RegFile) : Reg → Word
  | .x0 => 0
  | x => r x

def RegFile.set (r : RegFile) : Reg → Word → RegFile
  | .x0, _ => r
  | x, v => fun x' => if x' == x then v else r x'

/-- An in-scope instruction as *destination register and value*, on register
    file `r`, with `execInstrBr`'s semantics. `none` is "not in scope", never
    "traps". `pc` is only for `AUIPC`; `NOP` writes `x0`, which is no write. -/
def aluOf (pc : Word) (i : Instr) (r : RegFile) : Option (Reg × Word) :=
  match i with
  | .ADD rd rs1 rs2 => some (rd, r.get rs1 + r.get rs2)
  | .SUB rd rs1 rs2 => some (rd, r.get rs1 - r.get rs2)
  | .SLL rd rs1 rs2 => some (rd, r.get rs1 <<< ((r.get rs2).toNat % 64))
  | .SRL rd rs1 rs2 => some (rd, r.get rs1 >>> ((r.get rs2).toNat % 64))
  | .SRA rd rs1 rs2 => some (rd, BitVec.sshiftRight (r.get rs1) ((r.get rs2).toNat % 64))
  | .AND rd rs1 rs2 => some (rd, r.get rs1 &&& r.get rs2)
  | .OR rd rs1 rs2 => some (rd, r.get rs1 ||| r.get rs2)
  | .XOR rd rs1 rs2 => some (rd, r.get rs1 ^^^ r.get rs2)
  | .SLT rd rs1 rs2 => some (rd, if BitVec.slt (r.get rs1) (r.get rs2) then 1 else 0)
  | .SLTU rd rs1 rs2 => some (rd, if BitVec.ult (r.get rs1) (r.get rs2) then 1 else 0)
  | .ADDI rd rs1 imm => some (rd, r.get rs1 + signExtend12 imm)
  | .ANDI rd rs1 imm => some (rd, r.get rs1 &&& signExtend12 imm)
  | .ORI rd rs1 imm => some (rd, r.get rs1 ||| signExtend12 imm)
  | .XORI rd rs1 imm => some (rd, r.get rs1 ^^^ signExtend12 imm)
  | .SLTI rd rs1 imm => some (rd, if BitVec.slt (r.get rs1) (signExtend12 imm) then 1 else 0)
  | .SLTIU rd rs1 imm => some (rd, if BitVec.ult (r.get rs1) (signExtend12 imm) then 1 else 0)
  | .SLLI rd rs1 shamt => some (rd, r.get rs1 <<< shamt.toNat)
  | .SRLI rd rs1 shamt => some (rd, r.get rs1 >>> shamt.toNat)
  | .SRAI rd rs1 shamt => some (rd, BitVec.sshiftRight (r.get rs1) shamt.toNat)
  | .LUI rd imm => some (rd, ((imm.zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64)
  | .AUIPC rd imm => some (rd, pc + ((imm.zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64)
  | .MV rd rs => some (rd, r.get rs)
  | .LI rd imm => some (rd, imm)
  | .NOP => some (.x0, 0)
  | _ => none

/-- The register-only instructions as a function on register files. -/
def execPlain (pc : Word) (i : Instr) (r : RegFile) : Option RegFile :=
  (aluOf pc i r).map fun p => r.set p.1 p.2

/-- The registers an instruction names, for the instructions this file
    handles: its footprint. `JAL x0` names none. -/
def regsOf : Instr → List Reg
  | .ADD rd rs1 rs2 | .SUB rd rs1 rs2 | .SLL rd rs1 rs2 | .SRL rd rs1 rs2 | .SRA rd rs1 rs2
  | .AND rd rs1 rs2 | .OR rd rs1 rs2 | .XOR rd rs1 rs2 | .SLT rd rs1 rs2
  | .SLTU rd rs1 rs2 => [rd, rs1, rs2]
  | .ADDI rd rs1 _ | .ANDI rd rs1 _ | .ORI rd rs1 _ | .XORI rd rs1 _ | .SLTI rd rs1 _
  | .SLTIU rd rs1 _ | .SLLI rd rs1 _ | .SRLI rd rs1 _ | .SRAI rd rs1 _ => [rd, rs1]
  | .LUI rd _ | .AUIPC rd _ | .LI rd _ => [rd]
  | .MV rd rs => [rd, rs]
  | .BEQ rs1 rs2 _ | .BNE rs1 rs2 _ | .BLT rs1 rs2 _ | .BGE rs1 rs2 _
  | .BLTU rs1 rs2 _ | .BGEU rs1 rs2 _ => [rs1, rs2]
  | _ => []

/-- Whether an instruction is in `execPlain`'s scope. Independent of the
    register file, so any one will do. -/
def isPlain (i : Instr) : Bool := (execPlain 0 i (fun _ => 0)).isSome

/-- The branch condition, as `execInstrBr` decides it. `false` for anything
    that is not a conditional branch. -/
def branchTaken (i : Instr) (r : RegFile) : Bool :=
  match i with
  | .BEQ rs1 rs2 _ => r.get rs1 == r.get rs2
  | .BNE rs1 rs2 _ => r.get rs1 != r.get rs2
  | .BLT rs1 rs2 _ => BitVec.slt (r.get rs1) (r.get rs2)
  | .BGE rs1 rs2 _ => !BitVec.slt (r.get rs1) (r.get rs2)
  | .BLTU rs1 rs2 _ => BitVec.ult (r.get rs1) (r.get rs2)
  | .BGEU rs1 rs2 _ => !BitVec.ult (r.get rs1) (r.get rs2)
  | _ => false

/-- The transfers a loop body may end a block with: a conditional branch, or a
    `JAL` that writes nothing. A `JAL rd` with `rd ≠ x0` is a call. -/
def isTerminal (i : Instr) : Bool :=
  match i with
  | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. => true
  | .JAL .x0 _ => true
  | _ => false

/-- Where control goes after the instruction at `pc`, on registers `r`, for the
    instructions this file handles. -/
def nextPc (pc : Word) (i : Instr) (r : RegFile) : Option Word :=
  match succOf pc i with
  | .fall n => some n
  | .jump t => some t
  | .branch t f => some (if branchTaken i r then t else f)
  | _ => none

/-! ## Agreement with the machine

`execPlain` is the register half of `execInstrBr`, and `nextPc` is its pc half,
on the instructions in scope. These are theorems about the generator's model of
the instructions, not about any program; `Decomp/Extract/Cert.lean` turns them
into the leaves the certificate is built from. -/

theorem getReg_eq (s : MachineState) (x : Reg) : s.getReg x = RegFile.get s.regs x := by
  cases x <;> rfl

theorem setReg_regs (s : MachineState) (x : Reg) (v : Word) :
    (s.setReg x v).regs = RegFile.set s.regs x v := by
  cases x <;> rfl

theorem RegFile.set_x0 (r : RegFile) (v : Word) : r.set .x0 v = r := rfl

theorem RegFile.get_x0 (r : RegFile) : r.get .x0 = 0 := rfl

theorem RegFile.get_of_ne (r : RegFile) {x : Reg} (h : x ≠ .x0) : r.get x = r x := by
  cases x <;> first | exact absurd rfl h | rfl

theorem RegFile.set_of_ne (r : RegFile) {x : Reg} (h : x ≠ .x0) (v : Word) :
    r.set x v = fun x' => if x' == x then v else r x' := by
  cases x <;> first | exact absurd rfl h | rfl

theorem RegFile.get_set_self (r : RegFile) {x : Reg} (h : x ≠ .x0) (v : Word) :
    (r.set x v).get x = v := by
  rw [RegFile.get_of_ne _ h, RegFile.set_of_ne _ h]; simp

theorem RegFile.get_set_ne (r : RegFile) {x a : Reg} (h : a ≠ x) (v : Word) :
    (r.set x v).get a = r.get a := by
  by_cases hx : x = .x0
  · subst hx; rw [RegFile.set_x0]
  · rw [RegFile.set_of_ne _ hx]
    by_cases ha : a = .x0
    · subst ha; rfl
    · rw [RegFile.get_of_ne _ ha, RegFile.get_of_ne _ ha]
      simp [h]

/-- An in-scope instruction is plain: not a memory access, not a syscall, not
    a breakpoint. -/
theorem aluOf_plain {pc : Word} {i : Instr} {r : RegFile} {p : Reg × Word}
    (h : aluOf pc i r = some p) :
    i.isMemAccess = false ∧ i ≠ .ECALL ∧ i ≠ .EBREAK := by
  cases i <;> simp_all [aluOf, Instr.isMemAccess]

theorem terminal_plain {i : Instr} (h : isTerminal i = true) :
    i.isMemAccess = false ∧ i ≠ .ECALL ∧ i ≠ .EBREAK := by
  cases i <;> simp_all [isTerminal, Instr.isMemAccess]

/-- The destination is a register the instruction names, or `x0`. -/
theorem aluOf_dest {pc : Word} {i : Instr} {r : RegFile} {rd : Reg} {v : Word}
    (h : aluOf pc i r = some (rd, v)) : rd = .x0 ∨ rd ∈ regsOf i := by
  cases i <;> simp_all [aluOf, regsOf]

/-- The value depends on the register file only through the registers the
    instruction names. -/
theorem aluOf_congr {pc : Word} {i : Instr} {r₁ r₂ : RegFile}
    (h : ∀ x ∈ regsOf i, r₁.get x = r₂.get x) : aluOf pc i r₁ = aluOf pc i r₂ := by
  cases i <;> simp_all [aluOf, regsOf]

theorem nextPc_congr {pc : Word} {i : Instr} {r₁ r₂ : RegFile}
    (h : ∀ x ∈ regsOf i, r₁.get x = r₂.get x) : nextPc pc i r₁ = nextPc pc i r₂ := by
  cases i <;> simp_all [nextPc, succOf, branchTaken, regsOf] <;> rfl

/-- On an in-scope instruction, `execInstrBr` is the write `aluOf` names,
    then `pc + 4`. -/
theorem execInstrBr_alu (s : MachineState) {i : Instr} {rd : Reg} {v : Word}
    (h : aluOf s.pc i s.regs = some (rd, v)) :
    execInstrBr s i = (s.setReg rd v).setPC (s.pc + 4) := by
  cases i <;> simp only [aluOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp [execInstrBr, MachineState.setReg, getReg_eq]

/-- On an in-scope instruction, `execInstrBr` writes the registers `execPlain`
    computes and advances the pc by four. -/
theorem execPlain_regs (s : MachineState) (i : Instr) (r' : RegFile)
    (h : execPlain s.pc i s.regs = some r') :
    (execInstrBr s i).regs = r' ∧ (execInstrBr s i).pc = s.pc + 4 := by
  obtain ⟨⟨rd, v⟩, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [execInstrBr_alu s ha]
  exact ⟨setReg_regs s rd v, rfl⟩

/-- On a terminal, `execInstrBr` leaves the registers alone and sets the pc to
    what `nextPc` says. -/
theorem execInstrBr_terminal (s : MachineState) {i : Instr} (ht : isTerminal i = true)
    {t : Word} (hn : nextPc s.pc i s.regs = some t) :
    execInstrBr s i = s.setPC t := by
  cases i <;> simp only [isTerminal, reduceCtorEq] at ht <;>
    first
    | (rename_i rd off; cases rd <;> simp only [reduceCtorEq] at ht
       simp only [nextPc, succOf, Option.some.injEq] at hn; subst hn
       simp [execInstrBr, MachineState.setReg])
    | (simp only [nextPc, succOf, Option.some.injEq] at hn; subst hn
       simp [execInstrBr, branchTaken, getReg_eq] <;> split <;> simp_all)

/-- The pc half, stated as `terminal_step` was. -/
theorem terminal_step (s : MachineState) (i : Instr) (h : isTerminal i = true) :
    (execInstrBr s i).regs = s.regs ∧ nextPc s.pc i s.regs = some (execInstrBr s i).pc := by
  cases i <;> simp only [isTerminal, reduceCtorEq] at h <;>
    first
    | (rename_i rd off; cases rd <;> simp only [reduceCtorEq] at h
       simp [execInstrBr, MachineState.setPC, MachineState.setReg, nextPc, succOf])
    | simp [execInstrBr, MachineState.setPC, nextPc, succOf, branchTaken, getReg_eq] <;>
        split <;> simp_all

/-! ## Walking a loop -/

/-- The output of an extracted loop: the label it left to, and the registers
    at that moment. `cpsTotal_loopB_exits` takes `exitOf := Exit.label`. -/
structure Exit where
  label : Word
  regs : RegFile

/-- Run one block from its entry: the in-scope instructions update the
    registers, the terminal (if any) decides the next pc. `none` means the
    block is out of scope. -/
def stepBlock (b : Block) (r : RegFile) : Option (Word × RegFile) :=
  go b.entry b.instrs r
where
  go : Word → List Instr → RegFile → Option (Word × RegFile)
    | pc, [], r => some (pc, r)
    | pc, i :: is, r =>
      match execPlain pc i r with
      | some r' => go (pc + 4) is r'
      | none =>
        match is with
        | [] => if isTerminal i then (nextPc pc i r).map (·, r) else none
        | _ :: _ => none

/-- One pass of the body, walking the loop's blocks in address order from `pc`.
    Total: where the walk cannot go on it returns `inr` at the current pc, a
    claim the certificate will fail to discharge; `wellFormed` says when that
    cannot happen. -/
def runPass (header : Word) (loop : List Block) (resolve : Word → Word) :
    List Block → Word → RegFile → RegFile ⊕ Exit
  | [], pc, r => .inr ⟨pc, r⟩
  | b :: rest, pc, r =>
    if b.entry == pc then
      match stepBlock b r with
      | none => .inr ⟨pc, r⟩
      | some (n, r') =>
        if n == header then .inl r'
        else if inLoop loop n then runPass header loop resolve rest n r'
        else .inr ⟨resolve n, r'⟩
    else runPass header loop resolve rest pc r

/-- The static check that `runPass` never hits its fallback: every block's
    instructions are in scope with at most a terminal at the end, and every
    in-loop successor is the header or a later block. -/
def wellFormed (header : Word) (loop : List Block) : Bool :=
  loop.all fun b =>
    let body := b.instrs.dropLast
    let last := b.instrs.getLast?
    body.all isPlain &&
    (match last with
     | some i => isPlain i || isTerminal i
     | none => false) &&
    b.succ.targets.all fun t =>
      t == header || !inLoop loop t || b.entry.toNat < t.toNat

/-- The abstract body of one loop, or `none` if the loop is outside this
    file's scope. -/
def emitBody (bs : List Block) (info : LoopInfo) : Option (RecB RegFile Exit) :=
  let loop := intervalLoop bs info.backEdge
  if wellFormed info.header loop then
    some ⟨fun r =>
      runPass info.header loop (fun l => (resolveJumps bs bs.length l).1) loop info.header r⟩
  else none

/-- Every loop of a program with its body, where one can be emitted. -/
def emitAll (base : Word) (prog : Program) : List (LoopInfo × Option (RecB RegFile Exit)) :=
  let bs := blocks base prog
  (loops base prog).map fun info => (info, emitBody bs info)

/-! ## Checks against the hand-written bodies

The two example programs, under the couplings `CountdownMachine.lean` and
`FindIndexMachine.lean` use (`x10 ↦ᵣ n`; `x10 ↦ᵣ i ** x11 ↦ᵣ stop ** x12 ↦ᵣ e`).
Each `#guard` runs the emitted body on one input and compares with the hand
body run on the abstract state. -/

private def b0 : Word := 0x1000

/-- Did the pass continue, and do the registers satisfy `p`? -/
private def continues (o : RegFile ⊕ Exit) (p : RegFile → Bool) : Bool :=
  match o with
  | .inl r => p r
  | .inr _ => false

/-- Did the pass leave to `label`, with registers satisfying `p`? -/
private def leavesTo (o : RegFile ⊕ Exit) (label : Word) (p : RegFile → Bool) : Bool :=
  match o with
  | .inl _ => false
  | .inr e => e.label == label && p e.regs

private def regs (x10 : Word) (x11 : Word := 0) (x12 : Word := 0) : RegFile :=
  fun x => match x with
    | .x10 => x10
    | .x11 => x11
    | .x12 => x12
    | _ => 0

private def bodyOf (prog : Program) : RecB RegFile Exit :=
  match emitAll b0 prog with
  | [(_, some r)] => r
  | _ => ⟨fun r => .inr ⟨0, r⟩⟩

-- Both loops are in scope.
#guard (emitAll b0 countdownProg).all (·.2.isSome)
#guard (emitAll b0 findIndexProg).all (·.2.isSome)
#guard (emitAll b0 (findIndexProg.take 3)).all (·.2.isSome)

-- Countdown, against `countdown.toRecB`: continue with `n - 1` while `n ≠ 0`,
-- leave to `+12` with `n` once it is.
#guard continues ((bodyOf countdownProg).body (regs 5)) (fun r => r.get .x10 == 4)
#guard continues ((bodyOf countdownProg).body (regs 1)) (fun r => r.get .x10 == 0)
#guard leavesTo ((bodyOf countdownProg).body (regs 0)) (b0 + 12) (fun r => r.get .x10 == 0)

-- FindIndex, against `find stop e`: `i = stop` leaves at once (through the
-- pure-jump block, so to `+16`); `i + 1 = e` leaves from the bottom, also to
-- `+16`, with `x10 = e`; otherwise continue with `i + 1`.
#guard leavesTo ((bodyOf findIndexProg).body (regs 3 3 8)) (b0 + 16) (fun r => r.get .x10 == 3)
#guard leavesTo ((bodyOf findIndexProg).body (regs 7 3 8)) (b0 + 16) (fun r => r.get .x10 == 8)
#guard continues ((bodyOf findIndexProg).body (regs 4 3 8)) (fun r => r.get .x10 == 5 && r.get .x11 == 3 && r.get .x12 == 8)
-- The order of the two tests is the hand body's: a hit at the top wins over
-- an exhaustion at the bottom.
#guard leavesTo ((bodyOf findIndexProg).body (regs 7 7 8)) (b0 + 16) (fun r => r.get .x10 == 7)

-- With the `JAL` cut off, the same passes leave to two different labels: the
-- shape `find_found_div` / `find_exhausted_div` prove.
#guard leavesTo ((bodyOf (findIndexProg.take 3)).body (regs 3 3 8)) (b0 + 16) (fun r => r.get .x10 == 3)
#guard leavesTo ((bodyOf (findIndexProg.take 3)).body (regs 7 3 8)) (b0 + 12) (fun r => r.get .x10 == 8)

-- Out of scope, refused rather than mis-emitted: a load in the body, a call in
-- the body, a nested loop.
#guard (emitAll b0 [.BEQ .x10 .x0 (12 : BitVec 13), .LD .x11 .x10 0, .JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 8))]).all (·.2.isNone)
#guard (emitAll b0 [.BEQ .x10 .x0 (12 : BitVec 13), .JAL .x1 (BitVec.ofNat 21 4), .JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 8))]).all (·.2.isNone)
#guard (emitAll b0 [
    .BEQ .x10 .x0 (20 : BitVec 13),
    .ADDI .x11 .x11 (BitVec.ofNat 12 (2 ^ 12 - 1)),
    .BNE .x11 .x0 (BitVec.ofNat 13 (2 ^ 13 - 4)),
    .ADDI .x10 .x10 (BitVec.ofNat 12 (2 ^ 12 - 1)),
    .JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 16))]).any (·.2.isNone)

end Decomp.Extract
