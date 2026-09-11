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
  gives them (`execPlain_regs` and `terminal_step`, proved below, are the
  evidence -- the only theorems in the file, and they are about the
  generator's *model*, not about any program).

  Still the generator, so still outside the trusted base: what it emits is a
  candidate the certificate (M2) has to check against the stepper. A body that
  is wrong here is a certificate that fails to build. That is also why the body
  is *total* by construction: where the walk cannot continue -- an instruction
  outside the supported set, a backward jump that is not the back edge -- it
  returns `inr` at the current pc, which is a claim the certificate will then
  fail to discharge. `wellFormed` is the static check that no path reaches
  that fallback, and `emitBody` refuses a loop that fails it.

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
  That agreement is what M2 will have to *prove*, per loop, by discharging the
  emitted obligations against the leaves.
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

/-- The register-only instructions, with `execInstrBr`'s semantics. `none` is
    "not in scope", never "traps". `pc` is only for `AUIPC`. -/
def execPlain (pc : Word) (i : Instr) (r : RegFile) : Option RegFile :=
  match i with
  | .ADD rd rs1 rs2 => some (r.set rd (r.get rs1 + r.get rs2))
  | .SUB rd rs1 rs2 => some (r.set rd (r.get rs1 - r.get rs2))
  | .SLL rd rs1 rs2 => some (r.set rd (r.get rs1 <<< ((r.get rs2).toNat % 64)))
  | .SRL rd rs1 rs2 => some (r.set rd (r.get rs1 >>> ((r.get rs2).toNat % 64)))
  | .SRA rd rs1 rs2 => some (r.set rd (BitVec.sshiftRight (r.get rs1) ((r.get rs2).toNat % 64)))
  | .AND rd rs1 rs2 => some (r.set rd (r.get rs1 &&& r.get rs2))
  | .OR rd rs1 rs2 => some (r.set rd (r.get rs1 ||| r.get rs2))
  | .XOR rd rs1 rs2 => some (r.set rd (r.get rs1 ^^^ r.get rs2))
  | .SLT rd rs1 rs2 => some (r.set rd (if BitVec.slt (r.get rs1) (r.get rs2) then 1 else 0))
  | .SLTU rd rs1 rs2 => some (r.set rd (if BitVec.ult (r.get rs1) (r.get rs2) then 1 else 0))
  | .ADDI rd rs1 imm => some (r.set rd (r.get rs1 + signExtend12 imm))
  | .ANDI rd rs1 imm => some (r.set rd (r.get rs1 &&& signExtend12 imm))
  | .ORI rd rs1 imm => some (r.set rd (r.get rs1 ||| signExtend12 imm))
  | .XORI rd rs1 imm => some (r.set rd (r.get rs1 ^^^ signExtend12 imm))
  | .SLTI rd rs1 imm => some (r.set rd (if BitVec.slt (r.get rs1) (signExtend12 imm) then 1 else 0))
  | .SLTIU rd rs1 imm => some (r.set rd (if BitVec.ult (r.get rs1) (signExtend12 imm) then 1 else 0))
  | .SLLI rd rs1 shamt => some (r.set rd (r.get rs1 <<< shamt.toNat))
  | .SRLI rd rs1 shamt => some (r.set rd (r.get rs1 >>> shamt.toNat))
  | .SRAI rd rs1 shamt => some (r.set rd (BitVec.sshiftRight (r.get rs1) shamt.toNat))
  | .LUI rd imm => some (r.set rd (((imm.zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64))
  | .AUIPC rd imm => some (r.set rd (pc + ((imm.zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64))
  | .MV rd rs => some (r.set rd (r.get rs))
  | .LI rd imm => some (r.set rd imm)
  | .NOP => some r
  | _ => none

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

The one theorem here. `execPlain` is the register half of `execInstrBr`, and
`nextPc` is its pc half, on the instructions in scope. M2 composes leaves, not
this, but it is what makes "symbolic evaluation" mean something. -/

theorem getReg_eq (s : MachineState) (x : Reg) : s.getReg x = RegFile.get s.regs x := by
  cases x <;> rfl

theorem setReg_regs (s : MachineState) (x : Reg) (v : Word) :
    (s.setReg x v).regs = RegFile.set s.regs x v := by
  cases x <;> rfl

/-- On an in-scope instruction, `execInstrBr` writes the registers `execPlain`
    computes and advances the pc by four. -/
theorem execPlain_regs (s : MachineState) (i : Instr) (r' : RegFile)
    (h : execPlain s.pc i s.regs = some r') :
    (execInstrBr s i).regs = r' ∧ (execInstrBr s i).pc = s.pc + 4 := by
  cases i <;> simp only [execPlain, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [execInstrBr, MachineState.setPC, setReg_regs, getReg_eq]

/-- On a terminal, `execInstrBr` leaves the registers alone and goes where
    `nextPc` says. -/
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
