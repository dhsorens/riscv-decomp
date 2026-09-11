/-
  Decomp.Extract.CFG

  The extractor's first step: recover the control-flow shape of a `Program`.

  A decompiler-into-logic (TR-765 §3) begins by cutting the code into basic
  blocks, finding the loops, and deciding which rule each loop wants. Nothing
  here proves anything -- this is the **generator**, and it stays out of the
  trusted base because what it emits is later re-checked against the stepper.
  So every definition is computable, every claim it makes about a program is a
  `#guard` at the bottom of the file, and a wrong answer here is a certificate
  that fails to build, not a false theorem.

  What is recovered, per program:

  * **Blocks.** Maximal straight-line runs, cut at every control transfer and
    at every transfer target (`blocks`). Each carries the successor shape of
    its last instruction (`Succ`): fall-through, jump, two-way branch, syscall
    (which continues at `pc + 4` unless it is `HALT`, a fact the CFG cannot
    know), trap, or **indirect** -- a `JALR`, whose target is a register value
    and is the roadmap's known risk: CFG recovery stops there and a hand-written
    certificate has to take over. One blind spot to know before M1: a `JAL`
    with `rd ≠ x0` is a *call*, and `succOf` treats it as an unconditional
    jump that never returns to `pc + 4`, so a loop containing a call is
    analysed as leaving through the callee. Calls are M1's business, where the
    callee's certificate is sequenced in.
  * **Loops.** A back edge is a transfer to a block entry at or before the
    transferring block; its target is the header. The loop's blocks are taken to
    be the address interval from the header to the back edge's source
    (`intervalLoop`) -- true of compiler output for a reducible loop, and said
    in the name rather than assumed silently.
  * **Shape.** Whether the loop is what `cpsTotal_loop` wants (guard at the
    header, one exit, the body a straight line back) or what `cpsTotal_loopB`
    wants (exits from wherever the body decides), and, for the second, whether
    the exits **converge**: following each exit through the pure-jump blocks
    the compiler puts between an exit and its join, do they reach one label?
    If they do, that label is the region's `exit_` and those blocks are the
    ones the region must include; if not, the loop wants
    `cpsTotal_loopB_exits`.

  Run on the two hand-proved examples, this reproduces the analysis their
  headers describe in prose: `Countdown` is header-guarded with one exit;
  `FindIndex` has two exits that converge on `base + 16` through the `JAL` at
  `base + 12`. That is the check that the recovery is looking at the right
  things. `Decomp/Extract/Body.lean` (M1) takes the loops found here and emits
  their abstract bodies (`ROADMAP.md` item 6).
-/

module

public import Decomp.Upstream
-- The `#guard`s below *run* the recovery, so the interpreter needs the code
-- behind `Instr`, `signExtend13` / `signExtend21` and the `Word` arithmetic.
meta import RiscvZkvm.Rv64.Basic
meta import RiscvZkvm.Rv64.Instructions

@[expose] public section

namespace Decomp.Extract

open RiscvZkvm.Rv64

/-! ## Successors -/

/-- Where control can go after one instruction. -/
inductive Succ where
  /-- The next instruction. -/
  | fall (next : Word)
  /-- An unconditional direct jump (`JAL`). -/
  | jump (target : Word)
  /-- A two-way branch: taken target, fall-through. -/
  | branch (taken fall : Word)
  /-- A syscall. Continues at `next` unless it is the halt syscall, which the
      CFG cannot tell from the instruction alone. -/
  | syscall (next : Word)
  /-- `EBREAK`: the machine traps. -/
  | trap
  /-- `JALR`: the target is a register value. CFG recovery stops here. -/
  | indirect
  deriving DecidableEq, Repr

/-- The successor shape of the instruction at `pc`. -/
def succOf (pc : Word) : Instr → Succ
  | .BEQ _ _ off | .BNE _ _ off | .BLT _ _ off | .BGE _ _ off
  | .BLTU _ _ off | .BGEU _ _ off => .branch (pc + signExtend13 off) (pc + 4)
  | .JAL _ off => .jump (pc + signExtend21 off)
  | .JALR _ _ _ => .indirect
  | .ECALL => .syscall (pc + 4)
  | .EBREAK => .trap
  | _ => .fall (pc + 4)

/-- The labels a successor can lead to. -/
def Succ.targets : Succ → List Word
  | .fall n => [n]
  | .jump t => [t]
  | .branch t f => [t, f]
  | .syscall n => [n]
  | .trap => []
  | .indirect => []

/-- Straight-line: the only successor is the next instruction. -/
def Succ.isFall : Succ → Bool
  | .fall _ => true
  | _ => false

/-! ## Addressing -/

/-- The instruction at `pc`, if `pc` is a word-aligned address inside the
    program. -/
def instrAt (base : Word) (prog : Program) (pc : Word) : Option Instr :=
  let d := (pc - base).toNat
  if d % 4 = 0 then prog[d / 4]? else none

def inRange (base : Word) (prog : Program) (pc : Word) : Bool :=
  (instrAt base prog pc).isSome

/-- The program's addresses, in order. -/
def addresses (base : Word) (prog : Program) : List Word :=
  (List.range prog.length).map fun k => base + BitVec.ofNat 64 (4 * k)

/-- Insertion into an address-sorted list without duplicates. -/
def insertAddr (a : Word) : List Word → List Word
  | [] => [a]
  | b :: rest =>
    if a = b then b :: rest
    else if a.toNat < b.toNat then a :: b :: rest
    else b :: insertAddr a rest

def sortDedup (as : List Word) : List Word := as.foldr insertAddr []

/-! ## Blocks -/

/-- A basic block: its entry, its instructions, and where its last instruction
    can go. -/
structure Block where
  entry : Word
  instrs : List Instr
  succ : Succ
  deriving Repr

/-- The block's last address. -/
def Block.last (b : Block) : Word := b.entry + BitVec.ofNat 64 (4 * (b.instrs.length - 1))

/-- Block leaders: the entry, every in-range transfer target, and the
    instruction after every non-fall-through instruction. -/
def leaders (base : Word) (prog : Program) : List Word :=
  let fromInstrs := (addresses base prog).flatMap fun pc =>
    match instrAt base prog pc with
    | none => []
    | some i =>
      let s := succOf pc i
      let targets := s.targets.filter (inRange base prog)
      if s.isFall then [] else targets ++ [pc + 4]
  sortDedup (base :: fromInstrs.filter (inRange base prog))

/-- Read one block starting at `pc`: stop after a non-fall-through instruction,
    before a leader, or at the end of the program. Fuel is the program length. -/
def readBlock (base : Word) (prog : Program) (ls : List Word) : Nat → Word → List Instr × Succ
  | 0, pc => ([], .fall pc)
  | fuel + 1, pc =>
    match instrAt base prog pc with
    | none => ([], .fall pc)
    | some i =>
      let s := succOf pc i
      if !s.isFall then ([i], s)
      else if ls.contains (pc + 4) || !inRange base prog (pc + 4) then ([i], .fall (pc + 4))
      else
        let (rest, s') := readBlock base prog ls fuel (pc + 4)
        (i :: rest, s')

/-- The program's basic blocks, in address order. -/
def blocks (base : Word) (prog : Program) : List Block :=
  let ls := leaders base prog
  ls.map fun l =>
    let (is, s) := readBlock base prog ls prog.length l
    ⟨l, is, s⟩

def blockAt (bs : List Block) (l : Word) : Option Block := bs.find? (·.entry = l)

/-! ## Loops -/

/-- A back edge: a transfer from block `src` to a block entry `header` at or
    before `src`. -/
structure BackEdge where
  header : Word
  src : Word
  deriving Repr, DecidableEq

def backEdges (bs : List Block) : List BackEdge :=
  bs.flatMap fun b =>
    b.succ.targets.filterMap fun t =>
      if (bs.any (·.entry = t)) && t.toNat ≤ b.entry.toNat then some ⟨t, b.entry⟩ else none

/-- The blocks of the loop with the given back edge, taken as the address
    interval `[header, src]`. Right for compiler output of a reducible loop;
    named so nobody reads it as dominator analysis. -/
def intervalLoop (bs : List Block) (e : BackEdge) : List Block :=
  bs.filter fun b => e.header.toNat ≤ b.entry.toNat && b.entry.toNat ≤ e.src.toNat

def inLoop (loop : List Block) (l : Word) : Bool := loop.any (·.entry = l)

/-- The labels the loop leaves to, with the block that leaves. -/
def loopExits (loop : List Block) : List (Word × Word) :=
  loop.flatMap fun b =>
    b.succ.targets.filterMap fun t => if inLoop loop t then none else some (b.entry, t)

/-- A block that is nothing but an unconditional jump: what a compiler puts
    between a loop exit and the label another exit already targets. -/
def Block.isPureJump (b : Block) : Bool :=
  match b.instrs, b.succ with
  | [.JAL .x0 _], .jump _ => true
  | _, _ => false

/-- Follow pure-jump blocks from `l`, collecting the ones traversed. Fuel bounds
    a jump cycle. -/
def resolveJumps (bs : List Block) : Nat → Word → Word × List Word
  | 0, l => (l, [])
  | fuel + 1, l =>
    match blockAt bs l with
    | some b =>
      if b.isPureJump then
        match b.succ with
        | .jump t =>
          let (l', via) := resolveJumps bs fuel t
          (l', b.entry :: via)
        | _ => (l, [])
      else (l, [])
    | none => (l, [])

/-- Which loop rule the shape wants. -/
inductive LoopShape where
  /-- Guard at the header, one exit, body a straight line back:
      `cpsTotal_loop`. -/
  | headerGuarded (exit_ : Word)
  /-- Exits from inside the body, all converging on `join` through the
      pure-jump blocks `via`: `cpsTotal_loopB` over the region extended by
      `via`. -/
  | bodyExitsConverge (join : Word) (via : List Word)
  /-- Exits that do not converge: `cpsTotal_loopB_exits`. -/
  | bodyExitsDiverge (exits : List Word)
  deriving Repr, DecidableEq

/-- The analysis of one loop. -/
structure LoopInfo where
  header : Word
  backEdge : BackEdge
  members : List Word
  exits : List (Word × Word)
  shape : LoopShape
  /-- Some block in the loop ends in `JALR`; recovery is incomplete here. -/
  hasIndirect : Bool
  deriving Repr

def classify (bs : List Block) (e : BackEdge) : LoopInfo :=
  let loop := intervalLoop bs e
  let exits := loopExits loop
  let hasIndirect := loop.any fun b => b.succ = .indirect
  let headerGuarded :=
    match blockAt loop e.header with
    | some h =>
      match h.succ with
      | .branch t f =>
        -- exactly one arm leaves, every other block stays inside
        (inLoop loop t != inLoop loop f) && exits.all (·.1 = e.header)
      | _ => false
    | none => false
  let shape :=
    if headerGuarded then
      match exits with
      | [(_, x)] => .headerGuarded x
      | _ => .bodyExitsDiverge (exits.map (·.2))
    else
      let resolved := exits.map fun (_, x) => resolveJumps bs bs.length x
      match resolved with
      | [] => .bodyExitsDiverge []
      | (j, _) :: _ =>
        if resolved.all (·.1 = j) then
          .bodyExitsConverge j (sortDedup (resolved.flatMap (·.2)))
        else .bodyExitsDiverge (sortDedup (exits.map (·.2)))
  ⟨e.header, e, loop.map (·.entry), exits, shape, hasIndirect⟩

/-- Every loop of the program, by back edge. -/
def loops (base : Word) (prog : Program) : List LoopInfo :=
  let bs := blocks base prog
  (backEdges bs).map (classify bs)

/-! ## Checks against the hand-proved examples

These run the recovery on the two programs whose analysis was done by hand in
`Examples/CountdownMachine.lean` and `Examples/FindIndexMachine.lean`, and pin
it to what those files say. -/

/-- `Countdown`: `BEQ x10, x0, +12; ADDI x10, x10, -1; JAL x0, -8`. -/
def countdownProg : Program := [
  .BEQ .x10 .x0 (12 : BitVec 13),
  .ADDI .x10 .x10 (BitVec.ofNat 12 (2 ^ 12 - 1)),
  .JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 8))
]

/-- `FindIndex`: `BEQ x10, x11, +16; ADDI x10, x10, 1; BNE x10, x12, -8; JAL x0, +4`. -/
def findIndexProg : Program := [
  .BEQ .x10 .x11 (16 : BitVec 13),
  .ADDI .x10 .x10 (1 : BitVec 12),
  .BNE .x10 .x12 (BitVec.ofNat 13 (2 ^ 13 - 8)),
  .JAL .x0 (BitVec.ofNat 21 4)
]

-- A base with room on both sides.
private def b0 : Word := 0x1000

-- Countdown: two blocks, `[BEQ]` at +0 and `[ADDI; JAL]` at +4.
#guard (blocks b0 countdownProg).map (·.entry) == [b0, b0 + 4]
#guard (blocks b0 countdownProg).map (·.instrs.length) == [1, 2]
#guard (blocks b0 countdownProg).map (·.succ) == [.branch (b0 + 12) (b0 + 4), .jump b0]
-- One loop, header-guarded, exiting to +12.
#guard (loops b0 countdownProg).map (·.shape) == [.headerGuarded (b0 + 12)]
#guard (loops b0 countdownProg).map (·.members) == [[b0, b0 + 4]]

-- FindIndex: three blocks, `[BEQ]`, `[ADDI; BNE]`, `[JAL]`.
#guard (blocks b0 findIndexProg).map (·.entry) == [b0, b0 + 4, b0 + 12]
#guard (blocks b0 findIndexProg).map (·.instrs.length) == [1, 2, 1]
#guard (blocks b0 findIndexProg).map (·.succ)
  == [.branch (b0 + 16) (b0 + 4), .branch b0 (b0 + 12), .jump (b0 + 16)]
-- One loop over the first two blocks, with two exits -- from the top and from
-- the bottom -- that converge on +16 through the pure-jump block at +12. This
-- is exactly the region `FindIndexMachine.lean` proves, and the `JAL` it says
-- the region must include.
#guard (loops b0 findIndexProg).map (·.members) == [[b0, b0 + 4]]
#guard (loops b0 findIndexProg).map (·.exits) == [[(b0, b0 + 16), (b0 + 4, b0 + 12)]]
#guard (loops b0 findIndexProg).map (·.shape) == [.bodyExitsConverge (b0 + 16) [b0 + 12]]
#guard (loops b0 findIndexProg).all (!·.hasIndirect)

-- The same loop with the `JAL` removed: the exits no longer converge, which
-- is the shape `cpsTotal_loopB_exits` is for (`find_found_div`).
#guard (loops b0 (findIndexProg.take 3)).map (·.shape)
  == [.bodyExitsDiverge [b0 + 12, b0 + 16]]

-- A computed branch is flagged rather than followed.
#guard (loops b0 [.BEQ .x10 .x0 (8 : BitVec 13), .JALR .x0 .x1 0, .JAL .x0 (BitVec.ofNat 21 (2 ^ 21 - 8))]).all (·.hasIndirect)
  == true

end Decomp.Extract
