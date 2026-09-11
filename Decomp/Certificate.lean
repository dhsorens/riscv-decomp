/-
  Decomp.Certificate

  The standardised L2 output contract.

  The genericity boundary belongs here
  rather than at L1: do not abstract the separation logic over an abstract
  machine, standardise the *output* of decompilation instead. The contract it
  names is

      an L2 region certificate := (f : α → β) × (f_pre : α → Prop)
                                × (proof : machine-level triple)

  and `Cert` below is exactly that. The payoff is that everything above L2 sees
  only `fn`, `pre` and `post` -- no `Instr`, no `MachineState`, no `Word`, no
  `Stepper` -- so the L3 refinement calculus and the L4 specification are
  ISA-generic for free, and a second `*-asm` project reuses the expensive
  artifact (the proofs) rather than the plumbing.

  Nothing here is ZIP-2005-specific.
-/

import Decomp.Loop

namespace Decomp

open RiscvZkvm.Rv64

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- A decompiled code region: a Lean function, the side condition under which
    it describes the region, and the machine-level triple tying the two to the
    code.

    `sound` is quantified over the *trusted* stepper applied to the code
    requirement, which is why a generator that emits a `Cert` stays out of the
    TCB: a mistake in translation shows up as a `Cert` that cannot be built, not
    as a false theorem. Vale states the
    same argument. -/
structure Cert (st : Stepper) (α : Type u) (β : Type v) where
  /-- Where the region starts. -/
  entry : Word
  /-- Where it leaves. -/
  exit_ : Word
  /-- The code that must be resident. -/
  cr : CodeReq
  /-- The extracted function. -/
  fn : α → β
  /-- The generated side condition. TR-765's returned `cond`: a verification
      that uses `fn` has to prove it, "otherwise the postcondition of the
      certificate theorem has no meaning". -/
  pre : α → Prop
  /-- How an abstract input sits in the machine at `entry`. -/
  couple : α → Assertion
  /-- How an abstract output sits in the machine at `exit_`. -/
  post : β → Assertion
  /-- The certificate theorem. -/
  sound : ∀ x, pre x → cpsTotal st entry exit_ cr (couple x) (post (fn x))

namespace Cert

variable {st : Stepper}

/-- Grow the code requirement -- the lift from one function's `CodeReq.ofProg`
    to the whole image.

    `RiscvZkvm.Rv64.CodeReq.ofProg_sub_ofEntries_of_extentsOk` produces an
    `hmono` of exactly this shape from a single decidable extent check, so for
    this repository the call is

        c.extendCode (CodeReq.ofProg_sub_ofEntries_of_extentsOk
          Image.entries_ok (by norm_num) _ he)

    with `Image.entries_ok` the image's decidable extent check and `he` the
    membership of this function's entry in its `entries` table. That is the
    composition `Rv64.Logic.CodeReqExtents` was built for. -/
def extendCode (c : Cert st α β) {cr' : CodeReq}
    (hmono : ∀ a i, c.cr a = some i → cr' a = some i) : Cert st α β :=
  { c with
    cr := cr'
    sound := fun x hx => cpsTotal_extend_code hmono (c.sound x hx) }

@[simp] theorem extendCode_fn (c : Cert st α β) {cr' : CodeReq}
    (hmono : ∀ a i, c.cr a = some i → cr' a = some i) :
    (c.extendCode hmono).fn = c.fn := rfl

@[simp] theorem extendCode_pre (c : Cert st α β) {cr' : CodeReq}
    (hmono : ∀ a i, c.cr a = some i → cr' a = some i) :
    (c.extendCode hmono).pre = c.pre := rfl

/-- Strengthen the side condition and the coupling, weaken the observation.
    The rule of consequence at the certificate level. -/
def weaken (c : Cert st α β) {pre' : α → Prop} {couple' : α → Assertion}
    {post' : β → Assertion}
    (hpre : ∀ x, pre' x → c.pre x)
    (hcouple : ∀ x hp, couple' x hp → c.couple x hp)
    (hpost : ∀ y hp, c.post y hp → post' y hp) : Cert st α β :=
  { c with
    pre := pre'
    couple := couple'
    post := post'
    sound := fun x hx =>
      cpsTotal_weaken (hcouple x) (hpost (c.fn x)) (c.sound x (hpre x hx)) }

/-- Frame an assertion through a certificate: whatever the region does not
    touch, it leaves alone. -/
def frameR (c : Cert st α β) (F : Assertion) (hF : F.pcFree) : Cert st α β :=
  { c with
    couple := fun x => c.couple x ** F
    post := fun y => c.post y ** F
    sound := fun x hx => cpsTotal_frameR F hF (c.sound x hx) }

/-- Sequential composition of two regions, the second starting where the first
    stops. The composite's side condition is the first's conjoined with the
    second's *at the first's output* -- TR-765 §2.6.2's Seq propagation rule,
    which is why the obligation composes rather than being reinvented. -/
def seq (c1 : Cert st α β) (c2 : Cert st β γ) (hmid : c1.exit_ = c2.entry)
    (hcr : c1.cr = c2.cr)
    (hlink : ∀ y hp, c1.post y hp → c2.couple y hp) : Cert st α γ where
  entry := c1.entry
  exit_ := c2.exit_
  cr := c1.cr
  fn := fun x => c2.fn (c1.fn x)
  pre := fun x => c1.pre x ∧ c2.pre (c1.fn x)
  couple := c1.couple
  post := c2.post
  sound := fun x hx => by
    refine cpsTotal_seq_same_cr (c1.sound x hx.1) ?_
    rw [hmid, hcr]
    exact cpsTotal_weaken (hlink (c1.fn x)) (fun _ hp => hp) (c2.sound _ hx.2)

/-- Package a loop as a certificate. This is the intended way to build one:
    `pre` is `Terminates r side`, so TR-765's rider -- that a verification using
    the extracted function must discharge the returned `cond` -- is structural
    rather than a convention someone has to remember. -/
def ofLoop {r : Rec α β} {side : α → Prop}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {I J : α → Assertion} {Q : β → Assertion} {nH nB : Nat} {f : α → β}
    (hHeaderTrue : ∀ x, r.guard x = true → side x →
      cpsWithin st nH header bodyEntry cr (I x) (J x))
    (hHeaderFalse : ∀ x, r.guard x = false →
      cpsWithin st nH header exit_ cr (I x) (Q (r.out x)))
    (hBody : ∀ x, r.guard x = true → side x →
      cpsWithin st nB bodyEntry header cr (J x) (I (r.step x)))
    (heq : ∀ n x, TerminatesIn r side n x → r.runN n x = f x) :
    Cert st α β where
  entry := header
  exit_ := exit_
  cr := cr
  fn := f
  pre := Terminates r side
  couple := I
  post := Q
  sound := fun _ h => cpsTotal_loop_eq hHeaderTrue hHeaderFalse hBody heq h

@[simp] theorem ofLoop_fn {r : Rec α β} {side : α → Prop}
    {header bodyEntry exit_ : Word} {cr : CodeReq}
    {I J : α → Assertion} {Q : β → Assertion} {nH nB : Nat} {f : α → β}
    (h1 : ∀ x, r.guard x = true → side x →
      cpsWithin st nH header bodyEntry cr (I x) (J x))
    (h2 : ∀ x, r.guard x = false → cpsWithin st nH header exit_ cr (I x) (Q (r.out x)))
    (h3 : ∀ x, r.guard x = true → side x →
      cpsWithin st nB bodyEntry header cr (J x) (I (r.step x)))
    (h4 : ∀ n x, TerminatesIn r side n x → r.runN n x = f x) :
    (ofLoop h1 h2 h3 h4).fn = f := rfl

/-- Package a returning-body loop as a certificate. `pre` is `TerminatesB r
    side`, for the same reason `ofLoop`'s is `Terminates`: the rider is
    structural. `heq` is the closed-form obligation -- whatever the region
    returns is `f x` -- and it is quantified over every derivation, so a body
    with several `inr` branches discharges it once per branch
    (`Examples/FindIndex.lean`'s `runsTo_eq_result`). -/
def ofLoopB {r : RecB α β} {side : α → Prop}
    {entry exit_ : Word} {cr : CodeReq}
    {I : α → Assertion} {Q : β → Assertion} {nC nE : Nat} {f : α → β}
    (hCont : ∀ x x', r.body x = .inl x' → side x →
      cpsWithin st nC entry entry cr (I x) (I x'))
    (hExit : ∀ x y, r.body x = .inr y → side x →
      cpsWithin st nE entry exit_ cr (I x) (Q y))
    (heq : ∀ n x y, RunsTo r side n x y → y = f x) :
    Cert st α β where
  entry := entry
  exit_ := exit_
  cr := cr
  fn := f
  pre := TerminatesB r side
  couple := I
  post := Q
  sound := fun _ h => cpsTotal_loopB_eq hCont hExit heq h

@[simp] theorem ofLoopB_fn {r : RecB α β} {side : α → Prop}
    {entry exit_ : Word} {cr : CodeReq}
    {I : α → Assertion} {Q : β → Assertion} {nC nE : Nat} {f : α → β}
    (h1 : ∀ x x', r.body x = .inl x' → side x →
      cpsWithin st nC entry entry cr (I x) (I x'))
    (h2 : ∀ x y, r.body x = .inr y → side x →
      cpsWithin st nE entry exit_ cr (I x) (Q y))
    (h3 : ∀ n x y, RunsTo r side n x y → y = f x) :
    (ofLoopB h1 h2 h3).fn = f := rfl

end Cert

end Decomp
