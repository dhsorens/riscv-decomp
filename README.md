# riscv-decomp

Myreen-style decompilation into logic for RISC-V, in Lean 4, over an abstract
stepper.

A machine-code region is turned into a **tail-recursive function** plus a
**certificate theorem** relating that function to the machine. Every subsequent
proof is a proof about the function. No fuel parameter, no invented loop variant,
no step budget threaded through the statement.

The namespace is `Decomp`; the method is Magnus Myreen's, from
*Formal verification of machine-code programs* (UCAM-CL-TR-765).

Extracted from [`zip-2005-asm`](https://github.com/dhsorens/zip-2005-asm), where
it was the L2 layer under a ZIP-2005 guest, and where its worked instances still
live.

```
lake build            # 89 jobs, zero warnings
scripts/check-axioms.sh
scripts/check-forbidden-tactics.sh
```

## What is here

| Module | What it is |
| --- | --- |
| `Decomp.Upstream` | The one file that names `riscv-zkvm`: re-exports the module-system contents of its two legacy aggregators. |
| `Decomp.Stepper` | The two-field interface a backend owes: `next`, and "execution never rewrites code". Everything below is stated over it, so ZisK, SP1 and any future backend instantiate rather than fork. |
| `Decomp.Triple` | The judgements: `cpsWithin` (bounded), `cpsTotal` (Myreen's `∃k`), `cpsBranch`, `cpsHalt`, `cpsSyscallHalt`. 30-odd structural rules — frame, sequence, weaken, extend-code — restated over a `Stepper`. |
| `Decomp.Tailrec` | Conditional termination as an *inductive*, so the least fixpoint is termination and Lean's generated `.rec` is TR-765's derived induction principle. Two shapes: `Rec` (header-guarded) and `RecB` (`body : α → α ⊕ β`, for a body that may return). |
| `Decomp.Loop` | The loop rules. `cpsTotal_loop` for a header-guarded loop; `cpsTotal_loopB` for a body that may return — which covers an early `break`, a mid-body exit, and a bottom-guarded loop with no rotation. `cpsTotal_loop_of_loopB` proves the second subsumes the first. |
| `Decomp.Certificate` | TR-765's L2 output contract as a structure: `(fn, pre, sound)`, with the rider that the caller must discharge `pre` made structural rather than documentary. |
| `Decomp.Leaf.*` | One-instruction specs. `Core` transfers upstream's ZisK leaves to any `PlainAgree` stepper (18 of 26 constructors, no restatement). `Mem` re-proves the twelve load/store forms with the **cell as a parameter**. `Sp1Step`/`Sp1Text`/`Sp1Mem` are SP1's instances, including the code-window invariant a store guard needs. |
| `Decomp.Region.*` | Byte regions: `bytesRegionOn`, the `LBU`/`SB` keystones at an index and at an immediate offset, the same-register load form, and the wide `SW`/`SD`/`SH` stores. |
| `Decomp.Sp1.*` | SP1's ABI as triples: `HALT`, `COMMIT`, `COMMIT_DEFERRED_PROOFS`, `HINT_LEN`, `HINT_READ`. |
| `Decomp.Reject` | Showing a region *cannot* accept — the trapping half, on the observation that distinguishes a halt from a trap. |
| `Decomp.Examples.*` | Worked instances: a countdown loop driven end to end on both backends from one proof; an index search with a mid-body `break` and a bottom exit, the two `inr` branches of one `RecB` body discharged against code; and the SP1-vs-ZisK ecall regression. |

## Why no fuel

The rule available upstream is `loopNatCert`, whose `fuel` must be a literal at
proof-construction time, whose certificate is a right-nested conjunction of
`fuel` copies of its obligations, and whose step bound grows linearly in it. A
loop whose trip count depends on its input cannot be stated there at all.

`cpsTotal_loop` takes no fuel and produces no bound. The trip count arrives as
the *index* of a `TerminatesIn` derivation and is eliminated by induction on it,
so the caller discharges termination with the same induction that proves the
abstract function correct. That is what TR-765 §2.7's four-line worked example
does, and it is why `Tailrec` reads the unfolding equation

    terminates f g s x = (g x ⇒ s x ∧ terminates f g s (f x))

as an inductive rather than a recursive definition.

One correction worth recording, because it looked fine on paper: a `Prop`-valued
`Terminates` with a trip count read off the derivation is **not definable** —
that is large elimination from a non-subsingleton `Prop`. The trip count is an
index instead, which keeps the extracted function total, computable and
proof-free.

## Observations

What a judgement *observes* is where this library has most nearly gone wrong, so
it is worth stating plainly.

`cpsHalt` observes `(st.next s').isNone` — the machine cannot step. Under
`stepSp1` that is true in **five** distinct situations: no code at the pc, a
`.CSRS`, an `.EBREAK`, a memory access failing `memOkSp1`, and `sp1Ecall = none`,
which is where the real `HALT` lives. Nothing in the postcondition records which.

So a **trap** with `a0 = 0` satisfies `cpsHalt` exactly as an accepting `HALT`
with exit code `0` does. That is fatal for a reject-path argument — the cheapest
case, an instruction the loader could not decode, becomes unprovable rather than
definitional — and it is less faithful than the alternative, since a prover's
public values come out of the halt syscall and an illegal instruction yields no
proof at all.

`SyscallHalted s := s.code s.pc = some .ECALL ∧ s.getReg .x5 = 0` pins the
reason, `cpsSyscallHalt` is the judgement over it, and
`cpsHalt_of_cpsSyscallHalt` shows nothing is lost. `cpsHalt` is kept for callers
that only need "the machine stops here", with its doc comment now saying what it
does not say.

## Module system

Every file is a Lean `module`, with `public import` and an `@[expose] public
section` -- the same convention `riscv-zkvm` uses, so a downstream `rfl` on a
definition here keeps working. Two consequences worth knowing:

- A `module` cannot import a legacy file, and `riscv-zkvm`'s two aggregators
  (`RiscvZkvm.Rv64`, `RiscvZkvm.Rv64.Logic`) are legacy. `Decomp.Upstream`
  re-exports their *contents*, which are modules almost without exception, and
  is the only place upstream is named. The legacy files it cannot include are
  listed in its header; nothing here needs them.
- `#guard` evaluates, so a file whose checks *run* a definition needs a
  `meta import` of the module defining it -- transitively, down to whatever the
  interpreter has to call (`Sp1/HintRead.lean` needs three).

## Genericity, and what is deliberately *not* abstracted

`Stepper` abstracts the transition function and nothing else. `MachineState`,
`PartialState`, `Assertion`, `**`, `pcFree` and `CodeReq` are used unchanged
from `riscv-zkvm`, so every existing tactic — `xsimp`, `xperm`, `xcancel`,
`run_block` — keeps operating on the same syntax, and a `Stepper` is a *value*
whose `next` is a field projection `simp` unfolds. There is no abstraction
overhead to normalise back out.

Abstracting `Rv64.Logic` itself over a machine would cost all of that:
`PartialState.mem` is doubleword-addressed and ~20k lines of assertions are over
concrete `MachineState`/`Instr`/`Reg`.

`Backend` is a closed `inductive {zisk, sp1}` upstream, so quantifying over it
does not make room for a third backend — adding one is an upstream edit to a
datatype every `match` must then handle. A new backend here supplies a two-field
structure literal.

## Trust

Every declaration under `Decomp` and `DecompTools` rests on exactly three axioms:
`propext`, `Classical.choice`, `Quot.sound`. `scripts/check-axioms.sh` reads what
the kernel actually recorded, rather than trusting this paragraph;
`scripts/check-forbidden-tactics.sh` is the fast source scan that keeps
`native_decide` and `bv_decide` out.

Outside that, and not reduced by anything here:

- **The RV64 model.** `decode`, `step`, `stepSp1` and the SP1 precompiles come
  from `riscv-zkvm`, pinned by `lake-manifest.json`. `decode` is not tied to
  Sail's `encdec_backwards`, and the precompiles are `Accel` functions with no
  statement relating them to a group law.
- **The loader.** `Interpreter.load` is imperative (`Id.run do` over `HashMap`s).
  A downstream project that needs "this image, loaded, satisfies the invariant"
  discharges it by *evaluating* a predicate, not by proving a theorem.
- **`COMMIT` is under-observed.** `PartialState` has no `committed` component, so
  the `COMMIT` triple says "`pc += 4` and nothing else observable changed" —
  true, and weak. Harmless for a guest that commits nothing; a real obligation
  for one that does.

`ROADMAP.md` has the rest, including what is missing rather than merely trusted.

## Building on it

The shape a downstream project instantiates:

1. Emit the code as `Program` literals and a `CodeReq`; tie them to the binary
   with a regeneration gate, since `Program` is what the triples talk about.
2. Pick the stepper. `Sp1Text lo hi` is SP1 confined to a code window — the
   invariant a store guard needs.
3. Prove the code-window invariant of the loaded state by evaluation, once.
4. State the region assertions for the memory the code touches
   (`bytesRegionSp1`), and the `OffText` discharges for its heap and stack.
5. Build blocks from leaves, loops from `cpsTotal_loopB`, and the accept path
   from `cpsSyscallHalt`.

`zip-2005-asm` does all five; its `Examples/Guest*.lean` are the reference.

## Licence

None yet — ask before depending on this.
