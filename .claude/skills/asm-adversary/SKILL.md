---
name: asm-adversary
description: >
  Adversarial audit of a decompilation judgement, rule, leaf or
  observation against the RV64/SP1 machine. Succeeds by finding
  soundness holes, vacuous statements, or model bugs. Use when the
  user asks to attack, adversarially audit, or hard-diff a triple, a
  loop rule, a region keystone, or an observation.
disable-model-invocation: true
effort: xhigh
context: fork
background: false
argument-hint: "[focus-area]"
---

ultrathink

# Property / machine / observation adversary

Compare three artifacts on the formal stack. Comments are not evidence.
Success is a discrepancy backed by a definition, a `Program` literal, a
`step`/`Accel` body, or a run. A clean match is a negative result to
distrust.

This library states judgements about a machine. The hunt is whether a
statement is *weaker than it reads* — vacuous, or true of a machine that
is not the one that runs — and whether anything the model observes as
accept actually implies what the caller will read it as.

Optional focus: $ARGUMENTS

Do not invent a new judgement during an audit; attack the statement that
exists, or the one `ROADMAP.md` names.

## Stance

1. **Success = a discrepancy with evidence.** "The run halted" and
   "the triple typechecks" are not findings.
2. **Soundness holes are the highest prize.** Accept without the
   property outranks "the guest is incomplete."
3. **Vacuous theorems are the next prize.** A restricted relation, an
   unused hypothesis, or an undischarged side condition that excludes
   reachable states is a failure of the claim, not a successful proof.
4. **Ignore comments.** `README.md`, `ROADMAP.md`, theorem
   docstrings, are claims to verify.
5. **Chase callees.** `decode`, `step`, `stepSp1`, `sp1Ecall`,
   `memOkSp1` and the cell predicates are the comparison — not the
   call site in a docstring.

Majority vote when two sides agree:

- Statement + machine vs observation → the theorem is about a different
  event than the caller will read it as
- Statement + observation vs machine → model bug, or a leaf that is not
  the instruction it names
- Machine + observation vs statement → the statement is weaker, or
  vacuous, or its precondition has no inhabitant

## Preconditions

Abort only if `Decomp/` or the Lake `riscv-zkvm` checkout is missing.

Do not invent statements from an index or from a docstring.

Read [surfaces.md](surfaces.md) for the file map and chase rules.
Read [known-incomplete.md](known-incomplete.md) before scoring.
Read [hunt-list.md](hunt-list.md) before Pass 4.
Use [report-template.md](report-template.md) for the output.

## Four isolated passes

Do not look at the other sides during passes 1–3.

**Pass 1 — Statement only.** What does the theorem say, with every
`def` and `abbrev` unfolded? What must a caller own, and what does the
postcondition fail to mention? Ignore docstrings.

**Pass 2 — Machine only.** What do `step` / `stepSp1` / `sp1Ecall` /
`memOkSp1` / the cell predicates actually do? Read bodies. Do not read
the theorem comment.

**Pass 3 — Observation only.** What event does the judgement observe,
and what will a downstream caller read it as? `cpsHalt` vs
`cpsSyscallHalt`, what a frame does and does not preserve, which
`stepSp1` arm the statement means by "cannot step".

**Pass 4 — Join and attack.** For each claim, fill one row:

```text
Name:
Statement:     (theorem, unfolded)
Machine:       (step / cell predicate / leaf)
Observation:   (judgement + pre/post)
Reads differently?:
Vacuous?:      (uninhabited cell, unused hyp, side condition, inv)
Verdict: match | mismatch | vacuous | model-gap | unknown
```

Then walk [hunt-list.md](hunt-list.md). A skill that reports "aligned
except known TODOs" is still comment-following.

## Scoring

Highest first. Do not re-score items in
[known-incomplete.md](known-incomplete.md) unless the finding goes
beyond the known hole.

1. **soundness-hole** — a theorem that holds of a machine other than the
   one that runs, or an observation a caller may satisfy without the
   event the theorem names
2. **vacuous-theorem** — precondition with no inhabitant at the addresses
   a caller will use; side condition never discharged; unused hypothesis;
   an `inv` no reachable state satisfies
3. **model-bug** — a leaf that is not the instruction it names, a cell
   predicate misread, a backend disagreement
4. **incompleteness** — only if new relative to known-incomplete.md

No finding without a cited definition or function body.
If $ARGUMENTS names a focus area, finish that area first, then the rest.
