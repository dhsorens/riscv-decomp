# Agent conventions — riscv-decomp

Standing rules. Rituals live in skills; this file is operational doctrine.

**Start at [`ROADMAP.md`](ROADMAP.md)** — the work queue and the honest list of
what is missing, read it each session. [`README.md`](README.md) is the contract:
what the library claims, what it observes, what it trusts.

Neither is frozen. Do not treat item names or section numbers as fixed from
memory; read them today.

## Proof hygiene

Prefer, in order:

1. a real semantic disagreement with the machine
2. a vacuous or false guarantee
3. a model / judgement / observation blind spot
4. a meaningful theorem with an explicit trust base
5. an honest unknown

A green proof of a weak statement is not progress. The characteristic failure in
this library is not a wrong theorem, it is a **true one that says less than it
reads**: a precondition with no inhabitant, a postcondition that drops what the
instruction changed, an observation that a trap satisfies.

- Never introduce an `axiom`. Unfinished proofs use `sorry` (grep-able).
- No `native_decide` / `bv_decide`. `#guard` is fine — it produces no proof term.
- Unused hypotheses mean the theorem is not tight — drop them.
- Do not edit the Lake `riscv-zkvm` checkout to make a triple hold. Vendor the
  fix or send it upstream.
- A rule with no consumer is a statement, not a capability. When you land one,
  say which half you landed.

## Skills and commands

| name | when |
| --- | --- |
| `/work` (`work`) | default contribute: attack, then maybe prove, then PR |
| `/plan-slice` | plan 1–3 items; do not implement |
| `/reflect` | after `/work`; skill hygiene only |
| `asm-adversary` | statement ≟ machine ≟ observation |
| `asm-bridge-gotchas` | proving or debugging a triple, leaf, region or loop |

`asm-adversary` sets `disable-model-invocation`: only the user can run it. A
worker session that cannot run it says so in the PR rather than faking a pass.

## Off-limits

- Do not claim a rule is usable, or a theorem discharged, from chat or from
  "many lemmas."
- Do not weaken a statement to make it provable without saying so in the file
  header and in `ROADMAP.md`.
- Do not land `/work` slice work on `main`.
- Do not add a `Co-authored-by` trailer. Commits are the user's.
