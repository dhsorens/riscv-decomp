---
name: work
description: >
  Contribute one verification slice: pick the next hole in the living
  plan, attack first, prove only if the statement still looks sound,
  leave coverage honest, open a PR. Use when the user says /work, do
  what's next, make progress on verification, or contribute a slice.
disable-model-invocation: true
argument-hint: "[goal]"
---

# Work — contribute a slice

You are a **worker** session. Execute one coherent contribution toward
guest-vs-spec soundness, leave artifacts honest, and **open a pull
request** with the result.

Do **not** reimplement rituals here — load the skills this file names.

Start at [`ROADMAP.md`](../../../ROADMAP.md) — the work queue and the honest
list of what is missing. [`README.md`](../../../README.md) is the contract: what
the library claims, what it observes, what it trusts. Both are still being
written. Read them; do not assume a frozen item list from memory.

Optional goal: $ARGUMENTS

## Goal selection

**If the user passed a goal** (text after `/work`, e.g. `/work M1`,
`/work commit_ivk`, `/work attack leaf`): that is the goal. Clarify
only if it is ambiguous between two deliverables.

**If no goal was given** (bare `/work` / "do what's next"):

1. Read `ROADMAP.md` — the queue and the known gaps; take the next item.
2. Read `README.md` — the contract as it stands *today*.
3. Take the first incomplete item the roadmap currently treats as next.
   Prefer a hole that can fail a claim over a hole that only adds lemmas:
   a rule nobody can use, a statement that may be vacuous, an observation
   that does not say what a caller will read it as.
5. Announce the chosen goal in one sentence before editing.

Do not invent progress from chat or from a stale status paragraph.

## Branch (before editing)

`/work` never lands slice work directly on `main`.

1. `git fetch origin` (if networked) and note current branch.
2. If you are on `main` (or detached / unrelated): create and check out
   `work/<short-slug>` from up-to-date `origin/main`.
3. If you are already on a `work/…` (or user-named feature) branch for
   this goal: keep it.
4. Announce the branch name with the goal.

## Orient (always)

Before editing Lean or the guest:

1. `AGENTS.md` — standing rules.
2. Skill `asm-bridge-gotchas` — if proving or debugging a triple, a leaf,
   a region keystone or a loop.
3. `ROADMAP.md`'s "Known gaps" — do not rediscover one.

## Dispatch

| Goal kind | Attack first | Then |
| --- | --- | --- |
| A judgement, rule, leaf, keystone or observation | `asm-adversary` on the proposed statement | tighten the statement, or record the finding |
| A new instruction leaf or region keystone | `asm-adversary` on the footprint | implement only if the precondition has inhabitants |
| A worked example against real code | `asm-adversary` | it is the rule's first consumer — say what it does *not* exercise |
| Docs / status only | — | update `README.md` / `ROADMAP.md`; no fake theorems |
| "Plan, don't code" | — | command `/plan-slice` — stop (**no PR**) |

Keep the slice **atomic**. If it balloons, stop after a compiling or
documented subset, open the PR for that subset, and note the residual
(or suggest `/plan-slice`).

## Execute

**Attack is required, not a fallback.**

1. Run the dispatched adversary skill(s). Isolated passes. Comments
   are not evidence.
   **If the skill refuses** — `asm-adversary` sets
   `disable-model-invocation`, so a worker session cannot invoke it and
   must not reproduce its workflow another way — then: do the
   ordinary review the slice needs (is the precondition inhabited?
   `#guard` it; do the addresses match the `Program` literal? `decide`
   it), name the statement most worth attacking, and say in the PR and
   the session summary that the pass is **still owed**. Never claim an
   attack ran. Prefer additive, reversible shapes (a new datatype
   beside the old, a new judgement beside the old) while it is
   outstanding, and say so.
2. If you find a soundness-hole, vacuous statement, or model-bug: write
   it into `ROADMAP.md`'s "Known gaps" using the adversary report shape,
   and into the affected file's header. **Stop proving.** The finding is
   the contribution.
3. Only if the statement still looks sound: implement toward the
   plan's current acceptance criterion for this item.
4. `lake build` on touched Lean — no new `axiom`s; no
   `native_decide` / `bv_decide`; clear unused-hyp warnings in files
   you touched (drop the hyp).
5. Do not claim a rule is usable until something uses it. A rule with no
   consumer is a statement, not a capability — say which half you landed.

## Ship: commit + pull request

After a contribution that changed the tree (Lean, docs, mismatches,
skills, …):

1. `git status` / `git diff` / recent `git log` — commit message is
   why, not a file list.
2. Stage intentional files only; commit on the `work/…` branch.
   No `Co-authored-by` trailer (Claude, Cursor, or otherwise).
3. `git push -u origin HEAD`.
4. Open or update a PR against `main` (`gh pr create` if none).
   Summary + test plan (`lake build`, both gates, which docs changed).
5. Put the **PR URL** in the session summary.

**Skip the PR** only when:

- Nothing landed (plan-only, user aborted, or attack with no file
  changes worth reviewing).
- The user explicitly said not to open a PR.

A `ROADMAP.md` gap entry **is** worth a PR. Do **not** merge unless the
user asks.

## Finish with `/reflect`

1. Summarize in a few bullets: goal, branch, what landed, theorem
   names or finding ids, **PR URL** (or "no PR: \<reason\>").
2. Run `/reflect` (`.claude/commands/reflect.md`). High-signal skill /
   `AGENTS.md` tweaks only.
3. Do not open follow-up work in the same turn unless the user asks.

## Off-limits

- No edits inside Lake's `riscv-zkvm` checkout to make a triple hold.
  Vendor the fix or send it upstream.
- Do not weaken a statement to make it provable without saying so in the
  file header and in `ROADMAP.md`.
- Do not commit slice work on `main`; do not force-push.
- Do not add a `Co-authored-by` trailer. Commits are the user's.
