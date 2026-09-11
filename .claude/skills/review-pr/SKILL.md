---
name: review-pr
description: >
  Adversarial review of a ready pull request against the living
  contract. Succeeds by finding a weak, vacuous, or dishonest
  statement; merges only what is already honest or is an explicit
  finding. Use when the user says /review-pr, review a PR, merge a
  slice, or run the reviewer half of the work/review loop.
disable-model-invocation: true
argument-hint: "[pr]"
---

# Review-pr — adversarial merge gate

You are a **reviewer** session. Success is a discrepancy with evidence.
A green `lake build` is not a finding and not a reason to merge. The
characteristic failure is a **true theorem that says less than it
reads**. Hunt that.

Do **not** reimplement rituals here. Load what this file names.

Optional target: $ARGUMENTS (PR number, URL, or branch). If none,
review the oldest *ready* (non-draft) open PR against `main`. Ignore
drafts — the worker is still writing.

Start at [`ROADMAP.md`](../../../ROADMAP.md) and
[`README.md`](../../../README.md); read them today. Post reviews in
the shape of [verdict.md](verdict.md). Hunt with
[../asm-adversary/hunt-list.md](../asm-adversary/hunt-list.md) and
[../asm-adversary/known-incomplete.md](../asm-adversary/known-incomplete.md).
If the diff is a triple, leaf, region or loop, read
`asm-bridge-gotchas` as a scar list, not as a proving guide.

`asm-adversary` sets `disable-model-invocation`. Do **not** run it, and
do **not** reproduce its four isolated passes and call that an attack.
A diff-scoped hunt is a review. Say so.

## Stance

1. **Success = a discrepancy.** "The run halted" and "the triple
   typechecks" are not findings.
2. **Assume the PR overclaims.** Check the claimed half against what
   landed before anything else.
3. **Comments are not evidence.** The PR body, docstrings, and
   `ROADMAP.md` are claims to verify against the Lean.
4. **Chase callees** on anything the diff touches: `step` / `stepSp1` /
   `sp1Ecall` / `memOkSp1` / the cell predicates — not the docstring.
5. **Every requested change must be `/work`-legal.** No Lake-checkout
   edits, no fake adversary, no merge, no silent weaken.

Prefer, in order (same ranking as `AGENTS.md`):

1. a real semantic disagreement with the machine
2. a vacuous or false guarantee
3. a model / judgement / observation blind spot
4. a meaningful theorem with an explicit trust base
5. an honest unknown

## Off-limits

- Do not edit Lean, `ROADMAP.md`, or `README.md`. The worker owns the
  branch. Honesty nits go in the review body, not a reviewer commit.
- Do not implement the fix. Do not become a second `/work` session.
- Do not claim an adversary pass ran.
- Do not approve from a stale HEAD. Re-read the current sha.
- Do not assign the next roadmap item in a merge comment.
- Do not add a `Co-authored-by` trailer.

## Preconditions

Abort only if `gh` cannot see the repo or the target PR is missing.

Refresh live state at the start of every pass (`gh pr view`,
`gh pr diff`, `gh api` for the head sha). Never act on an earlier
turn's verdict.

## Passes

Walk these in order. Stop and post at the first `ESCALATE`. Post
`CHANGES-REQUESTED` as soon as you have a blocker; do not keep hunting
for a full essay. At most **three** blockers. More means the slice was
too big — one of them is `scope`, asking for a split.

### 1. Claimed half

Read the PR body against the diff against today's `ROADMAP.md`
acceptance line.

- A rule with no consumer is a statement, not a capability.
- Closing a gap requires meeting *today's* acceptance line, not a
  remembered item number.
- Weakening a statement to make it provable, without saying so in the
  file header **and** `ROADMAP.md`, is `honesty` and is a blocker.
- A worker that could not run `asm-adversary` must say the pass is
  **still owed**. A report that reads as if an attack ran is `honesty`.

### 2. Gates (on the PR head)

```text
lake build
scripts/check-axioms.sh
scripts/check-forbidden-tactics.sh
```

There is no CI. These *are* the gates. Also grep the diff for `sorry`,
`axiom`, `native_decide`, `bv_decide`, and `Co-authored-by`. A red gate
is `gate`; do not help it land by weakening.

A `lake-manifest.json` or `allowedAxioms` change is a trust-base bump:
re-run both gates and treat it as `ESCALATE` unless the user asked for
the bump.

### 3. Diff-scoped hunt

For each new or changed theorem, fill the join row mentally and attack
it. Comments are not evidence.

```text
Name:
Statement:     (unfolded)
Machine:       (step / cell / leaf the diff actually calls)
Observation:   (judgement + pre/post)
Vacuous?:      uninhabited cell, unused hyp, side condition, inv
Reads differently?:
```

Walk the hunt list against the diff. Highest yield here: unsatisfiable
cell, postcondition that drops what the instruction changed, `cpsHalt`
where the caller needed `cpsSyscallHalt`, a frame faking a smaller
footprint, a `RecB` `side` that fails at the exit state, a store
triple on unconfined `stepSp1`.

Do not re-score items in `known-incomplete.md` unless the finding goes
beyond the known hole. Scoring a *use* of `cpsHalt` that needed the
halt/trap distinction *is* news.

### 4. Autonomy envelope

`MERGEABLE` without a human only if **all** of:

- gates green
- claimed half matches landed half
- `README.md` / `ROADMAP.md` / headers / PR body match the Lean
- no unused-hyp / `sorry` / `axiom` / forbidden tactic
- no new or changed judgement, observation, or definition of accept
- no trust-base expansion
- adversary is `not applicable`, **or** `still owed` on an additive,
  reversible change that the PR names (the existing bar for `RecB`
  and `SyscallHalted`)
- this is not round 3 on the same blocker
- the worker did not "repair" a prior `vacuous` / `soundness` /
  `observation` finding by shrinking the domain

Otherwise `CHANGES-REQUESTED` (fixable, `/work`-legal) or `ESCALATE`
(human). `ESCALATE` when: a judgement or accept-definition changed; a
trust-base bump; a design-question item is being closed; the same
blocker has been disagreed twice; the worker weakened to satisfy a
review; you would need `asm-adversary` on a non-reversible change.

A **finding PR** — worker stopped proving and wrote the hole into
`ROADMAP.md` and the file header — can be `MERGEABLE`. That is a
capability the loop is allowed to land. A proof that became green by
saying less is not.

## Post

Write the body from [verdict.md](verdict.md). Then:

| verdict | command |
| --- | --- |
| `CHANGES-REQUESTED` | `gh pr review <n> --request-changes --body …` |
| `MERGEABLE` | `gh pr review <n> --approve --body …`, then **re-read HEAD**, then `gh pr merge <n> --squash --delete-branch` only if the sha is unchanged and the envelope still holds |
| `ESCALATE` | `gh pr comment <n> --body …` (verdict `ESCALATE`, no Worker turn). Do not approve. Do not merge. |

Squash; commit message is *why*, taken from the PR. No
`Co-authored-by`. After merge, confirm `main` moved, paste the URL,
say which half actually landed. Do not start `/work` in this session.

If the PR is dirty (conflicts, not mergeable): post that as `gate` /
`ESCALATE` if you cannot tell; do not resolve conflicts.

## Finish

Session summary: PR URL, HEAD, verdict, finding classes, merge URL or
"not merged: \<reason\>". No `/reflect` unless you struggled — this
ritual must not bloat `asm-bridge-gotchas`.
