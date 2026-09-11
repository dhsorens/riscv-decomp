# Review wire format

Posted as the `gh pr review` body (and copied into the reviewer session
summary). A worker parses this block; do not hide the fields in prose.

No finding without a citation to a definition, a function body, a
`Program` literal, a `#guard`, or a gate log.

```markdown
## Review

PR: <url>
HEAD: <sha>
Claimed half: statement | consumer | finding | docs
Roadmap item (as of <date / base HEAD>): <today's acceptance line, or "none">
Gates: lake <OK|FAIL> / axioms <OK|FAIL> / tactics <OK|FAIL>
Adversary: ran by user | still owed (<name>) | not applicable

### Findings

Highest first. At most three. Empty only on MERGEABLE, and then the
negative-result list below is required.

1. [<class>] <theorem or file:line>
   Evidence: <citation>
   Do not: <forbidden fix>
   Do: <the /work-legal move>

### Verdict

CHANGES-REQUESTED | MERGEABLE | ESCALATE

### Worker turn

(only on CHANGES-REQUESTED; omit otherwise)

Goal: <one sentence>
Attack first: yes (<name>) | no
Do not: <forbidden fix>
Done when: <one line>
```

## Classes

| class | means | worker does |
| --- | --- | --- |
| `soundness` | theorem holds of a machine that is not the one that runs | stop proving; record the hole |
| `vacuous` | precondition uninhabited, unused hyp, side condition that excludes reachable states | stop proving; record the hole |
| `observation` | a trap or the wrong event satisfies the judgement | stop proving; record the hole |
| `finding` | same family, when the reviewer is redirecting a proof-in-progress | stop proving; write `ROADMAP.md` + file header |
| `honesty` | Lean and `README.md` / `ROADMAP.md` / headers / PR body disagree | make the docs match the Lean; do not change the theorem to match the claim |
| `hygiene` | unused hyp, `sorry`, silent weaken, Lake-checkout edit | tighten; never shrink the domain |
| `scope` | claimed half is not the half that landed | reduce the claim, or land the missing half |
| `gate` | `lake build` / axiom census / forbidden tactic | fix the gate; do not weaken the statement to get green |

`soundness` / `vacuous` / `observation` on a PR that then "repairs" the
theorem by restricting it is `ESCALATE`, not another `CHANGES-REQUESTED`.

## Verdicts

| verdict | worker | reviewer |
| --- | --- | --- |
| `CHANGES-REQUESTED` | same branch; the Worker turn is the goal | wait; re-review the new HEAD |
| `MERGEABLE` | stop; next bare `/work` reads `ROADMAP.md` | squash-merge only after a fresh HEAD read still says `MERGEABLE` |
| `ESCALATE` | stop | do not merge; do not write a Worker turn |

## Negative result (MERGEABLE only)

List every claim checked. State why the review is still incomplete.
Do not conclude "they match." A clean merge is a negative result to
distrust, not a proof that the statement is as strong as it reads.
