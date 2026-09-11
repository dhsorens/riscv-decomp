# Self-reflection

Review the current conversation and identify where you **genuinely
struggled** and where additional prompting would have prevented the
issue.

Distinguish:

- **Successful adaptation** — figured it out and finished
- **Actual struggles** — repeated mistakes, user correction, or
  failed expectations

## Areas to consider

- Lean build / diagnostics in this repo
- Observation boundary, triples, ecall / decode / precompile traps
- Honesty of `README.md` / `ROADMAP.md` / ROADMAP gap notes vs chat
- Following `AGENTS.md` and project skills
- Attack-before-prove: was the adversary pass actually run?
- Review loop: did a bounce weaken a statement to satisfy `review-pr`?
- Tool usage and efficiency

## For each ACTUAL struggle

Only propose additions if:

1. The struggle caused real problems or required user intervention
2. Clearer prompting would have prevented it
3. The issue is likely to recur without guidance

Then:

1. Explain what happened and why it was problematic
2. Decide: `AGENTS.md` vs skill (`.claude/skills/`) vs command
3. Propose a **specific, concise** addition — prefer extending
   `asm-bridge-gotchas` or an adversary hunt list over a new skill

## Recognize success

If you adapted cleanly:

- Acknowledge what went well
- Note that no additional prompting is needed
- **Do not** propose changes just to document everything

Avoid prompt bloat.
