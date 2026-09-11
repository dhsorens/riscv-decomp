# Plan verification slices

You are a **planner** for this repo. Create a small set of atomic next
work items — do **not** implement them unless the user explicitly asks
to continue into execution.

## Orient

1. Read `ROADMAP.md` — the work queue: what is being worked, what is done.
2. Read `README.md` — the roadmap it points at, for the contract and
   the acceptance criteria of whichever milestone the queue item sits in. Both
   are still being written; use what they say *today*.
3. Skim `ROADMAP.md's Known gaps` / coverage docs if they exist.
4. Skim `AGENTS.md`.

## Sizing rules

Each work item must be **one logical concern**:

- one plan acceptance criterion, **or**
- one Recovery conjunct / one function / one relation prerequisite
- never span two plan milestones in one item

When in doubt, split. Prefer a hole that can falsify the claim over a
hole that only adds lemmas.

## Item template

```markdown
### Title
<specific>

### Current state
- What the plan says; relevant theorems, mismatch ids, files

### Deliverables
1. …
2. …
3. …   # max 3

### Attack first
- `asm-adversary` / neither (why)

### Context
- Files to read first; observation boundary if relevant

### Verification
- `lake build` if Lean
- living doc / mismatch row updated
```

## How many

Default: **1–3** items, ordered by dependency. End with the single
recommended first item to execute via `/work`.

Present the items in chat. Write GitHub issues only if the user asks.
**No PR.**
