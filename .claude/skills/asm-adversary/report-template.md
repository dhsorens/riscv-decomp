# Report template

Write the report in this shape. No finding without a citation to a
definition, function body, `Program` literal, or run.

```markdown
# Adversarial statement / machine / observation report

Focus: <all | $ARGUMENTS>
Roadmap read: ROADMAP.md (date / HEAD)
riscv-zkvm pin: <sha from lake-manifest.json>

## Outcome

<one paragraph: did it succeed? highest finding?>

## Findings

### F1. <short title>
- Severity: soundness-hole | vacuous-theorem | model-bug | incompleteness
- Sides: statement / machine / observation
- Statement: <theorem, as written>
- Machine: `<path>` / `<def>` / run
- Observation: <halt glue / triple pre/post>
- Accepts differently: <witness or run sketch, or "same set">
- Vacuous?: <yes/no + why>
- Why this is / is not a known hole:

### F2. ...

## Claim join table

One row per statement audited. Add rows for the observation and for any
rule the statement leans on.

| Name | Statement | Machine | Observation | Verdict |
|---|---|---|---|---|
| <theorem> | | | | |
| accept vs halt | | | | |
| cell inhabited | | | | |
| frame / footprint | | | | |
| side condition | | | | |

## Hunt-list coverage

For each item in hunt-list.md: checked / skipped, one line.

## Unexamined surface

What was not chased (interpreter files, functions, runs).

## Negative result (only if zero findings)

List every claim checked. State why the audit is still incomplete.
Do not conclude "they match."
```
