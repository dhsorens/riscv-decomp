# Surfaces and chase rules

`ROADMAP.md` may rename things. Use this map as a starting point; verify
paths on disk.

## The three artifacts

| Side | Where | Role |
|---|---|---|
| Statement | the judgement, rule, leaf or keystone under audit, in `Decomp/` | What it claims |
| Machine | Lake `riscv-zkvm` — `decode`, `step`, `stepSp1`, `sp1Ecall`, `Accel.*`, `memOkSp1` | What actually runs |
| Observation | `cpsHalt` / `cpsSyscallHalt` / a triple's pre and post | What a caller will read the theorem as saying |

There is no ELF and no guest here. If the focus is a claim about a
*particular* image, that belongs downstream — audit the shape the library
gives it, not the image.

## Machine map

| Path | What to verify (do not trust the comment) |
|---|---|
| `RiscvZkvm/Rv64/StepOn.lean` | `stepSp1`, `sp1Ecall`, `memOkSp1`, `SP1_MAX_MEMORY`, every arm that returns `none` |
| `RiscvZkvm/Rv64/Step.lean` | `step`, `execInstrBr`, ecall dispatch |
| `RiscvZkvm/Rv64/Logic/SepLogic.lean` | `sepConj`, `memIsOn`, `regIs`, `CodeReq`, `pcFree` |
| `RiscvZkvm/Rv64/Logic/{Generic,Instruction,Syscall}Specs.lean` | the leaf specs this library transfers or mirrors |
| `RiscvZkvm/Rv64/Logic/MemRegion*.lean` | `bytesRegionOn` — note it owns **dword** cells |
| `Decomp/Leaf/*`, `Decomp/Region/*` | this library's own leaves and keystones |

Chase the checkout `lake-manifest.json` pins, not a random clone.

## Chase rules (statement)

- Unfold every `def` and `abbrev` in the statement. An `abbrev` that
  hides a `**` chain hides the footprint.
- A hypothesis that the proof never uses was restricting the domain;
  a hypothesis that *is* used may still be unsatisfiable.
- Read the proof before believing the statement is discharged.
- Ask what a caller must own. A precondition with fewer atoms than the
  instruction touches is either wrong or vacuous.

## Chase rules (machine)

- Unfold `stepSp1`'s arms. `none` means five different things; which one
  does the statement mean?
- A cell carries its own validity predicate. `↦ₘ` *requires*
  `isValidDwordAccess`; `memIsSp1` requires `isValidMemAddrSp1`. At an
  address outside the predicate's range the assertion has no inhabitant
  and every triple over it is vacuously true.
- `Sp1Text lo hi` and `Backend.stepper .sp1` have the same `next` and
  different `inv`. A theorem on the confined stepper says nothing about a
  state that fails `CodeWithin`.

## Chase rules (observation)

- Halted is not accepted, and `cpsHalt` cannot tell them apart:
  `(st.next s').isNone` is true of a `HALT` *and* of every trap.
  `SyscallHalted` pins the reason.
- A postcondition that mentions only `pc` and a register says nothing
  about memory, and a frame does not add anything back.
- Ask what the *downstream* caller will read the theorem as. That is the
  observation, even when this library has no run of its own.
