/-
  DecompTools.AxiomSweep -- kernel-truth axiom gate for this repository's own Lean.

  Ported in spirit from `riscv-zkvm`'s `scripts/AxiomSweep.lean`, which audits
  *its* libraries and says nothing about ours. Without it the axiom policy would
  be `AGENTS.md` prose and nothing else.

  Like upstream's, this is a **policy** gate rather than a name-by-name
  baseline: a baseline churns on every refactor without saying anything new,
  while the set of axioms a library rests on is the actual trust statement. So:
  walk every declaration under the audited prefixes, collect its axiom
  dependencies, and fail if anything outside the documented set appears.

  It complements `scripts/check-forbidden-tactics.sh`, which is a fast source
  scan. This one reads what the kernel actually recorded, so it also catches a
  `sorry`, a forbidden tactic hidden behind a macro, and any new axiom a
  `riscv-zkvm` pin bump drags into our proofs.

  Run after `lake build`; it imports the built oleans.

    lake build axiomsweep
    .lake/build/bin/axiomsweep            # enforce
    .lake/build/bin/axiomsweep --report   # print the census, exit 0

  `scripts/check-axioms.sh` is the wrapper.
-/

import Lean

open Lean

/-- Declarations under these prefixes are audited: everything this repository
    owns. -/
def scanPrefixes : List Name := [`Decomp, `DecompTools]

/-- Modules to import. These two roots transitively cover the whole owned
    tree. -/
def scanModules : Array Import :=
  #[{ module := `Decomp }, { module := `DecompTools }]

/-- The axioms this repository accepts, and why.

    Change this list only alongside README "Trust": it *is* the
    machine-readable form of that section. Note what is
    **not** here -- `sorryAx`, `Lean.ofReduceBool` and `Lean.trustCompiler` --
    and that the spec side's one documented exception,
    `CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt`, is an *inherited*
    `native_decide` on the other side of M1a and so cannot appear in this
    census. If it ever does, §6's accounting has changed. -/
def allowedAxioms : List Name :=
  -- Lean's three classical axioms, and nothing else.
  --
  -- Deliberately **not** the four Sail platform axioms (`load_reservation`,
  -- `match_reservation`, `plat_term_write`,
  -- `sys_enable_experimental_extensions`) that README "Trust" lists
  -- as inherited from `riscv-zkvm`'s generated extraction. Measured with
  -- `--report`, **no declaration here depends on any of them**: nothing we
  -- prove reaches the `SailEquiv` layer, only `step`/`stepOn` themselves. So
  -- leaving them in the allow-list would let a proof start resting on them
  -- silently. If one legitimately needs them, add it back here *and* in §6, in
  -- the same change, and say which theorem needed it.
  [`propext, `Classical.choice, `Quot.sound]

def isScanned (n : Name) : Bool :=
  scanPrefixes.any (fun p => p.isPrefixOf n) && !n.isInternal

def main (args : List String) : IO UInt32 := do
  let report := args.contains "--report"
  initSearchPath (← findSysroot)
  let env ← importModules scanModules {} (trustLevel := 1024)
  let ctx : Core.Context := { fileName := "<axiomsweep>", fileMap := default }
  let state : Core.State := { env }

  let run : CoreM (Nat × NameMap (Array Name) × NameMap (Array Name)) := do
    let mut audited := 0
    let mut offenders : NameMap (Array Name) := {}
    let mut census : NameMap (Array Name) := {}
    for (n, _) in (← getEnv).constants.toList do
      unless isScanned n do continue
      audited := audited + 1
      let axs ← collectAxioms n
      unless axs.isEmpty do census := census.insert n axs
      let bad := axs.filter (fun a => !allowedAxioms.contains a)
      unless bad.isEmpty do offenders := offenders.insert n bad
    return (audited, offenders, census)

  let ((audited, offenders, census), _) ← run.toIO ctx state

  let offList := offenders.toList
  if report then
    -- Which of the allowed axioms are actually used, and by how many
    -- declarations. This is the number README "Trust" should quote.
    IO.println s!"== Axiom sweep over {scanPrefixes} =="
    IO.println s!"   declarations audited:        {audited}"
    IO.println s!"   resting on some axiom:       {census.toList.length}"
    IO.println s!"   allowed axioms:              {allowedAxioms}"
    for a in allowedAxioms do
      let uses := census.toList.filter (fun (_, axs) => axs.contains a)
      IO.println s!"     {a}: {uses.length} declaration(s)"
    IO.println s!"   offenders:                   {offList.length}"
    for (n, axs) in offList do
      IO.println s!"     {n}: {axs.toList}"
    IO.println "\n(report mode -- exit 0)"
    return 0

  if offList.isEmpty then
    IO.println s!"axiomsweep: OK -- {audited} declarations rest only on the \
      {allowedAxioms.length} documented axioms."
    return 0

  IO.eprintln "axiomsweep FAILED: declaration(s) depend on an undocumented axiom:"
  for (n, axs) in offList do
    IO.eprintln s!"  {n}"
    IO.eprintln s!"    {axs.toList}"
  IO.eprintln "\nIf this is `sorryAx`, a proof is incomplete -- which is allowed \
    while it is grep-able, but not in a gated build. If it is \
    `Lean.ofReduceBool` / `Lean.trustCompiler`, a TCB-expanding tactic got in \
    (see scripts/check-forbidden-tactics.sh). If a `riscv-zkvm` pin bump \
    introduced a new platform axiom, add it to `allowedAxioms` AND to \
    the README's Trust section, in the same change."
  return 1
