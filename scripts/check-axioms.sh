#!/usr/bin/env bash
# Axiom gate: what the kernel actually recorded for this repository's own Lean.
#
# `Tools/AxiomSweep.lean` walks every declaration under `Decomp` and `Tools`,
# collects its axiom dependencies, and fails on anything outside the documented
# set (`propext`, `Classical.choice`, `Quot.sound` -- see README "Trust") -- so a
# `sorry`, a forbidden tactic behind a macro, or a new axiom arriving with a
# `riscv-zkvm` pin bump all fail the build instead of being noticed later.
#
# Usage:
#   scripts/check-axioms.sh            # enforce; exit 1 on an undocumented axiom
#   scripts/check-axioms.sh --report   # print the census, exit 0
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# The sweep imports the built oleans, so the libraries have to exist; and
# `lake env` is what puts them on LEAN_PATH -- the bare binary cannot find
# `Decomp.olean` on its own.
lake build Decomp Tools axiomsweep >/dev/null
exec lake env ./.lake/build/bin/axiomsweep "$@"
