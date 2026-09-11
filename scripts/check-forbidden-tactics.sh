#!/usr/bin/env bash
#
# check-forbidden-tactics.sh -- source-level gate forbidding proof tactics that
# expand the trusted computing base.
#
# Ported from `riscv-zkvm`'s gate of the same name. Upstream gates its own tree,
# which says nothing about ours.
#
# Why it exists: every proof here is meant to be kernel-checkable, resting on
# Lean's three classical axioms and nothing else (README "Trust"). Two tactics
# break that by sealing their result behind a native-compiler trust axiom
# (`Lean.ofReduceBool` / `Lean.trustCompiler`) instead of a proof term:
#
#   * `native_decide` -- trusts arbitrary compiled `Decidable` evaluation;
#   * `bv_decide`     -- reflects an LRAT checker run via native evaluation.
#
# `#guard` is deliberately NOT forbidden: it evaluates at elaboration time and
# produces no proof term, so it adds no axiom. Several `#guard`s here pin
# generated data and that is the right tool.
#
# Scope: this repository's own Lean. `.lake/` is excluded explicitly rather than
# by hoping it is absent -- dependencies gate themselves, and a scan directory
# that has ever been built otherwise drags every `native_decide` in Mathlib's
# test suite into the report.
#
# Doc mentions are allowed: a token inside `backticks` or on a `--` comment line
# is not flagged. A real tactic invocation is never backtick-wrapped.
#
# Usage:
#   scripts/check-forbidden-tactics.sh           # enforce; exit 1 on any hit
#   scripts/check-forbidden-tactics.sh --report  # list hits, exit 0

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

FORBIDDEN="native_decide bv_decide"
SCAN_DIRS="Decomp Refine DecompTools"

mode="enforce"
case "${1:-}" in
  "")       mode="enforce" ;;
  --report) mode="report" ;;
  *) echo "usage: $0 [--report]" >&2; exit 2 ;;
esac

alt="$(echo "$FORBIDDEN" | tr ' ' '|')"

dirs=()
for d in $SCAN_DIRS; do [[ -d "$d" ]] && dirs+=("$d"); done
if (( ${#dirs[@]} == 0 )); then
  echo "check-forbidden-tactics: no scan directories present" >&2; exit 2
fi

hits="$(
  grep -rnE "(^|[^\`A-Za-z_])(${alt})([^\`A-Za-z_]|\$)" --include='*.lean' \
      --exclude-dir='.lake' "${dirs[@]}" 2>/dev/null \
    | grep -vE "\`(${alt})\`" \
    | grep -vE '^[^:]*:[0-9]+:[[:space:]]*--' \
    || true
)"

if [[ "$mode" == "report" ]]; then
  echo "== Forbidden-tactic scan over ${SCAN_DIRS} =="
  echo "   forbidden: ${FORBIDDEN}"
  echo
  if [[ -n "$hits" ]]; then echo "$hits"; else echo "  (none)"; fi
  echo
  echo "(report mode -- exit 0)"
  exit 0
fi

if [[ -n "$hits" ]]; then
  echo "$hits" >&2
  n="$(printf '%s\n' "$hits" | grep -c . || true)"
  cat >&2 <<EOF

==================================================================
check-forbidden-tactics FAILED: $n invocation(s) of a TCB-expanding
tactic (${FORBIDDEN}) found in ${SCAN_DIRS}.

These seal their result behind a native-compiler trust axiom
(Lean.ofReduceBool / Lean.trustCompiler) rather than a kernel-checked
proof term, widening the trusted base the README accounts for.
AGENTS.md forbids them outright.

Replace with a kernel-checkable proof (decide / omega / simp /
bv_omega / ...), or -- if the goal is to pin generated data rather
than to prove something -- with a \`#guard\`, which evaluates without
producing a proof term. If you only meant to MENTION the tactic in
prose, wrap it in \`backticks\`.
==================================================================
EOF
  exit 1
fi

echo "check-forbidden-tactics: OK -- no ${FORBIDDEN} invocations in ${SCAN_DIRS}."
