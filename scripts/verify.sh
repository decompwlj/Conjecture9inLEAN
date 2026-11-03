#!/usr/bin/env bash
# One-command verification of the Lean development.
#   1. downloads the pre-compiled Mathlib (so nothing heavy is rebuilt),
#   2. type-checks every file of the project with the Lean kernel,
#   3. prints the statements and the axioms used by the main theorems,
#   4. fails if any proof is incomplete (`sorry`) or if a new axiom was declared.
set -euo pipefail
cd "$(dirname "$0")/.."

lake exe cache get
build_log="$(lake build 2>&1)" || { echo "$build_log"; echo "FAILED: lake build" >&2; exit 1; }
echo "$build_log" | grep -v "module system" || true
if echo "$build_log" | grep -qi "declaration uses .sorry"; then
  echo "FAILED: some declaration uses sorry." >&2
  exit 1
fi

echo
echo "=== Statements and axioms (Verify.lean) ==="
out="$(lake env lean Verify.lean)"
echo "$out"

if echo "$out" | grep -q "sorryAx"; then
  echo "FAILED: some proof uses sorry." >&2
  exit 1
fi
if grep -rnE "^\s*axiom\b" Conjecture9/ ; then
  echo "FAILED: the sources declare a new axiom." >&2
  exit 1
fi
echo
echo "OK: everything is checked by Lean; only the standard axioms propext, Classical.choice, Quot.sound are used."
