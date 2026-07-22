#!/usr/bin/env bash
# Fails if the optimizer's correctness proof is not fully machine-checked:
#   1. no `sorry` / `admit` / `native_decide` / `axiom` in the Lean sources,
#   2. the top-level correctness theorems depend only on Lean's three standard axioms, and
#   3. no human-written theorem is unused (unreachable from the correctness theorems).
# Run from the repo root (CI runs it after `lake build`).
set -euo pipefail

echo "==> Checking sources for forbidden tactics/axioms"
if grep -rnE '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' \
     ApcOptimizer Main.lean ApcOptimizer.lean; then
  echo "ERROR: found sorry/admit/native_decide/axiom above." >&2
  exit 1
fi

echo "==> Checking axiom dependencies of the correctness theorems"
out=$(lake env lean Scripts/CheckAxioms.lean 2>&1)
echo "$out"
if echo "$out" | grep -qE 'sorryAx|ofReduceBool|trustCompiler'; then
  echo "ERROR: a correctness theorem depends on a forbidden axiom." >&2
  exit 1
fi

echo "==> Checking for unused theorems (seeded by Scripts/unused-theorems.txt)"
lake env lean Scripts/UnusedTheorems.lean

echo "OK: proof integrity checks passed."
