#!/usr/bin/env bash
# Build the library and the checks, then require the standard axioms only.
# Exit status: 0 pass; 1 build failure; 2 an unexpected axiom (including sorryAx).
set -u
cd "$(dirname "$0")/.."
lake build IrrationalitySequences Challenge Verification || exit 1
out=$(lake env lean Verification/Axioms.lean) || exit 1
echo "$out"
expected="depends on axioms: [propext, Classical.choice, Quot.sound]"
n=$(printf '%s\n' "$out" | grep -c "depends on axioms")
ok=$(printf '%s\n' "$out" | grep -cF "$expected")
if [ "$n" -ne 2 ] || [ "$ok" -ne 2 ]; then
  echo "verify: unexpected axioms (expected two theorems with exactly propext, Classical.choice, Quot.sound)" >&2
  exit 2
fi
echo "verify: PASS"
