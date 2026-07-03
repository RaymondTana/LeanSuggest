#!/usr/bin/env bash
# End-to-end test for LeanSuggest's cross-file search and import resolution.
#
# Builds the engine and the `Fixture` test library, runs `test/Demo.lean`, and asserts the
# suggestions name the right lemmas and the `import` to add. Exits non-zero on any miss.
#
set -uo pipefail
cd "$(dirname "$0")/.."

echo "── building LeanSuggest + Fixture ──"
lake build LeanSuggest Fixture || { echo "FAIL: build failed"; exit 1; }

echo "── running test/Demo.lean (zero-config: roots auto-discovered from lakefile.toml) ──"
out=$(lake env lean test/Demo.lean 2>&1)
echo "$out"
echo "────────────────────────────────────────────────────────"

fail=0

# An elaboration error fails the test. `sorry` warnings are expected and fine.
if echo "$out" | grep -q ': error:'; then
  echo "FAIL: Demo.lean produced an elaboration error"
  fail=1
fi

# Assert the run output contains a substring.
check() {
  if echo "$out" | grep -qF "$2"; then
    echo "  ok   — $1"
  else
    echo "  MISS — $1  (expected to find: $2)"
    fail=1
  fi
}

echo "── assertions ──"
# 1. Exact cross-file.
check "exact closer found"          "Fixture.isShiny_all"
check "exact closer import"         "import Fixture.Lemmas"
# 2. Apply partial cross-file.
check "apply partial found"         "apply Fixture.sparkly_of_shiny"
# 3. Rewrite cross-file.
check "rw lemma found"              "rw [Fixture.frob_eq]"
# 4. Local hypothesis discharged cross-file.
check "local-hyp closer found"      "Fixture.sparkly_of_shiny h"
# 5. Closed-tactic panel.
check "hint tactic closer found"    "1. omega"

# Deterministic tests in `test/Guarded.lean`.
echo "── running test/Guarded.lean (#guard_msgs golden tests) ──"
if gout=$(lake env lean test/Guarded.lean 2>&1) && [ -z "$gout" ]; then
  echo "  ok   — golden #guard_msgs match"
else
  echo "  MISS — golden tests drifted:"; echo "$gout"
  fail=1
fi

echo "────────────────────────────────────────────────────────"
if [ "$fail" -eq 0 ]; then
  echo "E2E PASS ✅"
  exit 0
else
  echo "E2E FAIL ❌"
  exit 1
fi
