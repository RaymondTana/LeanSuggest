#!/usr/bin/env bash
# End-to-end test for LeanSuggest's cross-file search + import resolution.
#
# Builds the engine and the `Fixture` test library, runs `test/Demo.lean`, and asserts the
# suggestions name the right lemmas AND the `import` to add — the behaviour
# `exact?`/`apply?`/`rw?` cannot provide. Exits non-zero on any miss.
#
# No `LEANSUGGEST_ROOTS` is set: this exercises the *zero-config* path, where the search
# roots are auto-discovered from `[[lean_lib]]` entries in lakefile.toml (which includes
# `Fixture`). Pass it explicitly to test the override path instead.
set -uo pipefail
cd "$(dirname "$0")/.."

echo "── building LeanSuggest + Fixture ──"
lake build LeanSuggest Fixture || { echo "FAIL: build failed"; exit 1; }

echo "── running test/Demo.lean (zero-config: roots auto-discovered from lakefile.toml) ──"
out=$(lake env lean test/Demo.lean 2>&1)
status=$?
echo "$out"
echo "────────────────────────────────────────────────────────"

fail=0

# A genuine elaboration error fails the test; `sorry` warnings are expected and fine.
if echo "$out" | grep -qE '^.*: error:'; then
  echo "FAIL: Demo.lean produced an elaboration error"
  fail=1
fi

# Each `check <label> <substring>` asserts the run output contains <substring>.
check() {
  if echo "$out" | grep -qF "$2"; then
    echo "  ok   — $1"
  else
    echo "  MISS — $1  (expected to find: $2)"
    fail=1
  fi
}

echo "── assertions ──"
# 1. EXACT cross-file: the closer + its import.
check "exact closer found"          "Fixture.isShiny_all"
check "exact closer import"         "import Fixture.Lemmas"
# 2. APPLY partial cross-file: the lemma applied, leaving its premise.
check "apply partial found"         "apply Fixture.sparkly_of_shiny"
# 3. RW cross-file (the new feature): the rewrite + its import.
check "rw lemma found"              "rw [Fixture.frob_eq]"
# 4. Local hypothesis discharged cross-file.
check "local-hyp closer found"      "Fixture.sparkly_of_shiny h"
# 5. Closed-tactic (hint-style) panel: a core tactic closes the goal, no import.
check "hint tactic closer found"    "1. omega"

# Golden tests: `test/Guarded.lean` pins exact #suggest output via #guard_msgs; it elaborates
# silently iff every message matches (a drift makes it fail to elaborate, with a diff).
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
