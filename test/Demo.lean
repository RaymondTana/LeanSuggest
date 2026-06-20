import LeanSuggest
import Fixture.Defs   -- the symbols, but NOT `Fixture.Lemmas` (where the proofs live)

/-!
# End-to-end showcase

Run with the search pointed at the fixture library:

```
lake build LeanSuggest Fixture
LEANSUGGEST_ROOTS=Fixture lake env lean test/Demo.lean
```

Each example states a goal whose lemma lives in the UNIMPORTED `Fixture.Lemmas`.
`#suggest`/`suggest?` find it across the file boundary and report the `import` to add —
something `exact?`/`apply?`/`rw?` structurally cannot do (the lemma is out of scope).

The two `suggest?` examples end in `sorry`: the goal genuinely cannot be closed here (its
lemma is unimported), so `sorry` stands in for "click the lightbulb to add the import, then
the suggested tactic closes it". The `#suggest` commands have no proof obligation at all.
-/

open Fixture

/- ── 1. EXACT cross-file ─────────────────────────────────────────────────────
   `IsShiny` is opaque, so nothing in scope closes this. The closer `isShiny_all`
   is in `Fixture.Lemmas`.
   EXPECT:  exact Fixture.isShiny_all    [add: import Fixture.Lemmas] -/
#suggest (∀ n, IsShiny n)

/- ── 2. APPLY (partial) cross-file ───────────────────────────────────────────
   Only `sparkly_of_shiny` matches, and it leaves the premise `IsShiny n` open
   (nothing in scope discharges it) — so it's a partial `apply`.
   EXPECT:  apply Fixture.sparkly_of_shiny   (leaves 1: ⊢ ...IsShiny...)
            [add: import Fixture.Lemmas] -/
#suggest (∀ n, IsSparkly n)

/- ── 3. RW cross-file (the new feature) ──────────────────────────────────────
   `frob` is in scope (Defs) but its rewrite lemma `frob_eq` is not. `frob n` is the
   only rewritable subterm here, so the rw engine surfaces `frob_eq` from the
   constructed env and reports the rewrite + the import.
   EXPECT among the hits:  rw [Fixture.frob_eq]   (⊢ ∀ n, ...IsShiny (n + n))
            [add: import Fixture.Lemmas] -/
#suggest (∀ n, IsShiny (frob n))

/- ── 4. LOCAL HYPOTHESIS carried into the cross-file search ───────────────────
   The goal `IsSparkly n` is closed by `sparkly_of_shiny` applied to the LOCAL
   hypothesis `h : IsShiny n` — the search runs in the goal's local context.
   EXPECT:  exact Fixture.sparkly_of_shiny h    [add: import Fixture.Lemmas] -/
example (n : Nat) (h : IsShiny n) : IsSparkly n := by
  suggest?
  sorry
