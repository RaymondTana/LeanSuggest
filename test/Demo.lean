/-
Copyright (c) 2026 Raymond Tana. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raymond Tana
-/
import LeanSuggest
import Fixture.Defs

/-!
# `LeanSuggest` Demo
-/

open Fixture

/- 1. A cross-file `exact`.
   `IsShiny` is opaque, so nothing in scope closes this. The closer `isShiny_all`
   is in `Fixture.Lemmas`.
   EXPECT:  exact Fixture.isShiny_all    [add: import Fixture.Lemmas] -/
#suggest (∀ n, IsShiny n)

/- 2. A cross-file `apply`.
   Only `sparkly_of_shiny` matches, and it leaves the premise `IsShiny n` open
   (nothing in scope discharges it), so it's a partial `apply`. -/
#suggest (∀ n, IsSparkly n)

/- 3. A cross-file `rw`.
   `frob` is in scope (Defs) but its rewrite lemma `frob_eq` is not. `frob n` is the
   only rewritable subterm here, so the `rw` engine surfaces `frob_eq` from the
   constructed environment and reports the rewrite and the import. -/
#suggest (∀ n, IsShiny (frob n))

/- 4. Cross-file local hypotheses.
   The goal `IsSparkly n` is closed by `sparkly_of_shiny` applied to the local
   hypothesis `h : IsShiny n`. -/
example (n : Nat) (h : IsShiny n) : IsSparkly n := by
  suggest?
  sorry

/- 5. A closed-tactic suggestion.
   No named lemma is needed: a closed core tactic solves the goal outright. It's reported as
   the tactic to run, with no import, and ranks ahead of closers with required imports. -/
#suggest (∀ a b : Nat, a + b + 0 = b + a)
