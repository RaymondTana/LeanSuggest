import Fixture.Defs

/-!
# Fixture lemmas (the "other file" the consumer does NOT import)

These stand in for lemmas you proved elsewhere in your project. A file that imports
`Fixture.Defs` (for the symbols) but NOT this module cannot reach them with `exact?`/`rw?`
— they are out of scope. `suggest?`/`#suggest` find them in the constructed environment and
report `import Fixture.Lemmas`. (`axiom` here only stands in for a real proof; the point is
that the declaration lives in an unimported module.)
-/

namespace Fixture

/-- The established fact about `IsShiny` (used by the EXACT cross-file demo). -/
axiom isShiny_all : ∀ n, IsShiny n

theorem isShiny_zero : IsShiny 0 := isShiny_all 0

/-- The ONLY route to `IsSparkly` — so a goal `IsSparkly n` can be closed only by
    discharging the `IsShiny n` premise (used by the APPLY-partial and local-hypothesis
    demos). -/
axiom sparkly_of_shiny {n : Nat} : IsShiny n → IsSparkly n

/-- A rewrite lemma about `frob` (used by the RW cross-file demo). `frob n` is `2 * n`, so
    this is a genuine lemma (not `rfl`); only it rewrites `frob n` to `n + n`. -/
theorem frob_eq (n : Nat) : frob n = n + n := by unfold frob; omega

end Fixture
