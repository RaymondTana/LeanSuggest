/-!
# Fixture definitions (E2E test support)

A consumer (`test/Demo.lean`) imports THIS module so it can *state* goals about these
symbols — but it does NOT import `Fixture.Lemmas`, where the actual lemmas live. That gap
is exactly what `suggest?`/`#suggest` close: find the lemma in the unimported module and
report the `import` to add.

`IsShiny`/`IsSparkly` are `opaque`, so nothing in Lean core (and no `rfl`/`solve_by_elim`)
can discharge a goal about them — only a lemma we proved can. That isolates the genuine
cross-file case from "the standard library already has it".
-/

namespace Fixture

/-- An opaque project predicate. Nothing in core mentions it. -/
opaque IsShiny : Nat → Prop

/-- A second opaque predicate, only ever derivable FROM `IsShiny` (see `Fixture.Lemmas`),
    so closing a goal about it forces using an `IsShiny` hypothesis. -/
opaque IsSparkly : Nat → Prop

/-- A concrete operation we prove a rewrite lemma (`frob_eq : frob n = n + n`) about in
    `Fixture.Lemmas`. Defined as `2 * n` (NOT `n + n`) so that `frob n = n + n` is a genuine
    lemma, not `rfl`: a goal mentioning `frob` is therefore not closed in-scope by `rfl`/
    `exact?`, but a `rw [frob_eq]` from the unimported module rewrites it away. -/
def frob (n : Nat) : Nat := 2 * n

end Fixture
