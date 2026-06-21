import LeanSuggest
import Fixture.Defs

/-!
# Golden (in-Lean) tests via `#guard_msgs`

Run it directly (roots are auto-discovered from `lakefile.toml`, which declares `Fixture`):

```
lake env lean test/Guarded.lean      # silent + exit 0 = all golden messages matched
```

It's also run as part of `test/e2e.sh`.

`#guard_msgs` pins the *exact* message a command/tactic emits: if a suggestion drifts,
**this file fails to elaborate** — the mismatch (with a diff) is the test failure. No shell,
no grep; it runs as part of `lake env lean` / `lake build`.

Only the **deterministic** cross-file cases live here: their goals mention `opaque` symbols,
so the standard library contributes no competing lemmas and the output is a stable, minimal
list. The noisy goals (arithmetic / the hint panel), whose suggestions include many
version-dependent core lemmas, are covered by substring assertions in `test/e2e.sh` instead —
pinning their full output would be brittle.
-/

open Fixture

/-- info: suggest? — suggestions (`exact`/`omega`/… close the goal; `apply`/`rw` transform it):
  1. exact fun n => Fixture.isShiny_all n    [add: import Fixture.Lemmas]
-/
#guard_msgs in
#suggest (∀ n, IsShiny n)

/-- info: suggest? — suggestions (`exact`/`omega`/… close the goal; `apply`/`rw` transform it):
  1. exact fun n => Fixture.isShiny_all (Fixture.frob n)    [add: import Fixture.Lemmas]
  2. rw [Fixture.frob_eq]   (⊢ Fixture.IsShiny (n✝ + n✝))    [add: import Fixture.Lemmas]
-/
#guard_msgs in
#suggest (∀ n, IsShiny (frob n))
