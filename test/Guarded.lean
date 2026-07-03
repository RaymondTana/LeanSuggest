/-
Copyright (c) 2026 Raymond Tana. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raymond Tana
-/
import LeanSuggest
import Fixture.Defs

/-!
# Deterministic, cross-file tests.

Run it:

```
lake env lean test/Guarded.lean
```

These tests are also run as part of `test/e2e.sh`.

`#guard_msgs` pins the precise message emitted by a command or tactic.
-/

open Fixture

/-- info: suggest? — suggestions:
  1. exact fun n => Fixture.isShiny_all n    [add: import Fixture.Lemmas]
-/
#guard_msgs in
#suggest (∀ n, IsShiny n)

/-- info: suggest? — suggestions:
  1. exact fun n => Fixture.isShiny_all (Fixture.frob n)    [add: import Fixture.Lemmas]
  2. rw [Fixture.frob_eq]   (⊢ Fixture.IsShiny (n✝ + n✝))    [add: import Fixture.Lemmas]
-/
#guard_msgs in
#suggest (∀ n, IsShiny (frob n))
