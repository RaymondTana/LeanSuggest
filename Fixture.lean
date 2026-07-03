/-
Copyright (c) 2026 Raymond Tana. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raymond Tana
-/
-- Root of the `Fixture` E2E test library. The search points `LEANSUGGEST_ROOTS=Fixture`
-- at this root so the constructed environment imports both `Fixture.Defs` and the
-- (deliberately-unimported-by-the-consumer) `Fixture.Lemmas`.
import Fixture.Defs
import Fixture.Lemmas
