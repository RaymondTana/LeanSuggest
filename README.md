# LeanSuggest

`suggest?` — a library-search tactic that **crosses file boundaries** and **resolves imports**.

It extends `exact?`/`apply?` along two axes:

- **Scope** — when no *imported* lemma closes your goal, it also searches the rest of
  your project (lemmas you haven't imported).
- **Actionability** — it reports the lemma *and the `import` line* that brings it into
  scope, and a one-click code action inserts the import + replaces the tactic.

It reuses the same `MetaM` procedures as `exact?`/`apply?` (`librarySearch`'s candidate
finder, `mkLibrarySearchLemma`, `apply`, `solveByElim`) — it does not call those tactics —
and drives its own candidate loop so it can return **multiple** results and **partial**
matches (`apply`, à la `apply?`), not just the first full closer.

It also runs Lean core's **`rw?` engine** (`Lean.Meta.Rewrites`) over the same scopes, so it
suggests **rewrite** lemmas — including ones from unimported modules, with the `import` to
add. (This is the first roadmap item, now built; see "Roadmap" below.)

## What you get

| Form | Kind | Use |
|------|------|-----|
| `suggest?` | tactic | use in a `by` block, exactly where you'd use `exact?`/`apply?` |
| `#suggest (T)` | command | top-level query (like `#check`/`#eval`), no proof needed |
| 💡 lightbulb | LSP code action | on a `suggest?` tactic: one click inserts the import + replaces it |

Full closers are suggested as `exact …`; partial matches as `apply …` with their
leftover subgoals; rewrite lemmas as `rw […]` (or `rw [← …]`) with the rewritten goal
(or "closes by rfl"). Full `exact` closers rank first.

## Install

1. **Add the dependency** to your project's `lakefile.toml`:
   ```toml
   [[require]]
   name = "LeanSuggest"
   git = "https://github.com/<you>/LeanSuggest"   # or a local `path = "..."`
   ```
   then run `lake update LeanSuggest` once.

2. **Import it** where you want the tactic:
   ```lean
   import LeanSuggest
   ```
   (Tip: put this in a base file your other files already import — in Lean a tactic is
   only available in files that transitively import the module defining it; there is no
   global always-on tactic short of forking Lean core.)

3. **Point it at your project.** Set the *built* library root(s) to search, either way:
   - **Env var (no rebuild):** `LEANSUGGEST_ROOTS=MyProject` (comma-separated for several,
     e.g. `A,B`). Read at search time by `configuredRoots`.
   - **In source:** edit `projectRoots` in `LeanSuggest/Basic.lean`:
     ```lean
     def projectRoots : List Name := [`MyProject]
     ```
   Each root must have its `.olean`s built (`lake build MyProject`). With neither set (default
   `[]`), `suggest?` only searches what your file already imports (no cross-file search).

## Using it

```lean
import LeanSuggest

-- in a proof: behaves like exact?/apply?, but also finds unimported project lemmas
example : MyGoal := by suggest?

-- as a query, no proof needed:
#suggest (MyGoal)
```

When `suggest?` finds an *unimported* lemma it cannot close the goal itself (the kernel
would reject a proof term naming a constant the file hasn't imported), so it reports the
suggestion and leaves the goal open — the **lightbulb** is what applies it (inserts the
`import` and replaces `suggest?` with the `exact …`/`apply …`).

## End-to-end test / demo

`test/e2e.sh` is a self-contained, runnable demonstration of every cross-file capability —
no Mathlib, no external project required. It builds a tiny fixture library (`Fixture/`) whose
*definitions* (`Fixture.Defs`) and *lemmas* (`Fixture.Lemmas`) live in separate modules, runs
`test/Demo.lean` (which imports only the definitions) against it via `LEANSUGGEST_ROOTS=Fixture`,
and asserts the suggestions name the right lemma **and** the `import` to add:

```
bash test/e2e.sh        # builds, runs, asserts → "E2E PASS ✅"
```

It exercises all four paths — cross-file `exact`, partial `apply`, **`rw`** (the rewrite
engine), and discharging a goal from a **local hypothesis** — each reported with its
`[add: import Fixture.Lemmas]`. `test/Demo.lean` is also readable on its own as a worked
example (open it and watch the InfoView).

## How it works (two tiers)

1. Search the **current file's environment** (what `exact?` sees).
2. If nothing in scope *closes* the goal, build a **constructed environment** — your
   file's imports plus the configured roots (`LEANSUGGEST_ROOTS` / `projectRoots`) — and
   search that. Each result records the module it came from, diffed against your file's
   imports to produce the `import` to add.

A `∀`-goal is `intro`'d first so its conclusion indexes in the discrimination tree, and
the goal's local hypotheses are carried into the search so premises can be discharged.

## Caveats / known limitations (productionization TODO)

These are the gaps a maintainer should tackle (also flagged in `Basic.lean`):

- **`projectRoots` isn't auto-discovered.** It can be set without editing source via the
  `LEANSUGGEST_ROOTS` env var (see Install §3), but the ideal is auto-discovery from the Lake
  configuration (the consuming project's `lean_lib` names).
- **No cache invalidation.** The constructed environment is cached for the process and
  goes **stale** when you rebuild your project — restart the server to refresh. Should be
  keyed on a fingerprint of project `.olean` mtimes/hashes.
- **Cold start is slow** (~30s) the first time the constructed environment is built
  (it imports the project + its dependencies); cached after.
- **`maxHeartbeats` is forced high** to absorb that build cost — a workaround, not
  something `exact?`/`apply?` need.
- **Full-Mathlib search isn't enabled.** Searching all of Mathlib (not just your project)
  would require every Mathlib `.olean` present (`lake exe cache get`) and gigabytes of RAM.
- **Broad `catch _`** swallows genuine errors (robust, but hides bugs).
- **∀-quantified equality goals lose symm-awareness** (the `∀` branch uses the plain
  finder, not the symm-aware one).

## Scope vs. general "library-search is dumb" critiques

LeanSuggest is a **thin layer** over `exact?`/`apply?` that adds **scope**
(cross-file / unimported) and **actionability** (import resolution + a code action).
It deliberately does **not** try to make the underlying *search* smarter, so the common
critique list of `apply?` (multi-step chaining, rewriting, case-splits, ML ranking, …) is
mostly **orthogonal** to this tool. Note too that several such critiques are factually off
about `apply?` as it stands: it **does** use local hypotheses (via `solveByElim`), **is**
symm-aware, **does** rank by discrimination-tree relevance, and **does** emit `refine … ?_`
when metavariables remain.

Genuinely accurate limitations that LeanSuggest **inherits** (and that are non-goals here —
separate tools already exist):

- **Single-step only** — one library lemma + bounded `solveByElim`; no multi-tactic
  chaining (that's "hammer" territory). The partial-match output (`apply …` leaving
  subgoals) is the only nod toward partial progress.
- **Suggests `exact`/`apply`/`rw` and a small set of closed tactics** (`omega`/`simp`/
  `trivial`, via the `hint`-style panel) — not `cases`/`induction`, and not full
  multi-tactic chaining. (`rw?` and the closed-tactic panel are covered — see Roadmap §1–2.)

The first idea that *extended this tool along its own axis* — an **import-resolving
`rw?`**, suggesting a rewrite lemma from an unimported module together with its `import` —
is now **built** (see "Roadmap" §1). It was the natural sequel: more searcher behind the
same import-resolving post-pass, not a fix to the search engine.

## Roadmap: a stronger `suggest?` (panel + shared post-pass)

The import-resolution here is a **tactic-agnostic post-pass**: run a proof-producing
search over the *constructed environment*, then map the proof's constants → their defining
modules → the `import` to add (`searchCandidates` + the `modsOf` step in `Basic.lean`).
Anything that (a) runs over a custom `Environment` and (b) yields an inspectable proof can
plug into it. So "stronger `suggest?`" = **more searchers behind the same post-pass**, not
a new engine. This refactor is now in place: a `Searcher := Environment → Expr → MetaM (Array
Hit)` abstraction with a `panel : List Searcher` that `allHits` runs and merges/ranks (full
closers first). Adding a searcher means **appending one entry to `panel`** — nothing else
changes. (The signature is `(baseline, type)` rather than the originally-sketched `MVarId`,
because both existing members create their own goal mvar and run in the ambient local
context; the panel runs over whatever env the caller set — current or constructed.)

Three concrete additions, easiest first:

### 1. Import-resolving `rw?` — ✅ **DONE**
- **Reuse:** Lean **core**'s `rw?` engine, `Lean.Meta.Rewrites` (`findRewrites` /
  `rewriteCandidates`, with `createModuleTreeRef` + `localHypotheses`) — the rewrite analogue
  of `librarySearch`, backed by its own discrimination tree of `Eq`/`Iff` lemmas. *(This
  engine moved from Mathlib into Lean core, so — unlike the original plan — it adds **no
  Mathlib dependency**; it's reused exactly like `librarySearch`.)*
- **Built as:** `rewriteHits` in `Basic.lean` runs `findRewrites` over the search env; each
  result becomes a `Hit` with `kind := .rewrite`, `tactic := "rw [lemma]"` (or `rw [← lemma]`),
  `mods` diffed against the baseline env (the cross-file import payoff), and the rewritten goal
  (or "closes by rfl") as its display. `allHits` merges these with the `exact`/`apply` hits and
  ranks full closers first. `=`/`↔` **local hypotheses** are offered as rewrites too.
- **Status / next:** a rewrite *transforms* rather than closes, so rw hits are reported (and
  applied via the lightbulb), never auto-`exact`'d — pair with step 3 for "rw then close".
  `rewriteHits` and `searchCandidates` are now uniform `panel` members (see the `Searcher`
  refactor above), so the next additions just append to `panel`.

### 2. A `hint`-style panel — ✅ **DONE**
- **Built as:** `hintHits` runs a list of closed tactics (`hintTactics := ["omega", "simp",
  "trivial"]`) against the goal — parsing each as `tactic` syntax and running it via
  `Lean.Elab.Tactic.run` — and keeps the ones that leave no subgoals (à la Mathlib's `hint`,
  but reusing only **Lean core** tactics, so no Mathlib/aesop dependency). Each becomes a
  `Hit` with `kind := .tacticClose`, `tactic := "omega"` (etc.), `mods := []`. Reported as the
  tactic to run, never auto-`exact`'d. Add a tactic by appending to `hintTactics`.
- **Ranking implemented:** `allHits` now orders **full closers first, then fewer imports,
  then partials** — so a no-import closer (`omega`, or an in-scope lemma) outranks an
  import-needing one.
- **Notes:** these are in-scope procedures; if one closes the goal the two-tier logic never
  reaches the cross-file search, so they effectively only matter over the current env.
  `decide` is intentionally excluded (can blow up). `ring`/`aesop` are left out to avoid a
  Mathlib/aesop dependency — add them if your project already depends on them. `simp` does
  NOT cross files cleanly (unimported `@[simp]` lemmas aren't in the active simp set), so it
  stays in-scope-only — which the panel already is.

### 3. Multi-step chaining via `aesop` over the constructed environment (research spike)
- **Reuse:** `aesop` (already a dependency) does best-first *backward* multi-step search.
  Programmatic entry via `Aesop.search` / the `Aesop.Frontend` API.
- **Slot in:** run `aesop` over `constructedEnv`. On success, the goal mvar is assigned a
  proof term → same post-pass extracts every lemma it used → the (possibly multiple)
  imports. Suggest **`aesop`** as the tactic (after the imports are added, plain `aesop`
  reproduces it) — or, more robustly, emit the explicit proof term validated by `roundTrips`.
- **Gotchas (this is the hard part):**
  - **Rule-set injection.** Unimported project lemmas aren't registered as `@[aesop]` rules,
    so out of the box aesop won't *use* them. You must feed them in — e.g. take the
    discrimination-tree candidates (as in `searchCandidates`) and pass them via
    `aesop (add unsafe apply [...])`, or build a temporary local rule set. Getting this
    scoping right is the crux.
  - **Multi-import minimization** and **multi-line edits** in the code action.
  - **Performance:** aesop over a full constructed env can be slow — bound its depth/time,
    and only invoke it when the cheaper panel members come up empty.

**Guiding principle:** keep the tool's identity — *cross-file search + import resolution*.
Extend the panel with searchers that genuinely benefit from cross-file scope (`rw?` is the
poster child); lean on `omega`/`ring`/`aesop` for breadth without trying to out-prove them.

## Provenance

Extracted from a POC built inside `formalising-mathematics-notes`. The engine is a single
file, `LeanSuggest/Basic.lean`.