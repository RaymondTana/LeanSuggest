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

## What you get

| Form | Kind | Use |
|------|------|-----|
| `suggest?` | tactic | use in a `by` block, exactly where you'd use `exact?`/`apply?` |
| `#suggest (T)` | command | top-level query (like `#check`/`#eval`), no proof needed |
| 💡 lightbulb | LSP code action | on a `suggest?` tactic: one click inserts the import + replaces it |

Full closers are suggested as `exact …`; partial matches as `apply …` with their
leftover subgoals.

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

3. **Point it at your project.** Edit `projectRoots` in `LeanSuggest/Basic.lean` to your
   project's *built* library root(s):
   ```lean
   def projectRoots : List Name := [`MyProject]
   ```
   Each root must have its `.olean`s built (`lake build MyProject`). With the default
   `[]`, `suggest?` only searches what your file already imports (no cross-file search).

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

## How it works (two tiers)

1. Search the **current file's environment** (what `exact?` sees).
2. If nothing in scope *closes* the goal, build a **constructed environment** — your
   file's imports plus `projectRoots` — and search that. Each result records the module
   it came from, diffed against your file's imports to produce the `import` to add.

A `∀`-goal is `intro`'d first so its conclusion indexes in the discrimination tree, and
the goal's local hypotheses are carried into the search so premises can be discharged.

## Caveats / known limitations (productionization TODO)

These are the gaps a maintainer should tackle (also flagged in `Basic.lean`):

- **`projectRoots` is hardcoded.** Should be auto-discovered from the Lake configuration
  (the consuming project's `lean_lib` names) or read from a config key.
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
- **Only suggests `exact`/`apply`** — not `rw`/`simp`/`cases`/`induction`. Those have
  their own search tactics (`rw?`, `simp?`, `hint`).

The one idea that could *extend this tool along its own axis*: an **import-resolving
`rw?`** — suggest a rewrite lemma from an unimported module together with its `import`.
That would be the natural sequel, not a fix to the search engine.

## Roadmap: a stronger `suggest?` (panel + shared post-pass)

The import-resolution here is a **tactic-agnostic post-pass**: run a proof-producing
search over the *constructed environment*, then map the proof's constants → their defining
modules → the `import` to add (`searchCandidates` + the `modsOf` step in `Basic.lean`).
Anything that (a) runs over a custom `Environment` and (b) yields an inspectable proof can
plug into it. So "stronger `suggest?`" = **more searchers behind the same post-pass**, not
a new engine. The clean refactor is a `Searcher := MVarId → MetaM (Array Hit)` abstraction
that `suggestHits` runs as a panel (some members over the current env, some over the
constructed env) and merges/ranks via `renderHits`.

Three concrete additions, easiest first:

### 1. Import-resolving `rw?` (recommended first; low risk)
- **Reuse:** Mathlib's `rw?` engine, `Mathlib.Tactic.Rewrites` (`rewrites`/`rewriteCandidates`)
  — the rewrite analogue of `librarySearch`, backed by its own discrimination tree of
  `Eq`/`Iff` lemmas.
- **Slot in:** run it over `constructedEnv`; each candidate is `(rewriteLemma, rewrittenGoal)`.
  Emit a `Hit` with `tactic := s!"rw [{rewriteLemma}]"`, `mods := moduleOf rewriteLemma`, and
  the rewritten goal as the "leaves" (it's naturally a *partial* match in our model).
- **Gotchas:** many candidates (rank, cap); a rewrite usually transforms rather than closes,
  so pair it with step 3 if you want "rw then close".

### 2. A `hint`-style panel (medium)
- **Reuse:** Mathlib's `hint` (`Mathlib.Tactic.Hint`) already runs a registered list of
  tactics and reports which close the goal — read its harness for how to run a tactic
  syntax against a goal mvar and detect closure.
- **Slot in:** add *closed* procedures — `omega`, `ring`, `decide`, `simp`, `aesop` — run in
  the **current** env (they don't reference unimported named lemmas, so `mods := []`, no
  import needed). Keep the *search* members (`exact?`/`apply?`/`rw?`) on the constructed env.
- **Gotchas:** ranking now spans tactic kinds — policy: full closers first, then fewer
  imports, then partials. `simp` does NOT cross files cleanly (unimported `@[simp]` lemmas
  aren't in the active simp set), so treat `simp?` as in-scope-only.

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