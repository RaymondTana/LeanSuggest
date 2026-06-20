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

## Provenance

Extracted from a POC built inside `formalising-mathematics-notes`. The engine is a single
file, `LeanSuggest/Basic.lean`.