# LeanSuggest

[![CI](https://github.com/RaymondTana/LeanSuggest/actions/workflows/ci.yml/badge.svg)](https://github.com/RaymondTana/LeanSuggest/actions/workflows/ci.yml)

`LeanSuggest`: better library and project search for Lean 4.

`suggest?` subsumes `exact?`, `apply?`, and `rw?`, running each over a wider, cross-file environment, and adds a small `hint`-style panel (employing `omega`, `simp`, and `trivial`) to close goals outright.

## The components of `LeanSuggest`

| Form | Kind | Use |
|------|------|-----|
| `suggest?` | tactic | in a `by` block |
| `#suggest (T)` | command | top-level query |
| 💡 lightbulb | LSP code action | insert the `import` + replace the tactic |

Full closers are suggested as `exact ...`; whereas partial matches as `apply ...` with their leftover subgoals; rewrites as `rw [lemma]` with the rewritten goal; plus a small closed-tactic panel (`omega`/`simp`/`trivial`). 

## Install

1. **Require it** in your project's `lakefile.toml`, then fetch once:
   ```toml
   [[require]]
   name = "LeanSuggest"
   git = "https://github.com/RaymondTana/LeanSuggest"   # or a local `path = "..."`
   rev = "v4.26.0"                                      # pin the tag matching your toolchain
   ```
   ```
   lake update LeanSuggest
   ```
2. **Import it**:
   ```lean
   import LeanSuggest
   ```
   This one import activates the tactic, the command, and the lightbulb in that file. A tactic only exists in files that transitively import its defining module, so put the import in a base file the rest of your project already imports.
3. **Build your project** (`lake build`). The cross-file search reads compiled `.olean` files, so only built lemmas are findable.

By default, every `[[lean_lib]]` in your `lakefile.toml` is searched.

### Configuration (only when the default is wrong)

The roots from which to search are resolved in this order:

1. **The `leanSuggest.roots` option**: per file, like any option:
   ```lean
   set_option leanSuggest.roots "MyProject,MyLib"
   ```
   or project-wide in *your* `lakefile.toml`:
   ```toml
   leanOptions = { weak.leanSuggest.roots = "MyProject" }
   ```
   (`weak.` is required in the lakefile form: Lake passes `leanOptions` as `-D` flags, validated before `LeanSuggest` is imported, and `weak.` defers that check. `set_option` needs no prefix.)
2. **The `LEANSUGGEST_ROOTS` env var** (comma-separated): handy for CI or CLI runs.
3. **Auto-discovery** from `lakefile.toml`: the zero-config default.

Options 1 and 2 work for searching a subset of your library, or if your project uses `lakefile.lean`. Each root must be built.

## Using it

```lean
import LeanSuggest

-- behaves like exact?/apply?, but also finds unimported project lemmas:
example : MyGoal := by suggest?

-- as a query, no proof needed:
#suggest (MyGoal)
```

When the closer is already imported, `suggest?` closes the goal and offers "Try this", exactly like `exact?`. When it lives in an *unimported* module, Lean would reject the proof (it names constants the file can't see), so the goal stays open and the result is reported:

```
suggest?: suggestions:
  1. exact fun n => Fixture.isShiny_all n    [add: import Fixture.Lemmas]
```

The **lightbulb** is what applies it: one click inserts the `import` at the end of your import header and replaces `suggest?` with the suggested tactic.

## How it works

Two phases:

1. **In scope**: search everything the file imports: the same `librarySearch` machinery behind `exact?`/`apply?`, Lean core's `rw?` engine, and the closed-tactic panel. A full in-scope closer ends the search.
2. **Cross-file**: otherwise, construct an environment of the file's imports **plus the configured roots** (loaded from the project's `.olean`s) and run the same searches over it.

Import resolution is a search-agnostic post-pass: collect the constants named by the found proof term, keep the ones the file can't already see, and map each to its defining module: those modules are the imports to add. Because it inspects proof terms, it works uniformly for library-search hits, rewrites, and even `simp` (a `simp` proof names the `@[simp]` lemmas it used, so a cross-file `simp` closer reports the imports that make it work). Hits whose `import` would create a cycle are dropped: whether the needed module is the current file itself (a stale compiled copy of it reaches phase 2 via the roots) or any module that transitively imports the current file.

The constructed environment is cached per process and invalidated by fingerprinting the roots' `.olean` mtimes, so a `lake build` refreshes it. A `∀`-goal is `intro`'d first, and the goal's local hypotheses are carried into both phases so premises can be discharged.

## What it is (and isn't)

- **Vs. `exact?` / `apply?` / `rw?`**: same search engines, deliberately: this is a thin layer adding *scope* (unimported project files) and *actionability* (import + one-click fix), not a smarter search.
- **Vs. Loogle / LeanSearch / Moogle**: those are lemma search engines: good for "does Mathlib have something like this?": but they don't see your goal in context, don't verify the lemma applies, don't know your local project, and leave the import to you.
- **Vs. `aesop` / `polyrith` / hammers**: those chain many steps to find whole proofs. `suggest?` is single-step by design: one library lemma plus a bounded `solve_by_elim` cleanup of side goals.

The gap it fills: you proved a lemma in one file of your project and are working in another that doesn't import it. `exact?` can't see it, search engines don't know your project exists, and nothing types the `import` line for you. `suggest?` automates exactly that, end to end.

## Limitations

- **First cross-file query is slow**: it loads the constructed environment. Cached after. A rebuild of your project invalidates the cache (by design). The cache is a single entry, so alternating between files with disjoint imports rebuilds it. `maxHeartbeats` is forced high to absorb this cost.
- **Only built lemmas are visible**: phase 2 reads `.olean`s, so run `lake build` after proving something new.
- **Project scope, not Mathlib scope.** Searching *all* of Mathlib for unimported lemmas would need every Mathlib `.olean` present and gigabytes of RAM, so it's not enabled; Mathlib modules you already import are searched like anything else.
- **`lakefile.lean` projects need explicit roots** (`leanSuggest.roots` or `LEANSUGGEST_ROOTS`); auto-discovery reads `lakefile.toml` only, and assumes the Lean server's cwd is the Lake project root (it is, under `lake serve`).
- **Version alignment:** `LeanSuggest` pins a Batteries revision per toolchain; if your project uses Mathlib, its Batteries must be compatible or Lake will complain.
- **∀-quantified equality goals lose symm-awareness** (the `∀` branch uses the plain candidate finder).

## Development

The engine is a single file, [`LeanSuggest/Basic.lean`](LeanSuggest/Basic.lean).

```bash 
bash test/e2e.sh   # builds, runs, asserts → "E2E PASS ✅"
```

The end-to-end test is a self-contained demo (no Mathlib needed): a tiny fixture library splits *definitions* (`Fixture.Defs`) from *lemmas* (`Fixture.Lemmas`), and [`test/Demo.lean`](test/Demo.lean), which imports only the definitions, exercises every cross-file path (`exact`, partial `apply`, `rw`, local-hypothesis discharge, the closed-tactic panel), asserting each suggestion names the right lemma as well as the right `import`. `test/Guarded.lean` pins exact outputs via `#guard_msgs`. CI runs all of it on every push and PR ([.github/workflows/ci.yml](.github/workflows/ci.yml)).

## License

Apache 2.0 - see [LICENSE](LICENSE).
