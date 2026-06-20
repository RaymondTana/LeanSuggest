import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.LibrarySearch
import Lean.Meta.Tactic.TryThis
import Batteries.CodeAction

/-!
# `suggest?` — library search that crosses file boundaries and resolves imports

This reuses the same `MetaM` procedures behind `exact?`/`apply?` (it does NOT call
those tactics): `librarySearch`'s candidate finder, `mkLibrarySearchLemma`, `apply`,
and `solveByElim`. It reimplements their driver loop (`tryOnEach`) because stock
`librarySearch` stops at the first full closer and won't surface multiple results
or partial matches — both of which we want.

`#suggest (goal)` and the `suggest?` tactic search in two tiers:
1. the current file's environment (what `exact?` sees), then
2. if nothing in scope CLOSES the goal, a **constructed environment** — the file's
   imports plus the project roots (`projectRoots`) — so lemmas your file hasn't
   imported are found, reported with the `import` line that brings them into scope.

Each candidate is `apply`-d and its subgoals attacked with `solveByElim`:
* 0 remaining  → a full closer, suggested as `exact <proof>`;
* ≥1 remaining → a partial match, suggested as `apply <lemma>` (à la `apply?`).
Full closers rank first. A `∀`-goal is `intro`'d so its conclusion head indexes
(beating `exact?`), and the goal's local hypotheses are carried into the search.

KNOWN LIMITATIONS (productionization TODO):
* `projectRoots` is hardcoded — should be auto-discovered from the Lake setup
  (the consuming project's `lean_lib` names) or read from a config key.
* `constructedEnvCache` is never invalidated — it goes stale when you rebuild the
  project. Should be keyed on a fingerprint of the project `.olean` mtimes/hashes.
* `maxHeartbeats` is forced high to absorb the constructed-env build cost; this is
  a workaround, not something `exact?`/`apply?` need (see `searchOpts`).
* Broad `catch _` swallows genuine errors (eases robustness, hurts debugging).
-/

open Lean Elab Command Term Meta Lean.Meta.LibrarySearch

namespace LeanSuggest

/-- Library roots the constructed environment imports on top of the file's imports.
    Each must be a *built* library root (its `.olean`s must exist — `lake build <root>`).
    TODO: auto-discover from the Lake configuration instead of hardcoding. -/
def projectRoots : List Name := []  -- CONFIGURE: your project's built library root(s), e.g. [`MyProject]

/-- Heartbeat budget for a search. The constructed environment builds the full library
    discrimination tree in-process on first use, which can exceed the default 200k; we
    raise it as a workaround. (Stock `exact?`/`apply?` run within the default.) -/
def searchOpts (base : Options) : Options := base.setNat `maxHeartbeats 1000000

/-- All constant names occurring in an expression. -/
def collectConsts (e : Expr) : NameSet :=
  e.foldConsts {} fun n s => s.insert n

/-- module-index → module-name table for an environment. -/
def moduleTable (env : Environment) : Std.HashMap Nat Name := Id.run do
  let mut hm : Std.HashMap Nat Name := {}
  for imp in env.header.moduleNames do
    hm := hm.insert ((env.getModuleIdx? imp).getD default) imp
  return hm

/-- The module a declaration was defined in (`.anonymous` if unknown). -/
def moduleOf (env : Environment) (hm : Std.HashMap Nat Name) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => (hm.get? i).getD .anonymous
  | none   => .anonymous

/-- Modules every file already has, so never worth suggesting as an import. -/
def isNoiseModule (m : Name) : Bool :=
  m == .anonymous || (`Init).isPrefixOf m || (`Lean).isPrefixOf m || (`Std).isPrefixOf m

/-- Validate a suggestion the way `exact?` does: its *pretty-printed* term must parse
    and re-elaborate at `type` with no leftover metavariables. A proof `Expr` can
    typecheck yet print to text that fails to round-trip (e.g. unsynthesizable implicit
    args); this filters those out. Runs in the ambient local context, so the term may
    mention the goal's hypotheses. NOTE: re-elaborates the whole proof — not free. -/
def roundTrips (type : Expr) (termStr : String) : MetaM Bool := do
  match Lean.Parser.runParserCategory (← getEnv) `term termStr with
  | .error _   => return false
  | .ok stx    =>
    Lean.Elab.Term.TermElabM.run' do
      try
        let e ← Lean.Elab.Term.elabTermEnsuringType stx (some type)
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars e).hasExprMVar
      catch _ => return false

/-- One search result. -/
structure Hit where
  /-- The (possibly partial) proof term — used to close the goal when `isFull`. -/
  proof   : Expr
  /-- True if it fully closes the goal (`exact`); false if it leaves subgoals (`apply`). -/
  isFull  : Bool
  /-- Tactic text to insert: `exact …` or `apply …`. -/
  tactic  : String
  /-- Human-readable line (adds the leftover subgoals for partial matches). -/
  display : String
  /-- Modules used by the proof that the baseline env lacks (the imports to add). -/
  mods    : List Name

/-- Find ranked library lemmas for `type`: full closers (`exact`) first, then partial
    matches (`apply`, with leftover subgoals). Runs in the ambient local context, so
    local hypotheses are available. `baseline` is the environment whose imports we diff
    against to decide which modules still need importing.

    We drive the candidate loop ourselves (rather than calling `librarySearch`) so we
    can collect *every* closer and the partial matches, not just the first closer. -/
def searchCandidates (baseline : Environment) (type : Expr)
    (maxFull : Nat := 5) (maxPartial : Nat := 3) : MetaM (Array Hit) :=
  withoutModifyingState do
  let env ← getEnv
  let hm := moduleTable env
  -- Imports the proof needs that `baseline` doesn't already provide.
  let modsOf (e : Expr) : List Name :=
    let needed := (collectConsts e).toList.filter (fun c => !baseline.contains c)
    (needed.map (moduleOf env hm)).filter (fun m => !isNoiseModule m) |>.eraseDups
  -- Build + validate a full-closer `Hit` from a proof term (must be called in the
  -- search goal's context so the term pretty-prints with its hypotheses).
  let mkFullHit (proof : Expr) : MetaM (Option Hit) := do
    let proof := proof.headBeta
    let termStr := toString (← Meta.ppExpr proof)
    if proof.hasExprMVar || !(← roundTrips type termStr) then return none
    let txt := s!"exact {termStr}"
    return some { proof, isFull := true, tactic := txt, display := txt, mods := modsOf proof }
  -- Build a partial-match `Hit` (no validation: `apply <name>` is a single ident
  -- that always re-parses; the leftover subgoals are pretty-printed for display).
  let mkPartialHit (name : Name) (proof : Expr) (remaining : List MVarId) : MetaM Hit := do
    let tyStrs ← remaining.mapM fun sg => sg.withContext do
      return s!"⊢ {← Meta.ppExpr (← instantiateMVars (← sg.getType))}"
    return { proof, isFull := false, tactic := s!"apply {name}",
             display := s!"apply {name}   (leaves {remaining.length}: " ++
               String.intercalate ", " tyStrs ++ ")",
             mods := modsOf proof }
  let .mvar goal0 ← mkFreshExprMVar type | return #[]
  -- intro a ∀-goal's binders so its conclusion head indexes; keep the fvars so we can
  -- abstract a found proof back into a closed term with `mkLambdaFVars`.
  let (introFvars, searchGoal) ← if type.isForall then goal0.intros else pure (#[], goal0)
  let fvarExprs := introFvars.map Expr.fvar
  -- Find candidates by the goal's CONCLUSION. For a ∀-goal we query with the conclusion
  -- under fresh METAVARIABLES: a free fvar (from `intros`) in the query would NOT match
  -- the discrimination tree's `*` slots, but a metavariable does. We still `apply` to the
  -- fvar `searchGoal`. (TODO: the ∀ branch drops the symm-aware finder, so symm-only
  -- matches on ∀-quantified equality goals are missed.)
  let candidates ←
    if type.isForall then do
      let (_, _, conclusion) ← forallMetaTelescope type
      let names ← try libSearchFindDecls conclusion catch _ => pure #[]
      let mctx ← getMCtx
      pure (names.map fun c => ((searchGoal, mctx), c))
    else
      try librarySearchSymm libSearchFindDecls searchGoal
      catch _ => do
        let names ← try libSearchFindDecls (← searchGoal.getType) catch _ => pure #[]
        let mctx ← getMCtx
        pure (names.map fun c => ((searchGoal, mctx), c))
  let cfg : ApplyConfig := { allowSynthFailures := true }
  let s ← saveState
  let mut full : Array Hit := #[]
  let mut part : Array Hit := #[]
  -- Pass 0: what `exact?` tries before any library lemma — close the goal directly with
  -- `solveByElim` (local hypotheses + basic lemmas). Recovers simple proofs like `Eq.symm h`.
  restoreState s
  let directHit? ← try
    let _ ← solveByElim [] (exfalso := true) (goals := [searchGoal]) (maxDepth := 6)
    searchGoal.withContext (mkFullHit (← mkLambdaFVars fvarExprs (← instantiateMVars (mkMVar searchGoal))))
  catch _ => pure none
  if let some h := directHit? then full := full.push h
  -- Pass 1: each library candidate — `apply` it, then `solveByElim` its subgoals.
  for cand in candidates do
    if full.size ≥ maxFull && part.size ≥ maxPartial then break
    restoreState s
    let ((g, mctx), (name, declMod)) := cand
    let hit? ← try
      setMCtx mctx
      let newGoals ← g.apply (← mkLibrarySearchLemma name declMod) cfg
      -- `solveByElim` THROWS when it can't discharge everything; a throw here just means
      -- the candidate is a partial match leaving `newGoals`, not that it's unusable.
      let remaining ← (try solveByElim [] (exfalso := false) (goals := newGoals) (maxDepth := 6)
                        catch _ => pure newGoals)
      searchGoal.withContext do
        let proof ← mkLambdaFVars fvarExprs (← instantiateMVars (mkMVar searchGoal))
        if remaining.isEmpty then mkFullHit proof
        else some <$> mkPartialHit name proof remaining
    catch _ => pure none
    match hit? with
    | some h =>
        if h.isFull then
          if full.size < maxFull then full := full.push h
        else
          if part.size < maxPartial then part := part.push h
    | none => pure ()
  return full ++ part

/-- Run a `MetaM` action over an arbitrary environment (e.g. the constructed env). -/
def runMetaOver {α : Type} (env : Environment) (opts : Options) (act : MetaM α) : IO α := do
  let coreCtx : Core.Context := { fileName := "<suggest>", fileMap := .ofString "", options := opts }
  let (a, _) ← (act.run').toIO coreCtx { env := env }
  return a

/-- Process-wide cache of the constructed environment, reused across calls.
    TODO: never invalidated — goes stale when project `.olean`s are rebuilt. Key it on
    `(import set, fingerprint of project olean mtimes)` and rebuild when that changes. -/
initialize constructedEnvCache : IO.Ref (Option Environment) ← IO.mkRef none

/-- The constructed environment: the file's imports plus `projectRoots`. Cached after the
    first (expensive, ~30s) build; subsequent calls in the same process are fast.
    `trustLevel := 1024` matches Lake's olean trust; `loadExts := true` loads environment
    extensions so instance resolution etc. work during the search. -/
def constructedEnv (cur : Environment) (opts : Options) : IO Environment := do
  if let some e ← constructedEnvCache.get then return e
  let extra := projectRoots.toArray.map (fun m => { module := m : Import })
  let e ← importModules (cur.header.imports ++ extra) opts (trustLevel := 1024) (loadExts := true)
  constructedEnvCache.set (some e)
  return e

/-- Two-tier search: the current env, then the constructed env if no in-scope lemma
    CLOSES the goal. `lctx`/`linsts` carry the goal's hypotheses into both searches.
    (The `suggest?` tactic inlines this same two-tier logic instead of calling here,
    because it additionally needs the goal's `MVarId` to close it and emit "Try this".) -/
def suggestHits (baseline : Environment) (opts : Options)
    (lctx : LocalContext) (linsts : LocalInstances) (type : Expr) : IO (Array Hit) := do
  let go (searchEnv : Environment) : IO (Array Hit) :=
    runMetaOver searchEnv opts <| withLCtx lctx linsts (searchCandidates baseline type)
  let inScope ← go baseline
  if inScope.any (·.isFull) then return inScope
  let crossFile ← go (← constructedEnv baseline opts)
  return if crossFile.isEmpty then inScope else crossFile

/-- Render ranked hits as a message. -/
def renderHits (hits : Array Hit) : MessageData :=
  let lines := hits.toList.zipIdx.map fun (h, i) =>
    let imp := if h.mods.isEmpty then ""
      else s!"    [add: {String.intercalate ", " (h.mods.map (fun m => s!"import {m}"))}]"
    s!"  {i + 1}. {h.display}{imp}"
  m!"suggest? — suggestions (`exact` closes the goal; `apply` leaves subgoals):\n{String.intercalate "\n" lines}"

/-- `#suggest (T)` — query form, like `#check`/`#eval`: prints ranked suggestions + imports
    for the goal type `T`, with no proof/goal state. -/
elab "#suggest " t:term : command => do
  let opts := searchOpts (← getOptions)
  let curEnv ← getEnv
  let type ← liftTermElabM do
    let e ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let hits ← suggestHits curEnv opts {} {} type
  if hits.isEmpty then
    logInfo m!"#suggest: nothing applies to `{type}`, even across the project."
  else
    logInfo (renderHits hits)

open Lean.Meta.Tactic.TryThis Elab.Tactic in
/-- `suggest?` — like `exact?`/`apply?`, but if no *imported* lemma closes the goal it
also searches the rest of the project and reports the lemma + the `import` to add.
Full closers show as `exact`, partial matches as `apply`. -/
elab (name := suggestImportTac) "suggest?" : tactic => do
  let goal ← getMainGoal
  let opts := searchOpts (← getOptions)
  let curEnv ← getEnv
  let (lctx, linsts, type) ← goal.withContext do
    pure ((← getLCtx), (← getLocalInstances), (← instantiateMVars (← goal.getType)))
  -- Tier 1: current env, in the goal's context.
  let inScope ← goal.withContext (withOptions (fun _ => opts) (searchCandidates curEnv type))
  match inScope.find? (·.isFull) with
  | some h =>
      -- An imported lemma closes it: actually close the goal and emit "Try this", like `exact?`.
      closeMainGoal `suggest? h.proof
      addExactSuggestion (← getRef) h.proof
      if inScope.size > 1 then logInfo (renderHits inScope)
  | none =>
      -- Tier 2: constructed env (+ partial matches). We can't `exact` an unimported lemma
      -- (the kernel would reject it), so we only report — the code action applies it.
      let crossFile ← runMetaOver (← constructedEnv curEnv opts) opts
        (withLCtx lctx linsts (searchCandidates curEnv type))
      let hits := if crossFile.isEmpty then inScope else crossFile
      if hits.isEmpty then
        throwError "suggest? found nothing that applies, even across the project."
      else
        logInfo (renderHits hits)

/-! ## The lightbulb: a code action on `suggest?`

When the cursor is on a `suggest?` tactic, offer a quick-fix whose `WorkspaceEdit`
inserts the needed `import` after the last existing import AND replaces `suggest?` with
the top suggestion (`exact …`/`apply …`) — in one click. -/

open Lean Server RequestM Lean.Lsp Batteries.CodeAction in
@[tactic_code_action suggestImportTac]
def suggestImportCodeAction : TacticCodeAction := fun _params _snap ctx _stack node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  if info.goalsBefore.isEmpty then return #[]
  let doc ← readDoc
  let eager : CodeAction := { title := "suggest?: insert import & apply suggestion", kind? := "quickfix" }
  return #[{
    eager
    -- The search is deferred to `lazy?` so the lightbulb list appears instantly; the work
    -- (and possible ~30s first constructed-env build) only runs when this action is chosen.
    lazy? := some do
      let goal := info.goalsBefore[0]!
      let opts := searchOpts ctx.options
      let (lctx, linsts, type) ← ctx.runMetaM {} (goal.withContext do
        pure ((← getLCtx), (← getLocalInstances), (← instantiateMVars (← goal.getType))))
      let some h := (← suggestHits ctx.env opts lctx linsts type)[0]? | return eager
      -- edit 1: replace `suggest?` with the suggested tactic.
      let tacPos := doc.meta.text.utf8PosToLspPos info.stx.getPos?.get!
      let tacEnd := doc.meta.text.utf8PosToLspPos info.stx.getTailPos?.get!
      let tacEdit : TextEdit := { range := ⟨tacPos, tacEnd⟩, newText := h.tactic }
      -- edit 2: insert the needed import(s) after the last existing import line.
      -- NOTE: naive — scans raw source lines for `import `, appends after the last one;
      -- doesn't sort or dedupe against a multi-line import block.
      let srcLines := (doc.meta.text.source.splitOn "\n").toArray
      let mut lastImp := 0
      for i in [0:srcLines.size] do
        if (srcLines[i]?.getD "").startsWith "import " then lastImp := i
      let impPos : Lsp.Position := ⟨lastImp, (srcLines[lastImp]?.getD "").length⟩
      let importEdit : TextEdit :=
        { range := ⟨impPos, impPos⟩, newText := String.join (h.mods.map fun m => s!"\nimport {m}") }
      let edits := if h.mods.isEmpty then #[tacEdit] else #[importEdit, tacEdit]
      let title :=
        if h.mods.isEmpty then s!"Replace with: {h.tactic}"
        else s!"Add import {h.mods.head!} & replace with: {h.tactic}"
      return { eager with
        title
        edit? := some <| .ofTextDocumentEdit { textDocument := doc.versionedIdentifier, edits } }
  }]

end LeanSuggest
