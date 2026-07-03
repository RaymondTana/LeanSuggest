/-
Copyright (c) 2026 Raymond Tana. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raymond Tana
-/
import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.LibrarySearch
import Lean.Meta.Tactic.Rewrites
import Lean.Meta.Tactic.TryThis
import Batteries.CodeAction

/-!
# `suggest?` — library search that crosses file boundaries and resolves imports

This reuses the same `MetaM` procedures behind `exact?`/`apply?`, including
`librarySearch`, `mkLibrarySearchLemma`, `apply`, and `solveByElim`.

Both the `#suggest (goal)` command and the `suggest?` tactic search in two phases:
1. First, through the current file's environment. But, if nothing in scope closes the goal,
2. Then through an enriched environment including the current file's imports, plus the
   project roots (`configuredRoots`: the `leanSuggest.roots` option, the `LEANSUGGEST_ROOTS`
   env var, or auto-discovery from `lakefile.toml`).

Each candidate lemma is `apply`-d, with any subgoals then being passed through `solveByElim`:
* =0 remaining indicates a full closure, so the candidate gets suggested as `exact <lemma>`;
* >0 remaining indicates a partial match, getting suggested as `apply <lemma>`.

Note that a `∀`-goal is `intro`'d, and the goal's local hypotheses are searched.
-/

open Lean Elab Command Term Meta Lean.Meta.LibrarySearch

-- Registered outside `namespace LeanSuggest` so the option key is exactly `leanSuggest.roots`.
-- Consumers set it in their own files (`set_option leanSuggest.roots "MyProject"`) or
-- project-wide via `leanOptions = { weak.leanSuggest.roots = "MyProject" }` in their
-- lakefile (`weak.` because a `-D` flag is validated before this library is imported).
register_option leanSuggest.roots : String := {
  defValue := ""
  descr := "comma-separated built library roots that suggest?/#suggest search across file \
    boundaries (e.g. \"MyProject,MyLib\"); empty: fall back to the LEANSUGGEST_ROOTS env \
    var, then to auto-discovery from lakefile.toml"
}

namespace LeanSuggest

/-- Parse a comma/whitespace/newline-separated list of module names, ignoring blanks. -/
def parseRootList (s : String) : List Name :=
  (s.splitToList (fun c => c == ',' || c == '\n' || c == ' ' || c == '\t')).filterMap fun part =>
    let part := part.trim
    if part.isEmpty then none else some part.toName

/-- Auto-discover the project's library roots from `lakefile.toml` in the current working
    directory: the `name` of every `[[lean_lib]]`. Returns `[]` if there's no `lakefile.toml`,
    or else it declares no libraries. -/
def discoverRootsFromToml : IO (List Name) := do
  let path : System.FilePath := (← IO.currentDir) / "lakefile.toml"
  if !(← path.pathExists) then return []
  let content ← IO.FS.readFile path
  let mut roots : List Name := []
  let mut inLib := false
  for raw in content.splitOn "\n" do
    let line := raw.trim
    if line.startsWith "[" then
      inLib := line.startsWith "[[lean_lib]]"
    else if inLib && line.startsWith "name" && (line.drop 4).trim.startsWith "=" then
      match line.splitOn "\"" with
      | _ :: v :: _ => roots := roots ++ [v.toName]
      | _           => pure ()
  return roots.eraseDups

/-- The library roots to search, by priority order:
    1. the `leanSuggest.roots` option (`set_option` in the consumer's file, or `leanOptions`
       in its lakefile),
    2. the `LEANSUGGEST_ROOTS` env var,
    3. auto-discovery: every `[[lean_lib]]` in the project's `lakefile.toml`. -/
def configuredRoots (opts : Options) : IO (List Name) := do
  let fromOpt := parseRootList (leanSuggest.roots.get opts)
  if !fromOpt.isEmpty then return fromOpt
  if let some s ← IO.getEnv "LEANSUGGEST_ROOTS" then
    let ns := parseRootList s
    if !ns.isEmpty then return ns
  try discoverRootsFromToml catch _ => return []

/-- Heartbeat budget for a search, especially for constructing the library discrimination
    tree for the first time. -/
def searchOpts (base : Options) : Options := base.setNat `maxHeartbeats 1000000

/-- All constant names occurring in an expression. -/
def collectConsts (e : Expr) : NameSet :=
  e.foldConsts {} fun n s => s.insert n

/-- The module in which a declaration was defined (otherwise, `.anonymous`). -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i]?.getD .anonymous
  | none   => .anonymous

/-- The names of every module in `env` whose import closure contains `target`, plus
    `target` itself. Adding an `import` of any of these to `target`'s source file would
    create an import cycle.

    Marks modules by forward passes over the module list: the loader stores a module after
    its imports, so one pass normally converges; looping to a fixpoint keeps the result
    correct without relying on that ordering. -/
def reverseImportClosure (env : Environment) (target : Name) : NameSet := Id.run do
  let mods := env.header.moduleNames.zip env.header.moduleData
  let mut marked : NameSet := ({} : NameSet).insert target
  let mut changed := true
  while changed do
    changed := false
    for (n, d) in mods do
      if !marked.contains n && d.imports.any (fun imp => marked.contains imp.module) then
        marked := marked.insert n
        changed := true
  return marked

/-- The imports a term still needs beyond `base`: the defining module of every constant
    `base` lacks. (`base.contains` subsumes any "universally imported" allowlist — whatever
    the file already reaches, `Init` included, never shows up as needed.)

    Returns `none` when the term depends on the module currently being elaborated **or on
    any module that transitively imports it** — a stale copy of the current module reaches
    the constructed environment via the project roots, and adding such an `import` to the
    current file would create an import cycle — so callers must drop such a hit entirely.

    Runs in the environment the term was found in (current or constructed). -/
def neededImports (base : Environment) (e : Expr) : MetaM (Option (List Name)) := do
  let env ← getEnv
  let needed := (collectConsts e).toList.filter fun c => !base.contains c
  let mods := (needed.map (moduleOf env)).filter (· != .anonymous) |>.eraseDups
  -- In-scope hits (phase 1, or cross-file hits already covered by imports) skip the
  -- cycle check entirely — it only costs anything for genuinely cross-file hits.
  if mods.isEmpty then return some []
  if base.mainModule != .anonymous then
    let cyclic := reverseImportClosure env base.mainModule
    if mods.any cyclic.contains then return none
  return some mods

/-- Validate a suggestion, ensuring its pretty-printed term parses and gets re-elaborated
    as `type` with no leftover metavariables. -/
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

/-- Enumeration of `Hit` kinds. `exactClose` and `applyPartial` come from library search.
    `rewrite` from Lean core's `rw?` engine; `tacticClose` from the `hint`-style panel. -/
inductive HitKind where
  -- Only `exactClose` are suggested as goal closers.
  | exactClose
  | applyPartial
  -- Report and apply using their tactic text.
  | rewrite
  -- Report and apply using their tactic text.
  | tacticClose
  deriving Inhabited, DecidableEq

/-- One search result. -/
structure Hit where
  /-- A (possibly partial) proof term. -/
  proof   : Expr
  /-- True iff the suggestion alone resolves the goal. I.e., an `exactClose` proof, or a
      `rewrite` which closes by `rfl`. -/
  isFull  : Bool
  /-- Which engine produced this hit. -/
  kind    : HitKind
  /-- Tactic text to insert. -/
  tactic  : String
  /-- Display text. -/
  display : String
  /-- Modules used by the proof but which the base env lacks. -/
  mods    : List Name

/-- Whether `exact h.proof` closes the goal. -/
def Hit.autoCloseable (h : Hit) : Bool :=
  match h.kind with
  | .exactClose => h.isFull
  | _           => false

/-- Find ranked library lemmas for `type`: full closers first, then partial matches.
    Runs in the ambient local context, so local hypotheses are available.
    Diff against the `base` environment to decide which modules still need importing. -/
def searchCandidates (base : Environment) (type : Expr)
    (maxFull : Nat := 5) (maxPartial : Nat := 3) : MetaM (Array Hit) :=
  withoutModifyingState do
  -- Build and validate a fully closing `Hit` from a proof term.
  let mkFullHit (proof : Expr) : MetaM (Option Hit) := do
    let proof := proof.headBeta
    let termStr := toString (← Meta.ppExpr proof)
    if proof.hasExprMVar || !(← roundTrips type termStr) then return none
    let some mods ← neededImports base proof | return none
    let txt := s!"exact {termStr}"
    return some { proof, isFull := true, kind := .exactClose, tactic := txt, display := txt, mods }
  -- Build a partially matching `Hit`.
  let mkPartialHit (name : Name) (proof : Expr) (remaining : List MVarId) :
      MetaM (Option Hit) := do
    let some mods ← neededImports base proof | return none
    let tyStrs ← remaining.mapM fun sg => sg.withContext do
      return s!"⊢ {← Meta.ppExpr (← instantiateMVars (← sg.getType))}"
    return some { proof, isFull := false, kind := .applyPartial, tactic := s!"apply {name}",
                  display := s!"apply {name}   (leaves {remaining.length}: " ++
                    String.intercalate ", " tyStrs ++ ")",
                  mods }
  let .mvar goal0 ← mkFreshExprMVar type | return #[]
  -- intro a ∀-goal's binders, keep its free vars for later abstracting a found proof into
  -- a closed term.
  let (introFvars, searchGoal) ← if type.isForall then goal0.intros else pure (#[], goal0)
  let fvarExprs := introFvars.map Expr.fvar
  -- Find candidates against the goal's conclusion.
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
  -- A direct attempt first: discharge the goal from the local hypotheses alone.
  let directHit? ← try
    let _ ← solveByElim [] (exfalso := true) (goals := [searchGoal]) (maxDepth := 6)
    searchGoal.withContext (mkFullHit (← mkLambdaFVars fvarExprs (← instantiateMVars (mkMVar searchGoal))))
  catch _ => pure none
  if let some h := directHit? then full := full.push h
  -- Try to `apply` the candidate and `solveByElim` its subgoals.
  for cand in candidates do
    if full.size ≥ maxFull && part.size ≥ maxPartial then break
    restoreState s
    let ((g, mctx), (name, declMod)) := cand
    let hit? ← try
      setMCtx mctx
      let newGoals ← g.apply (← mkLibrarySearchLemma name declMod) cfg
      let remaining ← (try solveByElim [] (exfalso := false) (goals := newGoals) (maxDepth := 6)
                        catch _ => pure newGoals)
      searchGoal.withContext do
        let proof ← mkLambdaFVars fvarExprs (← instantiateMVars (mkMVar searchGoal))
        if remaining.isEmpty then mkFullHit proof
        else mkPartialHit name proof remaining
    catch _ => pure none
    match hit? with
    | some h =>
        if h.isFull then
          if full.size < maxFull then full := full.push h
        else
          if part.size < maxPartial then part := part.push h
    | none => pure ()
  return full ++ part

/-- Find ranked rewrite lemmas for `type`, via Lean core's `rw?` engine. -/
def rewriteHits (base : Environment) (type : Expr) (maxHits : Nat := 6) :
    MetaM (Array Hit) := withoutModifyingState do
  let goal0 := (← mkFreshExprMVar type).mvarId!
  -- `intro` a ∀-goal's binders.
  let (_, searchGoal) ← if type.isForall then goal0.intros else pure (#[], goal0)
  -- `createModuleTreeRef` indexes the env we're running in (current or constructed);
  -- `findRewrites` respects the (raised) heartbeat budget. Be defensive: any failure → no hits.
  let results ← searchGoal.withContext do
    try
      let target ← instantiateMVars (← searchGoal.getType)
      let moduleRef ← Lean.Meta.Rewrites.createModuleTreeRef
      let hyps ← Lean.Meta.Rewrites.localHypotheses
      Lean.Meta.Rewrites.findRewrites hyps moduleRef searchGoal target (stopAtRfl := false) (max := maxHits)
    catch _ => pure []
  let mut hits : Array Hit := #[]
  -- Pretty-print under `searchGoal`'s context and the result's mctx.
  for r in results do
    let hit? ← searchGoal.withContext <| withMCtx r.mctx do
      let lem ← instantiateMVars r.expr
      let some mods ← neededImports base lem | return none
      let arrow := if r.symm then "← " else ""
      let tac := s!"rw [{arrow}{toString (← Meta.ppExpr lem)}]"
      let display ←
        if r.rfl? then pure s!"{tac}   (closes by rfl)"
        else match r.newGoal with
          | some g => do pure s!"{tac}   (⊢ {← Meta.ppExpr (← instantiateMVars g)})"
          | none   => pure tac
      pure (some { proof := lem, isFull := r.rfl?, kind := .rewrite, tactic := tac, display, mods })
    if let some hit := hit? then hits := hits.push hit
  return hits

/-- Closed tactics the `hint`-style panel tries: each either solves the goal outright or is
    discarded. Kept to **Lean core** procedures (no Mathlib/aesop dependency); extend freely.
    `decide` is omitted on purpose — it can blow up / loop on large goals. -/
def hintTactics : List String := ["omega", "simp", "trivial"]

/-- The `hint`-style panel: run each closed tactic in `hintTactics` against the goal and keep
    the ones which fully close it.

    Over the constructed environment a tactic (`simp` especially) may succeed only thanks to
    lemmas from unimported modules — its proof term names them, so the same `neededImports`
    post-pass recovers the `import`s to report. Once those modules are imported, the plain
    tactic text reproduces the proof (an imported `@[simp]` lemma is in the active simp set). -/
def hintHits (base : Environment) (type : Expr) : MetaM (Array Hit) := withoutModifyingState do
  let mut hits : Array Hit := #[]
  for tacStr in hintTactics do
    match Lean.Parser.runParserCategory (← getEnv) `tactic tacStr with
    | .error _   => pure ()
    | .ok stx    =>
      -- Run the tactic on a fresh goal of `type` in the ambient local context, and keep it
      -- only if it leaves no subgoals.
      let proof? ← Lean.Elab.Term.TermElabM.run' do
        try
          let goal := (← mkFreshExprMVar type).mvarId!
          let remaining ← Lean.Elab.Tactic.run goal (Lean.Elab.Tactic.evalTactic stx)
          if remaining.isEmpty then return some (← instantiateMVars (mkMVar goal)) else return none
        catch _ => return none
      if let some proof := proof? then
        if let some mods ← neededImports base proof then
          hits := hits.push
            { proof, isFull := true, kind := .tacticClose, tactic := tacStr, display := tacStr, mods }
  return hits

/-- A panel member: given the `base` environment and the goal `type`, produce its hits. -/
abbrev Searcher := Environment → Expr → MetaM (Array Hit)

/-- The searcher panel. -/
def panel : List Searcher :=
  -- `exact` and `apply`, via `librarySearch`
  [ (fun base type => searchCandidates base type)
  -- `rw`, via core's `rw?` engine
  , (fun base type => rewriteHits base type)
  -- `omega`/`simp`/`trivial` closers
  , (fun base type => hintHits base type) ]

/-- The full candidate set for a goal: every panel member's hits. Rank fully closing
    suggestions, first. Then, by fewer imports. Then, any partial matches. -/
def allHits (base : Environment) (type : Expr) : MetaM (Array Hit) := do
  let mut combined : Array Hit := #[]
  for searcher in panel do
    combined := combined ++ (← searcher base type)
  let fulls := combined.filter (·.isFull)
  let parts := combined.filter (fun h => !h.isFull)
  return fulls.filter (·.mods.isEmpty) ++ fulls.filter (fun h => !h.mods.isEmpty) ++ parts

/-- Run a `MetaM` action over an arbitrary environment. -/
def runMetaOver {α : Type} (env : Environment) (opts : Options) (act : MetaM α) : IO α := do
  let coreCtx : Core.Context := { fileName := "<suggest>", fileMap := .ofString "", options := opts }
  let (a, _) ← (act.run').toIO coreCtx { env := env }
  return a

/-- Fingerprint of one root's built `.olean`: its modification time. Lake rebuilds a module
    whenever anything it transitively imports changes, so a root's `.olean` mtime moves on
    *any* rebuild of the library below it — a cheap staleness signal that avoids hashing the
    whole tree. `(0, 0)` when the root has no findable `.olean` (the subsequent
    `importModules` will report that properly). -/
def rootFingerprint (root : Name) : IO (Name × Int × Nat) := do
  try
    let md ← (← Lean.findOLean root).metadata
    return (root, md.modified.sec, md.modified.nsec.toNat)
  catch _ => return (root, 0, 0)

/-- A process-wide cache of the constructed environment.

    Invalidation: the cached env is reused only when (a) every root's fingerprint is
    unchanged — so a `lake build` or a roots reconfiguration rebuilds it — and (b) it
    already contains every module the requesting file imports. (b) makes the single entry
    serve *different files*: reusing a superset environment is sound because
    `neededImports` diffs hits against the caller's `base` env, not the search env.

    Kept to a single entry on purpose — a constructed environment is large. Concurrent
    requests may race to build it; the loser's work is wasted but the result is correct. -/
initialize constructedEnvCache :
    IO.Ref (Option (List (Name × Int × Nat) × Environment)) ← IO.mkRef none

/-- The constructed environment: the file's imports plus `configuredRoots`. Cached; see
    `constructedEnvCache` for the invalidation rules. -/
def constructedEnv (cur : Environment) (opts : Options) : IO Environment := do
  let roots ← configuredRoots opts
  let fingerprints ← roots.mapM rootFingerprint
  let wanted := cur.header.imports.map (·.module) ++ roots.toArray
  if let some (cached, e) ← constructedEnvCache.get then
    if cached == fingerprints && wanted.all (e.header.moduleNames.contains ·) then
      return e
  let extra := roots.toArray.map (fun m => { module := m : Import })
  let e ← importModules (cur.header.imports ++ extra) opts (trustLevel := 1024) (loadExts := true)
  constructedEnvCache.set (some (fingerprints, e))
  return e

/-- Two-phase search: first in the current environment, then in a constructed environment.
    `lctx` and `linsts` carry the goal's hypotheses into both searches. -/
def suggestHits (base : Environment) (opts : Options)
    (lctx : LocalContext) (linsts : LocalInstances) (type : Expr) : IO (Array Hit) := do
  let go (searchEnv : Environment) : IO (Array Hit) :=
    runMetaOver searchEnv opts <| withLCtx lctx linsts (allHits base type)
  let inScope ← go base
  if inScope.any (·.isFull) then return inScope
  let crossFile ← go (← constructedEnv base opts)
  return if crossFile.isEmpty then inScope else crossFile

/-- Render ranked hits as a message. -/
def renderHits (hits : Array Hit) : MessageData :=
  let lines := hits.toList.zipIdx.map fun (h, i) =>
    let imp := if h.mods.isEmpty then ""
      else s!"    [add: {String.intercalate ", " (h.mods.map (fun m => s!"import {m}"))}]"
    s!"  {i + 1}. {h.display}{imp}"
  m!"suggest? — suggestions:\n{String.intercalate "\n" lines}"

/-- The `#suggest (T)` query form. Prints ranked suggestions and imports for the goal type
    `T` with no proof nor goal state. -/
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
/-- The `suggest?` tactic. If no imported lemma closes the goal, `suggest?` also searches
the rest of the project and reports the lemma + the `import` to add. -/
elab (name := suggestImportTac) "suggest?" : tactic => do
  let goal ← getMainGoal
  let opts := searchOpts (← getOptions)
  let curEnv ← getEnv
  let (lctx, linsts, type) ← goal.withContext do
    pure ((← getLCtx), (← getLocalInstances), (← instantiateMVars (← goal.getType)))
  -- Phase 1: in the ambient environment of the current goal.
  let inScope ← goal.withContext (withOptions (fun _ => opts) (allHits curEnv type))
  match inScope.find? (·.autoCloseable) with
  | some h =>
      -- An imported lemma closes it: close the goal and emit "Try this".
      closeMainGoal `suggest? h.proof
      addExactSuggestion (← getRef) h.proof
      if inScope.size > 1 then logInfo (renderHits inScope)
  | none =>
      if inScope.any (·.isFull) then
        -- An in-scope rewrite closes the goal by `rfl`, but isn't `exact`-able.
        logInfo (renderHits inScope)
        return
      -- Phase 2: in a constructed env.
      let crossFile ← runMetaOver (← constructedEnv curEnv opts) opts
        (withLCtx lctx linsts (allHits curEnv type))
      let hits := if crossFile.isEmpty then inScope else crossFile
      if hits.isEmpty then
        throwError "suggest? found nothing that applies."
      else
        logInfo (renderHits hits)

/-! ## The lightbulb code action for `suggest?`

A `WorkspaceEdit` which inserts the suggested `import` after the last existing import, and
which replaces `suggest?` with the top suggestion. -/

/-- The line index of the last `import` in the file's *header*: scan from the top, skipping
    comments and blank lines, and stop at the first declaration — so an `import` appearing
    later in the file (in a comment, string, or doc example) can't hijack the insertion
    point. `none` when the header has no imports (insert at the very top instead). -/
def lastHeaderImportLine (srcLines : Array String) : Option Nat := Id.run do
  let occ (s pat : String) : Nat := (s.splitOn pat).length - 1
  let mut lastImp : Option Nat := none
  let mut commentDepth : Nat := 0  -- Lean block comments nest
  for i in [0:srcLines.size] do
    let line := (srcLines[i]?.getD "").trim
    if commentDepth > 0 then
      commentDepth := commentDepth + occ line "/-" - occ line "-/"
    else if line.startsWith "import " || line.startsWith "public import " then
      lastImp := some i
    else if line.startsWith "/-" then
      commentDepth := 1 + occ (line.drop 2) "/-" - occ line "-/"
    else if line.isEmpty || line.startsWith "--" || line == "module" || line == "prelude" then
      pure ()  -- header trivia (copyright comments, blank lines, module-system keywords)
    else
      break
  return lastImp

open Lean Server RequestM Lean.Lsp Batteries.CodeAction in
@[tactic_code_action suggestImportTac]
def suggestImportCodeAction : TacticCodeAction := fun _params _snap ctx _stack node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  if info.goalsBefore.isEmpty then return #[]
  let doc ← readDoc
  let eager : CodeAction := { title := "suggest?: insert import & apply suggestion", kind? := "quickfix" }
  return #[{
    eager
    -- Lazily build the constructed environment.
    lazy? := some do
      let goal := info.goalsBefore[0]!
      let opts := searchOpts ctx.options
      let (lctx, linsts, type) ← ctx.runMetaM {} (goal.withContext do
        pure ((← getLCtx), (← getLocalInstances), (← instantiateMVars (← goal.getType))))
      let some h := (← suggestHits ctx.env opts lctx linsts type)[0]? | return eager
      -- Replace `suggest?` with the suggested tactic.
      let some tacStart := info.stx.getPos? | return eager
      let some tacStop := info.stx.getTailPos? | return eager
      let tacPos := doc.meta.text.utf8PosToLspPos tacStart
      let tacEnd := doc.meta.text.utf8PosToLspPos tacStop
      let tacEdit : TextEdit := { range := ⟨tacPos, tacEnd⟩, newText := h.tactic }
      -- Insert the needed import(s) at the end of the file's import header.
      let srcLines := (doc.meta.text.source.splitOn "\n").toArray
      let importText := String.intercalate "\n" (h.mods.map fun m => s!"import {m}")
      let importEdit : TextEdit :=
        match lastHeaderImportLine srcLines with
        | some i =>
          let pos : Lsp.Position := ⟨i, (srcLines[i]?.getD "").length⟩
          { range := ⟨pos, pos⟩, newText := "\n" ++ importText }
        | none => { range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, newText := importText ++ "\n" }
      let edits := if h.mods.isEmpty then #[tacEdit] else #[importEdit, tacEdit]
      let title :=
        if h.mods.isEmpty then s!"Replace with: {h.tactic}"
        else s!"Add import {h.mods.head!} & replace with: {h.tactic}"
      return { eager with
        title
        edit? := some <| .ofTextDocumentEdit { textDocument := doc.versionedIdentifier, edits } }
  }]

end LeanSuggest
