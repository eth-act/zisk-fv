import ZiskFv.AirsClean.PublicIo
import ZiskFv.AirsClean.PublicIoSource
import ZiskFv.AirsClean.SourcePublicVerifier
import TrustGate.AxiomClosure

open Lean

private def immediateDependencies (env : Environment) (declName : Name) : Array Name :=
  match env.checked.get.find? declName with
  | some (.axiomInfo info) => info.type.getUsedConstants
  | some (.defnInfo info) => info.type.getUsedConstants ++ info.value.getUsedConstants
  | some (.thmInfo info) => info.type.getUsedConstants ++ info.value.getUsedConstants
  | some (.opaqueInfo info) => info.type.getUsedConstants ++ info.value.getUsedConstants
  | some (.quotInfo _) => #[]
  | some (.ctorInfo info) => info.type.getUsedConstants
  | some (.recInfo info) => info.type.getUsedConstants
  | some (.inductInfo info) => info.type.getUsedConstants ++ info.ctors.toArray
  | none => #[]

private def dependencyGraph (env : Environment) (roots : Array Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut queue := roots
  let mut queued : NameSet := {}
  for root in roots do
    queued := queued.insert root
  let mut next := 0
  let mut graph : Std.HashMap Name (Array Name) := {}
  while next < queue.size do
    let declName := queue[next]!
    next := next + 1
    let children := immediateDependencies env declName
    graph := graph.insert declName children
    for child in children do
      unless queued.contains child do
        queued := queued.insert child
        queue := queue.push child
  return graph

private def axiomPaths (graph : Std.HashMap Name (Array Name))
    (root : Name) (axioms : Array Name) : Except String (Array Json) := do
  let mut queue := #[root]
  let mut parents : Std.HashMap Name Name := {}
  parents := parents.insert root root
  let mut next := 0
  let mut paths := #[]
  while next < queue.size && paths.size < axioms.size do
    let declName := queue[next]!
    next := next + 1
    if axioms.contains declName then
      let mut path := #[declName]
      let mut current := declName
      while current != root do
        let some parent := parents[current]? | throw s!"Missing parent for {current}"
        current := parent
        path := path.push parent
      paths := paths.push <| Json.mkObj [
        ("axiom", toJson declName.toString),
        ("path", toJson (path.reverse.map Name.toString))]
    for child in graph[declName]?.getD #[] do
      unless parents.contains child do
        parents := parents.insert child declName
        queue := queue.push child
  unless paths.size == axioms.size do
    throw s!"Incomplete full-type/value paths for {root}"
  return paths

open Lean in
run_meta do
  let env ← getEnv
  let modules := #[`ZiskFv.AirsClean.PublicIo, `ZiskFv.AirsClean.PublicIoSource,
    `ZiskFv.AirsClean.SourcePublicVerifier]
  let roots := env.constants.fold (init := (#[] : Array Name)) fun result decl _ =>
    match env.getModuleIdxFor? decl with
    | some index =>
      match env.header.moduleNames[index.toNat]? with
      | some owner => if modules.contains owner then result.push decl else result
      | none => result
    | none => result
  let roots := roots.qsort (fun left right => left.toString < right.toString)
  for moduleName in modules do
    unless roots.any (fun declName =>
      match env.getModuleIdxFor? declName with
      | some index => env.header.moduleNames[index.toNat]? == some moduleName
      | none => false) do
      throwError "No declarations found for expected module {moduleName}"
  let axioms := TrustGate.AxiomClosure.rawAxiomUnion env roots
  let graph := dependencyGraph env roots
  let mut perRoot := #[]
  let mut independentUnion : Array Name := #[]
  let mut seenAxioms : NameSet := {}
  for root in roots do
    let independent ← Lean.collectAxioms root
    let independent := independent.qsort (fun left right => left.toString < right.toString)
    let maintained := TrustGate.AxiomClosure.rawAxiomDepsForTheorem env root
    unless independent == maintained do
      throwError "Independent Lean.collectAxioms mismatch for {root}"
    let paths ← match axiomPaths graph root independent with
      | .ok paths => pure paths
      | .error message => throwError "{message}"
    perRoot := perRoot.push <| Json.mkObj [
      ("declaration", toJson root.toString),
      ("raw_axioms", toJson (independent.map Name.toString)),
      ("paths", Json.arr paths)]
    for axiomName in independent do
      unless seenAxioms.contains axiomName do
        seenAxioms := seenAxioms.insert axiomName
        independentUnion := independentUnion.push axiomName
  independentUnion := independentUnion.qsort (fun left right => left.toString < right.toString)
  unless independentUnion == axioms do
    throwError "Independent per-root Lean.collectAxioms union does not match RAW union"
  let report := Json.mkObj [
    ("modules", toJson (modules.map Name.toString)),
    ("declarations", toJson (roots.map Name.toString)),
    ("elaborated_types_and_values", toJson true),
    ("axiom_filter", toJson "none"),
    ("raw_axioms", toJson (axioms.map Name.toString)),
    ("independent_collectAxioms_union", toJson (independentUnion.map Name.toString)),
    ("independent_per_root_and_union_match", toJson true),
    ("path_edge_semantics", toJson "full checked type AND value; inductive constructors included"),
    ("per_root", Json.arr perRoot)]
  liftM <| IO.FS.writeFile
    "/home/cody/zisk-fv-source-public-verifier-port/build/public-io418-evidence/source-public-verifier-port/full-raw-axioms.json" report.pretty
  logInfo m!"Owned declarations: {roots.size}; FULL type+value RAW axiom union: {axioms}"
