import Lean
import ZiskFv.AirsClean.MemAlignWriteByte.NativeInstance
import ZiskFv.AirsClean.MemAlignWriteByte.NativeBus88

open Lean Elab Command
namespace NativeWriteByteInstanceRawClosureAudit

def targetModules : Array Name := #[
  `ZiskFv.AirsClean.MemAlignWriteByte.NativeInstance,
  `ZiskFv.AirsClean.MemAlignWriteByte.NativeBus88]

def sourceModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => Name.anonymous

def kind (info : ConstantInfo) : String :=
  match info with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"

/-- Explicit value cases match the installed Lean.CollectAxioms collector,
including opaque bodies. Nothing is pruned by external namespace or depth. -/
def references (info : ConstantInfo) : Array (Name × String) := Id.run do
  let mut result := info.type.getUsedConstants.map (fun name => (name, "type"))
  match info with
  | .defnInfo value =>
    result := result ++ value.value.getUsedConstants.map (fun name => (name, "definition-value"))
  | .thmInfo value =>
    result := result ++ value.value.getUsedConstants.map (fun name => (name, "theorem-value"))
  | .opaqueInfo value =>
    result := result ++ value.value.getUsedConstants.map (fun name => (name, "opaque-value"))
  | _ => pure ()
  if let .inductInfo value := info then
    result := result ++ value.ctors.toArray.map (fun name => (name, "constructor"))
  return result

def fullGraph (env : Environment) (roots : Array Name) :
    Array Name × Std.HashMap Name (Name × String) := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut queue := roots
  let mut parents : Std.HashMap Name (Name × String) := {}
  for root in roots do seen := seen.insert root
  let mut index := 0
  while index < queue.size do
    let current := queue[index]!
    index := index + 1
    if let some info := env.checked.get.find? current then
      for (next, edge) in references info do
        if !seen.contains next then
          seen := seen.insert next
          parents := parents.insert next (current, edge)
          queue := queue.push next
  return (queue, parents)

partial def pathTo (parents : Std.HashMap Name (Name × String)) (name : Name) :
    List (Name × String) :=
  match parents[name]? with
  | none => [(name, "seed")]
  | some (parent, edge) => pathTo parents parent ++ [(name, edge)]

def sortNames (names : Array Name) : Array Name :=
  names.qsort (fun left right => left.toString < right.toString)

def namesJson (names : Array Name) : Json := toJson (names.map Name.toString)

def summarize (env : Environment) (reachable : Array Name) :
    Array Name × Array Name × Array Name := Id.run do
  let mut axioms : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut opaqueValues : Array Name := #[]
  for name in reachable do
    match env.checked.get.find? name with
    | some (.axiomInfo _) => axioms := axioms.push name
    | some (.opaqueInfo _) => opaqueValues := opaqueValues.push name
    | some _ => pure ()
    | none => missing := missing.push name
  return (sortNames axioms, sortNames missing, sortNames opaqueValues)

def pathsJson (env : Environment) (parents : Std.HashMap Name (Name × String))
    (axioms : Array Name) : Array Json :=
  axioms.map fun axiomName => Json.mkObj [
    ("axiom", toJson axiomName.toString),
    ("module", toJson (sourceModule env axiomName).toString),
    ("path", toJson ((pathTo parents axiomName).map fun (name, edge) =>
      Json.mkObj [("name", toJson name.toString), ("edge", toJson edge)]))]

run_cmd do
  let env ← getEnv
  let roots := sortNames (env.constants.fold (init := (#[] : Array Name)) fun result name _ =>
    if targetModules.contains (sourceModule env name) then result.push name else result)
  for target in targetModules do
    unless roots.any (fun name => sourceModule env name == target) do
      throwError "No actual declarations found for assigned target {target}"
  let mut rawState : Lean.CollectAxioms.State := {}
  let mut entries : Array Json := #[]
  let mut mismatches : Array Name := #[]
  for root in roots do
    let (_, state) := ((Lean.CollectAxioms.collect root).run env).run {}
    rawState := ((Lean.CollectAxioms.collect root).run env).run rawState |>.snd
    let kernelAxioms := sortNames state.axioms
    let (reachable, parents) := fullGraph env #[root]
    let (graphAxioms, missing, opaqueValues) := summarize env reachable
    let rootMatches := graphAxioms == kernelAxioms && missing.isEmpty
    if !rootMatches then mismatches := mismatches.push root
    let info := env.checked.get.find? root |>.get!
    entries := entries.push <| Json.mkObj [
      ("name", toJson root.toString),
      ("module", toJson (sourceModule env root).toString),
      ("kind", toJson (kind info)),
      ("kernel_raw_axioms", namesJson kernelAxioms),
      ("independent_graph_axioms", namesJson graphAxioms),
      ("crosscheck_matches", toJson rootMatches),
      ("axiom_paths", toJson (pathsJson env parents graphAxioms)),
      ("reachable_constant_count", toJson reachable.size),
      ("opaque_values_traversed", namesJson opaqueValues),
      ("missing_constants", namesJson missing)]
  let mut moduleEntries : Array Json := #[]
  let mut moduleMismatches : Array Name := #[]
  for target in targetModules do
    let moduleRoots := roots.filter (fun root => sourceModule env root == target)
    let mut moduleState : Lean.CollectAxioms.State := {}
    for root in moduleRoots do
      moduleState := ((Lean.CollectAxioms.collect root).run env).run moduleState |>.snd
    let moduleAxioms := sortNames moduleState.axioms
    let (reachable, parents) := fullGraph env moduleRoots
    let (graphAxioms, missing, opaqueValues) := summarize env reachable
    let moduleMatches := graphAxioms == moduleAxioms && missing.isEmpty
    if !moduleMatches then moduleMismatches := moduleMismatches.push target
    moduleEntries := moduleEntries.push <| Json.mkObj [
      ("module", toJson target.toString),
      ("actual_roots", namesJson moduleRoots),
      ("seed_count", toJson moduleRoots.size),
      ("kernel_raw_axioms", namesJson moduleAxioms),
      ("independent_graph_axioms", namesJson graphAxioms),
      ("crosscheck_matches", toJson moduleMatches),
      ("axiom_paths", toJson (pathsJson env parents graphAxioms)),
      ("reachable_constant_count", toJson reachable.size),
      ("opaque_values_traversed", namesJson opaqueValues),
      ("missing_constants", namesJson missing)]
  let rawUnion := sortNames rawState.axioms
  let (reachable, parents) := fullGraph env roots
  let (graphAxioms, missing, opaqueValues) := summarize env reachable
  let unionMatches := graphAxioms == rawUnion && missing.isEmpty
  let report := Json.mkObj [
    ("target_modules", namesJson targetModules),
    ("selection", toJson "ALL actual declarations defined in BOTH target modules, including private/compiler-generated/constructors; no assumed root count"),
    ("traversal", toJson "EVERY referenced type plus explicit defnInfo/thmInfo/opaqueInfo value and inductive constructors; no namespace/external pruning, allowlist, or depth cutoff"),
    ("crosscheck", toJson "Independent full graph and installed Lean.CollectAxioms for EACH actual root, EACH defining-module union, and combined union"),
    ("seed_count", toJson roots.size),
    ("declarations", toJson entries),
    ("module_unions", toJson moduleEntries),
    ("mismatched_roots", namesJson mismatches),
    ("mismatched_module_unions", namesJson moduleMismatches),
    ("raw_axiom_union", namesJson rawUnion),
    ("independent_graph_axiom_union", namesJson graphAxioms),
    ("union_crosscheck_matches", toJson unionMatches),
    ("axiom_paths", toJson (pathsJson env parents graphAxioms)),
    ("reachable_constant_count", toJson reachable.size),
    ("reachable_constants", namesJson (sortNames reachable)),
    ("opaque_values_traversed", namesJson opaqueValues),
    ("missing_constants", namesJson missing)]
  liftIO <| IO.FS.writeFile "build/writebyte-instance-gate/raw-closure.json" (report.pretty ++ "\n")
  logInfo m!"RAW closure: {roots.size} actual roots, {reachable.size} constants, {opaqueValues.size} opaque values, kernel union {rawUnion}, independent union {graphAxioms}"
  unless mismatches.isEmpty && moduleMismatches.isEmpty && unionMatches do
    throwError "Opaque-complete RAW crosscheck FAILED: roots {mismatches}, modules {moduleMismatches}, union {unionMatches}"

end NativeWriteByteInstanceRawClosureAudit
