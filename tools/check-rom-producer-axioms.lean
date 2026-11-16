import ZiskFv.Compliance.RomProducerFlags
import Lean

open Lean Elab Command
set_option maxHeartbeats 0

private def rootModule (env : Environment) (declName : Name) : Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => Name.anonymous

private def dependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut refs := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    refs := refs ++ value.getUsedConstants
  if let .inductInfo info := ci then
    refs := refs ++ info.ctors.toArray
  return refs

private def nodeKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"
  | .quotInfo _ => "quotient"

private def pathTo (parents : Std.HashMap Name Name) (root target : Name) : List Name :=
  let rec loop : Nat → Name → List Name → List Name
    | 0, current, acc => current :: acc
    | fuel + 1, current, acc =>
      if current == root then current :: acc
      else match parents[current]? with
        | some parent => loop fuel parent (current :: acc)
        | none => current :: acc
  loop (parents.size + 1) target []

private def scan (env : Environment) (root : Name)
    (cache : IO.Ref (Std.HashMap Name (Array Name))) : IO (Array Name × Std.HashMap Name Name) := do
  let mut todo := [root]
  let mut seen : NameSet := {}
  let mut parents : Std.HashMap Name Name := {}
  let mut axioms : Array Name := #[]
  while !todo.isEmpty do
    let current := todo.head!
    todo := todo.tail!
    if seen.contains current then continue
    seen := seen.insert current
    if let some ci := env.checked.get.find? current then
      if let .axiomInfo _ := ci then axioms := axioms.push current
      let cached ← cache.get
      let refs ← match cached[current]? with
        | some refs => pure refs
        | none =>
          let refs := dependencies ci
          cache.modify (·.insert current refs)
          pure refs
      for next in refs do
        if !seen.contains next then
          if !parents.contains next then parents := parents.insert next current
          todo := next :: todo
  return (axioms.qsort Name.quickLt, parents)

run_cmd do
  let env ← getEnv
  let selected := #[`ProductionM2.RomFlags, `ZiskFv.Compliance.RomProducerFlags]
  let roots := (env.constants.toList.filter fun (declName, _) =>
    selected.contains (rootModule env declName)).toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  let cache ← liftIO (IO.mkRef ({} : Std.HashMap Name (Array Name)))
  let mut union : NameSet := {}
  let mut records : Array Json := #[]
  for (root, ci) in roots do
    let (raw, parents) ← liftIO (scan env root cache)
    let checked ← Lean.collectAxioms root
    let checked := checked.qsort Name.quickLt
    unless raw == checked do
      throwError "Full graph/Lean.collectAxioms disagreement at {root}: {raw} versus {checked}"
    for axiomName in raw do union := union.insert axiomName
    let paths := raw.map fun axiomName => Json.mkObj [
      ("axiom", toJson axiomName.toString),
      ("path", toJson ((pathTo parents root axiomName).map Name.toString))]
    records := records.push (Json.mkObj [
      ("root", toJson root.toString), ("module", toJson (rootModule env root).toString),
      ("kind", toJson (nodeKind ci)), ("raw_axioms", toJson (raw.map Name.toString)),
      ("collectAxioms_crosscheck", toJson true), ("paths", Json.arr paths)])
  let report := Json.mkObj [
    ("modules", toJson (selected.map Name.toString)), ("root_count", toJson roots.size),
    ("raw_axiom_union", toJson ((union.toList.mergeSort Name.quickLt).map Name.toString)),
    ("roots", Json.arr records)]
  liftIO (IO.FS.writeFile "build/rom-flags-all-roots-raw.json" (report.pretty ++ "\n"))
  logInfo m!"Audited ALL {roots.size} roots; RAW unfiltered union {union.toList}"
