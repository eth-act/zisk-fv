import TrustGate.ConstantClosure
import TrustGate.AxiomClosure

open Lean

namespace TrustGate.Dependencies

/-- The accounting graph includes generated declarations as well as project declarations.
Unlike the presentation-only proof tree, it retains compiler-generated helper nodes. -/
def included (n : Name) : Bool :=
  ConstantClosure.isProjectName n || n.getRoot == `Extraction ||
    n.toString.startsWith "_private.Extraction." ||
    (n.toString.splitOn ".extraction.").length > 1

def namesJson (names : NameSet) : Json :=
  toJson ((names.toList.filter included).map Name.toString |>.mergeSort (· < ·))

/-- The assertion side of a component correspondence must be equality to zero. -/
def isZero (e : Expr) : Bool :=
  let literalZero (v : Expr) := match v with
    | .lit (.natVal 0) => true
    | _ => false
  literalZero e ||
    (e.isAppOfArity `OfNat.ofNat 3 && literalZero e.getAppArgs[1]!)

/-- Validate the compiled manifest theorem's elaborated boundary, not its source spelling
or its unchecked index list. Both sides remain visible even for an `Iff.rfl` proof. -/
def correspondence (env : Environment) (ci : ConstantInfo) : Option Json := do
  let .thmInfo _ := ci | none
  let parts := ci.name.toString.splitOn "."
  let ["Extraction", "Components", air, "Manifest", leaf] := parts | none
  if !leaf.startsWith "constraint_" || !leaf.endsWith "_correspondence" then none else do
    let index := ((leaf.drop 11).toString.dropEnd 15).toString
    let some _ := index.toNat? | none
    let mut body := ci.type
    while body matches .forallE .. do
      body := body.bindingBody!
    let args := body.getAppArgs
    if !body.isAppOfArity `Iff 2 then none else do
      let raw := s!"{air}.extraction.constraint_{index}_every_row".toName
      if args[1]!.getAppFn.constName? != some raw then none else do
        let model := s!"ZiskFv.AirsClean.{air}.main".toName
        let source := s!"Extraction.Components.{air}.Manifest.sourceRow".toName
        let refs := ConstantClosure.gatherConsts args[0]! {}
        if !args[0]!.isAppOfArity `Eq 3 || !isZero args[0]!.getAppArgs[2]! ||
            !refs.contains model || !refs.contains source then none
        else some <| Json.mkObj [
          ("theorem", toJson ci.name.toString), ("constraint", toJson raw.toString),
          ("model", toJson model.toString),
          ("axioms", toJson ((AxiomClosure.rawAxiomDepsForTheorem env ci.name).map Name.toString))]

/-- Stable, lossless-for-accounting declaration graph over the loaded environment.
Only library leaves that cannot depend on project/generated declarations are pruned. -/
def report (env : Environment) : Json := Id.run do
  let nodes := env.constants.fold (init := #[]) fun acc n ci =>
    if included n then acc.push (n, ci) else acc
  let nodes := nodes.qsort (fun a b => a.1.toString < b.1.toString)
  let mut declarations : Array Json := #[]
  let mut correspondences : Array Json := #[]
  for (n, ci) in nodes do
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | _ => "definition"
    let mut body := ci.type
    while body matches .forallE .. do
      body := body.bindingBody!
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("module", toJson (ConstantClosure.moduleOf env n)),
      ("kind", toJson kind),
      ("relation", toJson (body.isAppOfArity `Iff 2 || body.isAppOfArity `Eq 3)),
      ("type", namesJson (ConstantClosure.gatherConsts ci.type {})),
      ("value", namesJson (ci.value?.map (ConstantClosure.gatherConsts · {}) |>.getD {}))]
    if let some proof := correspondence env ci then
      correspondences := correspondences.push proof
  return Json.mkObj [("schema_version", toJson (1 : Nat)),
    ("declarations", toJson declarations), ("correspondences", toJson correspondences)]

end TrustGate.Dependencies
