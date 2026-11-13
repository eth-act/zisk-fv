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

/-- Read a literal assertion position, never an unchecked manifest index list. -/
def numeral? (e : Expr) : Option Nat :=
  let literal? (v : Expr) := match v with
    | .lit (.natVal n) => some n
    | _ => none
  if e.isAppOfArity `OfNat.ofNat 3 then literal? e.getAppArgs[1]! else literal? e

/-- Reconstruct the complete generated assertion/constraint boundary in the
elaborated local context. Extra hypotheses, unrelated mentions of `main`, and
the default value of an out-of-range list access cannot stand in for a proof. -/
def correspondence (ci : ConstantInfo) : Meta.MetaM (Option Json) := do
  let .thmInfo _ := ci | return none
  if ci.name.getRoot != `Extraction then return none
  let ["Extraction", "Components", air, "Manifest", leaf] := ci.name.toString.splitOn "."
    | return none
  if !leaf.startsWith "constraint_" || !leaf.endsWith "_correspondence" then return none
  let index := ((leaf.drop 11).toString.dropEnd 15).toString
  let some _ := index.toNat? | return none
  let raw := s!"{air}.extraction.constraint_{index}_every_row".toName
  let model := s!"ZiskFv.AirsClean.{air}.main".toName
  let source := s!"Extraction.Components.{air}.Manifest.sourceRow".toName
  Meta.forallTelescope ci.type fun params body => do
    -- Exactly C, its Circuit instance, c, r, offset, env; no proof promises.
    if params.size != 6 || !body.isAppOfArity `Iff 2 then return none
    let sides := body.getAppArgs
    if sides[1]!.getAppFn.constName? != some raw || !sides[0]!.isAppOfArity `Eq 3 then
      return none
    let evaluated := sides[0]!.getAppArgs[1]!
    if !evaluated.isApp then return none
    let selected := evaluated.appArg!
    if !selected.isAppOfArity `GetElem?.getElem! 8 then return none
    let some position := numeral? selected.getAppArgs[7]! | return none
    let row ← Meta.mkAppOptM source
      #[some params[0]!, some params[1]!, some params[2]!, some params[3]!]
    let main ← Meta.mkAppM model #[row]
    let operations ← Meta.mkAppM `Circuit.operations #[main, params[4]!]
    let constraints ← Meta.mkAppM `Operations.constraints #[operations]
    let length ← Meta.reduce (← Meta.mkAppM `List.length #[constraints])
    let some length := numeral? length | return none
    if position >= length then return none
    let assertion ← Meta.mkAppM `GetElem?.getElem! #[constraints, mkNatLit position]
    let value ← Meta.mkAppM `Expression.eval #[params[5]!, assertion]
    let zero ← Meta.mkAppOptM `OfNat.ofNat #[some (← Meta.inferType value), some (mkNatLit 0), none]
    let lhs ← Meta.mkEq value zero
    let arity := sides[1]!.getAppNumArgs
    if arity < 4 then return none
    let rawArgs := (Array.replicate arity none)
      |>.set! 0 (some params[0]!)
      |>.set! (arity - 3) (some params[1]!)
      |>.set! (arity - 2) (some params[2]!)
      |>.set! (arity - 1) (some params[3]!)
    let rhs ← Meta.mkAppOptM raw rawArgs
    let expected ← instantiateMVars (mkApp2 (mkConst `Iff) lhs rhs)
    if expected.hasMVar || !(← Meta.isDefEq body expected) then return none
    let env ← getEnv
    return some <| Json.mkObj [
      ("theorem", toJson ci.name.toString), ("constraint", toJson raw.toString),
      ("model", toJson model.toString), ("position", toJson position),
      ("axioms", toJson ((AxiomClosure.rawAxiomDepsForTheorem env ci.name).map Name.toString))]

/-- Stable, lossless-for-accounting declaration graph over the loaded environment.
Only library leaves that cannot depend on project/generated declarations are pruned. -/
def report : Meta.MetaM Json := do
  let env ← getEnv
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
    if let some proof ← correspondence ci then
      correspondences := correspondences.push proof
  return Json.mkObj [("schema_version", toJson (1 : Nat)),
    ("declarations", toJson declarations), ("correspondences", toJson correspondences)]

end TrustGate.Dependencies
