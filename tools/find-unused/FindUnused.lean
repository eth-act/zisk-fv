import Lean
import ZiskFv

/-!
Systematic dead-code detector for ZiskFv.Equivalence.*.

Computes transitive forward closure (FORWARD edges = "uses") from the
63 canonical `equiv_<OP>` roots. Anything declared under
`ZiskFv.Equivalence.*` that's not in the closure is genuinely dead.
-/

open Lean

namespace ZiskFv.FindUnused

private def isProjectName (n : Name) : Bool :=
  n.toString.startsWith "ZiskFv."

private def isInEquivalence (n : Name) : Bool :=
  n.toString.startsWith "ZiskFv.Equivalence."

/-- Canonical public surface: `ZiskFv.Equivalence.<File>.equiv_<OP>`
    where `<OP>` is uppercase + digits only (no underscore-suffix). -/
private def isCanonical (n : Name) : Bool := Id.run do
  let s := n.toString
  unless s.startsWith "ZiskFv.Equivalence." do return false
  let rest := s.drop "ZiskFv.Equivalence.".length
  let parts := rest.splitOn "."
  unless parts.length = 2 do return false
  let inner := parts[1]!
  unless inner.startsWith "equiv_" do return false
  let opPart := inner.drop "equiv_".length
  return opPart.length > 0 && opPart.all (fun c => c.isUpper || c.isDigit)

end ZiskFv.FindUnused

open ZiskFv.FindUnused in
#eval show MetaM Unit from do
  let env ← getEnv
  -- Forward edges: caller → list of callees (project-internal only).
  let mut forward : Std.HashMap Name (Array Name) := {}
  let mut canonicals : Array Name := #[]
  for (caller, ci) in env.constants.toList do
    unless isProjectName caller do continue
    if isCanonical caller then canonicals := canonicals.push caller
    let typeDeps := ci.type.getUsedConstants
    let valueDeps : Array Name :=
      match ci.value? with
      | some v => v.getUsedConstants
      | none => #[]
    let allDeps := (typeDeps ++ valueDeps).filter
      (fun n => isProjectName n && n != caller)
    forward := forward.insert caller allDeps
  IO.println s!"# Canonical roots: {canonicals.size}"
  -- BFS from canonicals.
  let mut alive : Std.HashSet Name := {}
  let mut frontier : Array Name := canonicals
  for c in canonicals do alive := alive.insert c
  while !frontier.isEmpty do
    let mut nextFrontier : Array Name := #[]
    for n in frontier do
      for callee in forward.getD n #[] do
        unless alive.contains callee do
          alive := alive.insert callee
          nextFrontier := nextFrontier.push callee
    frontier := nextFrontier
  IO.println s!"# Alive (reachable from canonicals): {alive.size}"
  -- Dead = ZiskFv.Equivalence.* declarations not in the alive set.
  let mut dead : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isInEquivalence n && !alive.contains n then
      dead := dead.push n
  IO.println s!"# Dead under ZiskFv.Equivalence.*: {dead.size}"
  IO.println ""
  let sorted := dead.qsort (fun a b => a.toString < b.toString)
  for n in sorted do
    IO.println n
