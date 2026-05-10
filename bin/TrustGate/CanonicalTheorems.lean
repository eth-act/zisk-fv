/-
TrustGate.CanonicalTheorems — environment-side enumeration of the canonical
`equiv_<OP>` theorems whose trust surface the V2 gate polices.

A name is "canonical" iff:
  * its leaf component matches `equiv_[A-Z][A-Z0-9]*` (no underscore-suffix —
    so `equiv_ADD_sail`, `equiv_ADD_from_bus`, etc. are all rejected);
  * its parent namespace is `ZiskFv.Equivalence.<File>`.

This mirrors the V1 textual regex semantically — a renamed/aliased entry
point would also dodge V1, so V2 walks the ELABORATED environment.
-/
import Lean

open Lean

namespace TrustGate.CanonicalTheorems

/-- True iff `s` matches `equiv_[A-Z][A-Z0-9]*` exactly. -/
def isCanonicalLeaf (s : String) : Bool :=
  if !"equiv_".isPrefixOf s then false
  else
    let rest := s.drop "equiv_".length
    if rest.isEmpty then false
    else
      rest.all (fun c => (c.isUpper || c.isDigit))

/-- True iff `n` is a canonical equiv-theorem name. -/
def isCanonical (n : Name) : Bool :=
  match n with
  | .str (.str (.str (.str .anonymous "ZiskFv") "Equivalence") _file) leaf =>
    isCanonicalLeaf leaf
  | _ => false

/-- Walk the environment, return all canonical theorem names sorted. -/
def findCanonical (env : Environment) : Array Name :=
  let acc :=
    env.constants.fold (init := (#[] : Array Name)) fun out n ci =>
      match ci with
      | .thmInfo _ => if isCanonical n then out.push n else out
      | _          => out
  acc.qsort (fun a b => a.toString < b.toString)

end TrustGate.CanonicalTheorems
