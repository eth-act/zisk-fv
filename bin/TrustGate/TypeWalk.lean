/-
TrustGate.TypeWalk — walk the elaborated parameter binders of a canonical
theorem and detect forbidden const references after closure under
reducible definitions.

This is the V2 anti-aliasing layer: an `abbrev SilentSpec :=
LeanRV64D.Functions.execute` wrapper would dodge V1's regex, but the
const-closure walk follows the alias's definition body and the
underlying forbidden Name surfaces.

We avoid `MetaM` reduction here — naive `whnfR`-recursion explodes
on the deeply-elaborated Sail/circuit types in `equiv_<OP>` binders.
Instead we do an environment-side static closure: for each const
appearing in the binder type, if its definition is `abbrev` or has
`reducible` reducibility hint, we unfold by descending into its
value's syntactic constants. Bounded by the env's const count.
-/
import Lean

open Lean

namespace TrustGate.TypeWalk

/-- Gather every distinct `Expr.const` Name appearing syntactically in `e`. -/
partial def gatherConsts (e : Expr) (acc : NameSet) : NameSet :=
  match e with
  | .const n _      => acc.insert n
  | .app f a        => gatherConsts a (gatherConsts f acc)
  | .lam _ t b _    => gatherConsts b (gatherConsts t acc)
  | .forallE _ t b _ => gatherConsts b (gatherConsts t acc)
  | .letE _ t v b _ => gatherConsts b (gatherConsts v (gatherConsts t acc))
  | .mdata _ b      => gatherConsts b acc
  | .proj _ _ b     => gatherConsts b acc
  | _               => acc

/-- True iff this constant should be transparently unfolded for the
const-closure walk: definitions whose body is itself part of the
"shape" reviewers see. Catches `abbrev` and `@[reducible] def`. -/
def shouldUnfold (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo d =>
    match d.hints with
    | .abbrev => true
    | .regular n => n > 0  -- @[reducible] sets a positive depth hint
    | .opaque => false
  | _ => false

/-- Compute the closure of `init` Names under reducible-definition
unfolding. Each Name's definition body's syntactic consts are added if
the Name is a reducible/abbrev definition. -/
partial def reducibleClosure (env : Environment) (init : NameSet) : NameSet :=
  go init init.toList {}
where
  go (acc : NameSet) (todo : List Name) (visited : NameSet) : NameSet :=
    match todo with
    | [] => acc
    | n :: rest =>
      if visited.contains n then
        go acc rest visited
      else
        let visited' := visited.insert n
        match env.find? n with
        | none => go acc rest visited'
        | some ci =>
          if shouldUnfold ci then
            -- Pull defn body's consts into the closure.
            let body := match ci with | .defnInfo d => d.value | _ => default
            let bodyConsts := gatherConsts body {}
            let newOnes := bodyConsts.toList.filter (!acc.contains ·)
            let acc' := bodyConsts.toList.foldl (·.insert ·) acc
            go acc' (newOnes ++ rest) visited'
          else
            go acc rest visited'

/-- A binder-level forbidden-type hit. -/
structure Violation where
  thm        : Name
  binderIdx  : Nat
  binderType : String
  hits       : Array Name
  deriving Inhabited

/-- For each parameter binder of `name`, scan its (reducible-closure)
const set for forbidden Names. -/
def checkTheorem (forbidden : NameSet) (name : Name)
    : Meta.MetaM (Array Violation) := do
  let env ← getEnv
  let some ci := env.find? name
    | throwError s!"unknown const: {name}"
  let typ := ci.type
  Meta.forallTelescope typ fun args _ => do
    let mut viols : Array Violation := #[]
    for h : i in [0:args.size] do
      let arg := args[i]
      let bt ← Meta.inferType arg
      let direct := gatherConsts bt {}
      let closure := reducibleClosure env direct
      let mut hits : Array Name := #[]
      for c in closure.toList do
        if forbidden.contains c then hits := hits.push c
      if !hits.isEmpty then
        let fmt ← Meta.ppExpr bt
        viols := viols.push
          { thm := name, binderIdx := i, binderType := fmt.pretty, hits := hits }
    return viols

end TrustGate.TypeWalk
