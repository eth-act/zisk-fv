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

/-- Collapse pretty-printer whitespace so generated baselines keep one row per
binder even when the type is too wide for the default formatter. -/
def normalizeWhitespace (s : String) : String :=
  String.intercalate " " (s.splitToList (·.isWhitespace) |>.filter (!·.isEmpty))

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

/-- Rendered information for one theorem binder. This is an audit surface only:
it records the elaborated binder name and type without applying any policy. -/
structure BinderInfo where
  thm        : Name
  binderIdx  : Nat
  binderName : Name
  binderType : String
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

/-- Render the parameter binders of `name` in elaborated order. -/
def renderTheoremBinders (name : Name) : Meta.MetaM (Array BinderInfo) := do
  let some ci := (← getEnv).find? name
    | throwError s!"unknown const: {name}"
  let typ := ci.type
  Meta.forallTelescope typ fun args _ => do
    let mut rows : Array BinderInfo := #[]
    for h : i in [0:args.size] do
      let arg := args[i]
      let localDecl ← arg.fvarId!.getDecl
      let bt ← Meta.inferType arg
      let fmt ← Meta.ppExpr bt
      rows := rows.push
        { thm := name
          binderIdx := i
          binderName := localDecl.userName
          binderType := fmt.pretty }
    return rows

/-- One leaf line of the DEEP (recursive) construction-binder render.

`path` is a dotted accessor path from a top-level binder down to a leaf field
(e.g. `binding.mainTable`); `fieldType` is the normalized pretty-printed leaf
type. The numeric binder index is deliberately DROPPED — paths are the stable
key, so a re-ordering refactor does not churn the baseline. -/
structure DeepBinderInfo where
  path      : String
  fieldType : String
  deriving Inhabited

/-- True iff the recursive deep walk should DESCEND into structure `head`.

Only `ZiskFv.*` project structures are descended. Library structures
(`Fin`, `And`, `Exists`, `Prod`, `Subtype`, `BitVec`, `EStateM.Result`, `Eq`,
…) are treated as LEAVES — this stop-set is critical: naive recursion into
library structures explodes into anonymous-projection (`s✝.1`) noise. -/
def shouldRecurse (head : Name) : Bool :=
  head.getRoot == `ZiskFv

/-- Recursively render the leaf fields reachable from a single binder.

`path` is the accessor path so far; `parent` is the elaborated `Expr` for the
value at `path`; `parentTy` is its (already-inferred) type; `visited` guards
against cyclic structure references. We descend into a structure `head` iff
`parentTy` is not itself a forall AND `head` is a project structure
(`shouldRecurse`). Function-valued fields are leaves (descending into them would
require telescoping, and they are honest "is a function" facts, not smuggled
data). Each non-descended node emits exactly one leaf line. -/
partial def renderDeep (name : Name) (path : String)
    (parent parentTy : Expr) (visited : NameSet) :
    Meta.MetaM (Array DeepBinderInfo) := do
  let (head, _) := parentTy.getAppFnArgs
  let env ← getEnv
  -- Descend only into ZiskFv.* project structures whose type is not a forall.
  if parentTy.isForall || !(Lean.isStructure env head) || !(shouldRecurse head) then
    let fmt ← Meta.ppExpr parentTy
    return #[{ path := path, fieldType := normalizeWhitespace fmt.pretty }]
  if visited.contains head then
    return #[{ path := path, fieldType := s!"<CYCLE {head}>" }]
  let visited := visited.insert head
  let fields := Lean.getStructureFields env head
  let mut rows : Array DeepBinderInfo := #[]
  for h : idx in [0:fields.size] do
    let fieldName := fields[idx]
    let proj := Expr.proj head idx parent
    let fieldTy ← Meta.inferType proj
    if fieldTy.isForall then
      -- Function-valued field: leaf (do not telescope).
      let fmt ← Meta.ppExpr fieldTy
      rows := rows.push
        { path := s!"{path}.{fieldName}"
          fieldType := normalizeWhitespace fmt.pretty }
    else
      let sub ← renderDeep name s!"{path}.{fieldName}" proj fieldTy visited
      rows := rows ++ sub
  return rows

/-- Deep (recursive) render of `name`'s parameter binders. Top-level binders
are telescoped; each is then recursively descended via `renderDeep`, emitting
one leaf line per reachable non-descended field. The output is the audit
surface for the P4 construction theorem: because the sound construction carries
NO `*RowBinding` / `MainRowProvenance` deep record, the deep baseline is just
the flat list of its honest top-level binders — and any future attempt to
smuggle a fact inside a project structure surfaces as new dotted leaf lines. -/
def renderTheoremBindersDeep (name : Name)
    : Meta.MetaM (Array DeepBinderInfo) := do
  let some ci := (← getEnv).find? name
    | throwError s!"unknown const: {name}"
  let typ := ci.type
  Meta.forallTelescope typ fun args _ => do
    let mut rows : Array DeepBinderInfo := #[]
    for arg in args do
      let localDecl ← arg.fvarId!.getDecl
      let bt ← Meta.inferType arg
      let sub ← renderDeep name (toString localDecl.userName) arg bt {}
      rows := rows ++ sub
    return rows

end TrustGate.TypeWalk
