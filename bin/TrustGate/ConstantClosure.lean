/-
TrustGate.ConstantClosure — full constant-graph reachability under
the elaborated environment.

Where `AxiomClosure` filters `Lean.collectAxioms`'s output down to
`ZiskFv.*` axioms, this module exposes the *unfiltered* transitive
reachability: starting from a seed set of Names, walk every
referenced constant (types + values, including projections,
helper lemmas, defs) and return the set of all reachable
`ConstantInfo` Names.

Used by the dead-code audit subcommands (`print-reachable`,
`find-unused`). The audit is conservative: a constant is reported
as "unreachable" iff no entry-point closure mentions it
syntactically. False positives occur for:
  * type-class instances reached only via implicit-argument
    elaboration (the resolver inserts the instance const at
    elaboration time, so the *uses* of the instance do reference
    it — but instances declared but never used at synthesis sites
    look unreachable);
  * tactic-only definitions surfaced via `by` macro expansion that
    no const refers to syntactically;
  * `@[simp]`, `@[ext]`, etc. lemmas referenced only by tactic
    discharge (rare in this codebase, since opcode proofs use
    explicit term-mode dispatch).

Both classes are flagged for human review; we do not filter them
automatically.
-/
import Lean

open Lean

namespace TrustGate.ConstantClosure

/-- Collect every Name appearing as `Expr.const` in `e`. -/
partial def gatherConsts (e : Expr) (acc : NameSet) : NameSet :=
  match e with
  | .const n _       => acc.insert n
  | .app f a         => gatherConsts a (gatherConsts f acc)
  | .lam _ t b _     => gatherConsts b (gatherConsts t acc)
  | .forallE _ t b _ => gatherConsts b (gatherConsts t acc)
  | .letE _ t v b _  => gatherConsts b (gatherConsts v (gatherConsts t acc))
  | .mdata _ b       => gatherConsts b acc
  | .proj _ _ b      => gatherConsts b acc
  | _                => acc

/-- All constants referenced syntactically by `ci`'s type and (when
present) value. -/
def referencedByCI (ci : ConstantInfo) : NameSet :=
  let acc := gatherConsts ci.type {}
  match ci.value? with
  | some v => gatherConsts v acc
  | none   => acc

/-- BFS from `seeds`: union the syntactic-const closure under the
environment. Stops at constants without a definition (axioms, opaques)
after recording their type's references. -/
partial def transitiveClosure (env : Environment) (seeds : List Name) : NameSet :=
  go (seeds.foldl (·.insert ·) ({} : NameSet)) seeds
where
  go (acc : NameSet) (todo : List Name) : NameSet :=
    match todo with
    | [] => acc
    | n :: rest =>
      match env.find? n with
      | none => go acc rest
      | some ci =>
        let refs := referencedByCI ci
        let newOnes := refs.toList.filter (!acc.contains ·)
        let acc' := newOnes.foldl (·.insert ·) acc
        go acc' (newOnes ++ rest)

/-- True iff `n` is project-namespaced (`ZiskFv.*`). -/
def isProjectName (n : Name) : Bool :=
  n.getRoot == `ZiskFv

/-- Enumerate every `ZiskFv.*` const in the environment, excluding
internal compiler-generated names that begin with `_` after the
final dot (e.g. `_aux`, `_proof_`, `_eq_`) — these are emitted by
the elaborator for equation compilation, recursors, etc. and are
not user-authored. We keep them out of the audit set since they
trivially track their parent definition. -/
def isCompilerInternal (n : Name) : Bool :=
  -- Drop names containing `_proof_`, `_eq_`, `match_`, `proof_`,
  -- `_unsafe_rec`, `.rec`, `.recOn`, etc. anywhere in the chain.
  let s := n.toString
  s.splitOn "." |>.any fun part =>
    part.startsWith "_" ||
    part == "rec" || part == "recOn" || part == "casesOn" ||
    part == "noConfusion" || part == "noConfusionType" ||
    part == "mk" ||  -- structure constructors are auto-built; their parent type covers them
    part == "below" || part == "brecOn" ||
    part == "ind" || part == "indOn" ||
    part == "binductionOn" || part == "ndrec" || part == "ndrecOn"

/-- True iff `n` looks like a user-authored project Name (subject to
the audit). -/
def isAuditable (n : Name) : Bool :=
  isProjectName n && !isCompilerInternal n

/-- Enumerate all auditable `ZiskFv.*` constants in `env`. -/
def allAuditableProjectConsts (env : Environment) : Array Name :=
  let acc :=
    env.constants.fold (init := (#[] : Array Name)) fun out n _ci =>
      if isAuditable n then out.push n else out
  acc.qsort (fun a b => a.toString < b.toString)

/-- Try to recover the source-module Name for `n`. Returns the
module Name (e.g. `ZiskFv.Airs.Arith.Ranges`) if known, else "?". -/
def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some m => m.toString
    | none   => "?"
  | none => "<current>"

/-- A node-kind tag for the proof-tree visualizer. -/
inductive NodeKind
  | project    -- a ZiskFv.* const (theorem, def, etc.)
  | axiom_     -- a ZiskFv.* axiom (trust-ledger leaf)
  | external   -- non-ZiskFv const (mathlib / Sail / Lean core)
  deriving Repr, BEq

/-- Tag a Name with its NodeKind. -/
def nodeKindOf (env : Environment) (n : Name) : NodeKind :=
  if isProjectName n then
    match env.find? n with
    | some (.axiomInfo _) => NodeKind.axiom_
    | _                   => NodeKind.project
  else
    NodeKind.external

/-- True iff `n` is a Lean-internal Name we want to drop entirely
from the proof tree (kernel `Eq.refl`, congr lemmas, propext, etc.
appear thousands of times and add no signal). -/
def isNoiseExternal (n : Name) : Bool :=
  let s := n.toString
  n == `Eq || n == `Eq.refl || n == `Eq.mpr || n == `Eq.mp ||
  n == `HEq || n == `HEq.refl ||
  n == `propext || n == `funext || n == `congrArg || n == `congr ||
  n == `congrFun || n == `congrFun₂ || n == `congrFun₃ ||
  n == `id || n == `id.def ||
  n == `True || n == `True.intro || n == `False || n == `False.elim ||
  n == `And || n == `And.intro || n == `Or ||
  n == `Iff || n == `Iff.intro || n == `Iff.mp || n == `Iff.mpr ||
  n == `Not || n == `decide ||
  s.startsWith "Eq." || s.startsWith "HEq." ||
  s.startsWith "Nat.rec" || s.startsWith "Bool.rec"

/-- Render a NodeKind as a short string tag. -/
def NodeKind.toTag : NodeKind → String
  | .project  => "P"
  | .axiom_   => "A"
  | .external => "E"

/-- BFS edge collection from `root`. Yields a sorted array of
`(parent, child, parentKind, childKind)` quadruples for the proof-
tree visualizer.

Edge policy: we only emit edges whose CHILD is project-namespaced
(project const or project axiom). External refs (mathlib, Sail,
Lean core) would be tens of thousands of dangling leaves with no
information for the user, so they are dropped at the edge stage.
Project constants that reference no project children still appear
implicitly as terminal nodes (they show up as the child of some
parent's edge). The root is guaranteed to be present.

We never recurse into external constants. -/
def collectEdges (env : Environment) (root : Name) :
    Array (Name × Name × NodeKind × NodeKind) := Id.run do
  let mut visited : NameSet := NameSet.empty.insert root
  let mut todo : Array Name := #[root]
  let mut edges : Array (Name × Name × NodeKind × NodeKind) := #[]
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    let pKind := nodeKindOf env n
    -- Only recurse into project consts. External consts are leaves.
    if pKind matches .external then continue
    match env.find? n with
    | none => continue
    | some ci =>
      let refs := referencedByCI ci
      for c in refs.toList do
        if c == n then continue
        if isCompilerInternal c then continue
        if isNoiseExternal c then continue
        let cKind := nodeKindOf env c
        -- Drop external children entirely — they are pure noise for
        -- the visualizer.
        if cKind matches .external then
          if !visited.contains c then
            visited := visited.insert c
          continue
        edges := edges.push (n, c, pKind, cKind)
        if !visited.contains c then
          visited := visited.insert c
          todo := todo.push c
  -- Sort edges deterministically.
  edges.qsort (fun a b =>
    if a.1.toString == b.1.toString then a.2.1.toString < b.2.1.toString
    else a.1.toString < b.1.toString)

end TrustGate.ConstantClosure
