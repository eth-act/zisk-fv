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

/-- Collect every Name appearing as `Expr.const` in `e`.

PERF: a Lean `Expr` is a DAG with heavy structural SHARING (after
`ring`/`simp`/`omega` a single proof term can have thousands of shared
sub-terms). A naive tree recursion re-walks every shared sub-term once
per incoming edge — exponential on real proof values, which is the
root cause of the multi-minute dead-code scan. We memoize the set of
ALREADY-VISITED sub-`Expr`s in a `Std.HashSet Expr` (keyed on Lean's
cached structural hash + `BEq`), so each distinct node is walked once.
This is purely an efficiency change: the set of const Names found is
identical to the naive walk. -/
partial def gatherConstsAux (e : Expr) (acc : NameSet) (seen : Std.HashSet Expr)
    : NameSet × Std.HashSet Expr :=
  -- Atoms with no sub-`Expr`s are not worth memoizing (no sharing payoff).
  match e with
  | .const n _       => (acc.insert n, seen)
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => (acc, seen)
  | _ =>
    if seen.contains e then (acc, seen)
    else
      let seen := seen.insert e
      match e with
      | .app f a         =>
        let (acc, seen) := gatherConstsAux f acc seen
        gatherConstsAux a acc seen
      | .lam _ t b _     =>
        let (acc, seen) := gatherConstsAux t acc seen
        gatherConstsAux b acc seen
      | .forallE _ t b _ =>
        let (acc, seen) := gatherConstsAux t acc seen
        gatherConstsAux b acc seen
      | .letE _ t v b _  =>
        let (acc, seen) := gatherConstsAux t acc seen
        let (acc, seen) := gatherConstsAux v acc seen
        gatherConstsAux b acc seen
      | .mdata _ b       => gatherConstsAux b acc seen
      | .proj _ _ b      => gatherConstsAux b acc seen
      | _                => (acc, seen)

/-- Collect every Name appearing as `Expr.const` in `e` (memoized over
shared sub-terms — see `gatherConstsAux`). -/
def gatherConsts (e : Expr) (acc : NameSet) : NameSet :=
  (gatherConstsAux e acc {}).1

/-- All constants referenced syntactically by `ci`'s type and (when
present) value. -/
def referencedByCI (ci : ConstantInfo) : NameSet :=
  let acc := gatherConsts ci.type {}
  match ci.value? with
  | some v => gatherConsts v acc
  | none   => acc

/-- Strip a leading Lean `private` mangling prefix, if present, returning the
forward-ordered components of the *user-visible* name.

Lean encodes a private declaration as
`_private.<Module.Path>.<num>.<RealName...>` — a `str "_private"` root, then
the source module's path components, then a numeric component (`Name.num`),
then the actual user-authored name (e.g. `ZiskFv.Compliance.foo`). A naive
`n.getRoot == `ZiskFv` therefore MISSES every private decl (its root is
`_private`). This helper drops everything up to and including the first numeric
component so the remainder can be root-checked like a public name. For a
non-private name it returns the components unchanged. -/
def strippedComponents (n : Name) : List Name :=
  let fwd := n.componentsRev.reverse
  if n.getRoot == `_private then
    -- Drop through the first numeric (`Name.num`) component; what follows is
    -- the user-visible name.
    let rec drop : List Name → List Name
      | [] => []
      | c :: rest =>
        match c with
        | .num _ _ => rest
        | _        => drop rest
    drop fwd
  else
    fwd

/-- The user-visible root of `n` (after stripping any `private` mangling). -/
def visibleRoot (n : Name) : Name :=
  match strippedComponents n with
  | (h :: _) => h
  | []       => n.getRoot

/-- True iff `n` is project-namespaced (`ZiskFv.*`), looking THROUGH any
`private` mangling so private project decls are not invisible to the audit. -/
def isProjectName (n : Name) : Bool :=
  visibleRoot n == `ZiskFv

/-- BFS from `seeds`: union the syntactic-const closure under the
environment. Stops at constants without a definition (axioms, opaques)
after recording their type's references.

PERF (audit-only optimization, result-preserving for the `ZiskFv.*`
reachable set): we do NOT expand the body/type of a NON-project
constant. A mathlib / Lean-core / Sail const cannot reference any
`ZiskFv.*` const (the project depends on those libraries, not the
reverse — there is no dependency edge from an external const back into
the project namespace). So pruning external expansion removes the
dominant cost (walking the giant Sail/mathlib proof terms) without
dropping a single reachable `ZiskFv.*` name. External names are still
recorded in `acc` (so callers that inspect non-project reachability
keep seeing them as reached leaves); they are simply not re-expanded. -/
partial def transitiveClosure (env : Environment) (seeds : List Name) : NameSet :=
  go (seeds.foldl (·.insert ·) ({} : NameSet)) seeds
where
  go (acc : NameSet) (todo : List Name) : NameSet :=
    match todo with
    | [] => acc
    | n :: rest =>
      -- Do not expand external constants: their closure adds no `ZiskFv.*`
      -- names and is the source of the multi-minute blowup. We look THROUGH
      -- any `private` mangling so private project deps are still followed.
      if !isProjectName n then go acc rest
      else
      match env.find? n with
      | none => go acc rest
      | some ci =>
        let refs := referencedByCI ci
        let newOnes := refs.toList.filter (!acc.contains ·)
        let acc' := newOnes.foldl (·.insert ·) acc
        go acc' (newOnes ++ rest)

/-- Enumerate every `ZiskFv.*` const in the environment, excluding
internal compiler-generated names that begin with `_` after the
final dot (e.g. `_aux`, `_proof_`, `_eq_`) — these are emitted by
the elaborator for equation compilation, recursors, etc. and are
not user-authored. We keep them out of the audit set since they
trivially track their parent definition. -/
def isCompilerInternal (n : Name) : Bool :=
  -- Drop names containing `_proof_`, `_eq_`, `match_`, `proof_`,
  -- `_unsafe_rec`, `.rec`, `.recOn`, etc. anywhere in the chain.
  --
  -- We classify the USER-VISIBLE name (after stripping any `private`
  -- mangling). Otherwise the `_private` literal and the source-module-path
  -- prefix would make EVERY private decl look compiler-internal and so be
  -- silently dropped from the audit set.
  (strippedComponents n).any fun part =>
    let p := part.toString
    p.startsWith "_" ||
    p == "rec" || p == "recOn" || p == "casesOn" ||
    p == "noConfusion" || p == "noConfusionType" ||
    p == "mk" ||  -- structure constructors are auto-built; their parent type covers them
    p == "below" || p == "brecOn" ||
    p == "ind" || p == "indOn" ||
    p == "binductionOn" || p == "ndrec" || p == "ndrecOn"

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
