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

end TrustGate.ConstantClosure
