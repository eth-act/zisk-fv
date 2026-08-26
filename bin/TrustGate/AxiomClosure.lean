/-
TrustGate.AxiomClosure — per-theorem transitive axiom closure via
`Lean.collectAxioms`.

We keep only `ZiskFv.*`-prefixed Names. This is the project trust
surface tracked by `trust/generated/baseline-axioms.txt`.
Everything else is external:

  * Lean kernel postulates (`propext`, `Classical.choice`, `Quot.sound`,
    `Lean.ofReduceBool`, `Lean.trustCompiler`) — unconditional kernel
    trust.
  * The LeanRV64D Sail-translation axioms (`riscv_f64Sqrt`,
    `cancel_reservation`, `plat_term_write`, …) — external to the
    project trust ledger documented in `trust/trusted-base.md`.

Both are documented as external trust scopes; the V2 baseline tracks
only the project-internal axioms whose membership review actually
controls.

`sorryAx` would also be filtered by this rule (it is not
`ZiskFv.`-prefixed), but the V1 no-sorry gate covers source-level
`sorry` and `lake build` rejects an unresolved `sorry` so any
`sorryAx`-via-metaprogramming dodge would already fail elsewhere.
-/
import Lean

open Lean

namespace TrustGate.AxiomClosure

/-- True iff `n` is a project-trust axiom (root component is `ZiskFv`). -/
def isProjectAxiom (n : Name) : Bool :=
  n.getRoot == `ZiskFv

/-- Compute the transitive project axiom closure of `name`, sorted. -/
def axiomDepsForTheorem (env : Environment) (name : Name) : Array Name :=
  let st := ((Lean.CollectAxioms.collect name).run env).run {} |>.snd
  let filtered := st.axioms.filter isProjectAxiom
  filtered.qsort (fun a b => a.toString < b.toString)

/-- Compute the FULL, UNFILTERED transitive axiom closure of `name`, sorted —
every axiom `Lean.collectAxioms` reaches, including external ones (`sorryAx`,
`Lean.ofReduceBool`, `Lean.trustCompiler`, the LeanRV64D Sail-translation
axioms) AND the `ZiskFv.*` project axioms.

Unlike `axiomDepsForTheorem`, this applies NO filter. It backs the
extraction-pin closure gate (`check-extraction-closure`), whose whole point is
to catch a leaked external `sorryAx` / `ofReduceBool` from the imported Aeneas
runtime — exactly the axioms `axiomDepsForTheorem` deliberately drops. -/
def rawAxiomDepsForTheorem (env : Environment) (name : Name) : Array Name :=
  let st := ((Lean.CollectAxioms.collect name).run env).run {} |>.snd
  st.axioms.qsort (fun a b => a.toString < b.toString)

/-- The RAW, UNFILTERED axiom closure of `roots` taken all at once.

`Lean.CollectAxioms.State` carries the `visited` set, so threading one state
through every root walks the shared constant graph a single time instead of
once per root. That is what makes a union over thousands of project
declarations affordable. -/
def rawAxiomUnion (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let mut st : Lean.CollectAxioms.State := {}
  for r in roots do
    st := ((Lean.CollectAxioms.collect r).run env).run st |>.snd
  return st.axioms.qsort (fun a b => a.toString < b.toString)

/-- Lean's own postulates, plus the two the compiled-certificate tactics
(`native_decide`, `bv_decide`) add. Trusted unconditionally, so they are
reported apart from the axioms membership review actually controls. -/
def kernelAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound, `Lean.ofReduceBool,
    `Lean.trustCompiler, `sorryAx]

/-- Which trust scope `n` belongs to: `project` (`ZiskFv.*`, the ledger in
`trust/trusted-base.md`), `kernel` (see `kernelAxioms`), or `spec` (everything
else, i.e. the LeanRV64D Sail-translation primitives and the Aeneas runtime). -/
def scopeOf (n : Name) : String :=
  if isProjectAxiom n then "project"
  else if kernelAxioms.contains n then "kernel"
  else "spec"

end TrustGate.AxiomClosure
