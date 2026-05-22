import ZiskFv.Compliance.OpEnvelope

/-!
# Known-defect predicates for the global compliance theorem

This module records the Lean side of `docs/fv/defects.md`. A defect
predicate is not a trusted fact: it is a visible exclusion on a theorem
whose claim is "compliance outside known defect regions".

The predicates below are deliberately conservative while the exact bad
witness shapes are still being triaged. Retiring a defect should shrink
`Blocks`; it should not add an axiom.
-/

namespace ZiskFv.Compliance.Defects

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- Stable identifiers for entries in `docs/fv/defects.md`. -/
inductive DefectId where
  | arithTableTrustShape
  | arithMulSignedWitnessSoundness
  | fenceIncomplete
  deriving DecidableEq, Repr

/-- Current modeled FENCE subset: Sail/ZisK-observable no-op behavior.

This is a placeholder predicate for the FENCE triage. Today the FENCE proof
already reduces Sail FENCE to `PC += 4` under the Machine-mode and Sail
concurrency assumptions carried by the wrapper, so every current FENCE
envelope is in the modeled subset. If the triage finds an in-scope behavior
outside this subset, this predicate should become the precise condition. -/
def FenceNopEquivalent
    (_env : OpEnvelope state m r_main) : Prop :=
  True

/-- Conservative marker for the malicious signed-MUL witness shape.

Until the raw witness predicate is pinned down, the signed multiply arms
whose correctness depended on the false static product-sign shortcut are
blocked by this defect. This is a claim-weakening exclusion, not a trusted
fact: retiring it requires a dynamic carry/range proof or an upstream circuit
fix. -/
def MaliciousSignedMulWitnessShape
    : OpEnvelope state m r_main → Prop
  | .mul .. => True
  | .mulh .. => True
  | .mulhsu .. => True
  | _ => False

/-- Conservative marker for remaining opcode-shaped ArithTable trust.

This starts broad across the ArithMul/ArithDiv opcode families because the
current defect is about the proof/trust shape, not a single program input.
As C3/C4 retire the bad `arith_table_op_*` assumptions, these arms should
be narrowed and then deleted. -/
def UsesOpcodeSpecificArithTableAxiom
    : OpEnvelope state m r_main → Prop
  | _ => False

/-- `Blocks id env` means defect `id` excludes this envelope from the
    defect-qualified compliance theorem. -/
def Blocks (id : DefectId) (env : OpEnvelope state m r_main) : Prop :=
  match id with
  | .arithTableTrustShape =>
      UsesOpcodeSpecificArithTableAxiom env
  | .arithMulSignedWitnessSoundness =>
      MaliciousSignedMulWitnessShape env
  | .fenceIncomplete =>
      ¬ FenceNopEquivalent env

/-- Public theorem-side hypothesis: this envelope is outside every known
    defect region. -/
def NoKnownDefect (env : OpEnvelope state m r_main) : Prop :=
  ∀ id, ¬ Blocks id env

theorem fence_nop_equivalent_of_no_known_defect
    {env : OpEnvelope state m r_main}
    (h_known_bugs : NoKnownDefect env) :
    FenceNopEquivalent env := by
  by_contra h_not
  exact h_known_bugs .fenceIncomplete h_not

theorem no_malicious_signed_mul_witness_of_no_known_defect
    {env : OpEnvelope state m r_main}
    (h_known_bugs : NoKnownDefect env) :
    ¬ MaliciousSignedMulWitnessShape env :=
  h_known_bugs .arithMulSignedWitnessSoundness

theorem no_opcode_specific_arith_table_axiom_of_no_known_defect
    {env : OpEnvelope state m r_main}
    (h_known_bugs : NoKnownDefect env) :
    ¬ UsesOpcodeSpecificArithTableAxiom env :=
  h_known_bugs .arithTableTrustShape

end ZiskFv.Compliance.Defects
