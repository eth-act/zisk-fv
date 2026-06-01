import ZiskFv.Compliance.OpEnvelope

/-!
# Known-defect predicates for the global compliance theorem

This module records the Lean side of `trust/defects.md`. A defect
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

/-- Stable identifiers for entries in `trust/defects.md`. -/
inductive DefectId where
  | arithTableTrustShape
  | arithMulSignedWitnessSoundness
  | arithDivDynamicWitnessSoundness
  | fenceIncomplete
  deriving DecidableEq, Repr

/-- Current modeled FENCE subset: Sail/ZisK-observable no-op behavior.

This predicate is intentionally `True` today. The known FENCE concern is that
ZisK may reject some encodings that Sail would execute as no-ops; that is a
completeness/coverage limitation, not a soundness counterexample. If triage
finds an accepted FENCE row whose Sail-observable behavior is not `PC += 4`,
this predicate should become the precise soundness-side exclusion. -/
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

/-- Conservative marker for remaining dynamic DIV/REM witness facts.

The retired `arith_table_op_*` and `arith_div_*` assumptions were not pure
finite-table projections: they connected row selectors to concrete operand
chunks, sign witnesses, and remainder bounds. The unsigned `DIVU`/`REMU` and
`DIVUW`/`REMUW` paths now derive these facts from row/range/operation-bus
evidence; the remaining signed arms stay excluded until their extra sign and
overflow/div-by-zero facts are proved. -/
def ArithDivDynamicWitnessShape
    : OpEnvelope state m r_main → Prop
  | .div .. => True
  | .divw .. => True
  | .rem .. => True
  | .remw .. => True
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
  | .arithDivDynamicWitnessSoundness =>
      ArithDivDynamicWitnessShape env
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

theorem no_arith_div_dynamic_witness_of_no_known_defect
    {env : OpEnvelope state m r_main}
    (h_known_bugs : NoKnownDefect env) :
    ¬ ArithDivDynamicWitnessShape env :=
  h_known_bugs .arithDivDynamicWitnessSoundness

theorem no_opcode_specific_arith_table_axiom_of_no_known_defect
    {env : OpEnvelope state m r_main}
    (h_known_bugs : NoKnownDefect env) :
    ¬ UsesOpcodeSpecificArithTableAxiom env :=
  h_known_bugs .arithTableTrustShape

end ZiskFv.Compliance.Defects
