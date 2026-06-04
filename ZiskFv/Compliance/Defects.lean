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
  | arithMulSignedWitnessSoundness
  | arithDivDynamicWitnessSoundness
  | fenceIncomplete
  deriving DecidableEq, Repr

/-- Register-zero shape used by ZisK's currently accepted FENCE subset. -/
def IsX0Reg : regidx → Prop
  | regidx.Regidx r => r = 0#5

/-- Current modeled FENCE subset accepted by ZisK's production decoder.

The extracted decoder rejects generic FENCE encodings with a nonzero `fm`,
`rs1`, or `rd` field. The known-bug gate therefore keeps only the known-good
FENCE shape in the global theorem surface while completeness is being
triaged. Non-FENCE envelopes are unaffected by this predicate. -/
def FenceKnownGoodShape
    : OpEnvelope state m r_main → Prop
  | .fence _ fm _ _ rs rd _ _ _ =>
      fm = 0#4 ∧ IsX0Reg rs ∧ IsX0Reg rd
  | _ => True

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

/-- `Blocks id env` means defect `id` excludes this envelope from the
    defect-qualified compliance theorem. -/
def Blocks (id : DefectId) (env : OpEnvelope state m r_main) : Prop :=
  match id with
  | .arithMulSignedWitnessSoundness =>
      MaliciousSignedMulWitnessShape env
  | .arithDivDynamicWitnessSoundness =>
      ArithDivDynamicWitnessShape env
  | .fenceIncomplete =>
      ¬ FenceKnownGoodShape env

/-- Public theorem-side hypothesis: this envelope is outside every known
    defect region. -/
def NoKnownDefect (env : OpEnvelope state m r_main) : Prop :=
  ∀ id, ¬ Blocks id env

theorem fence_known_good_shape_of_no_known_defect
    {env : OpEnvelope state m r_main}
    (h_known_bugs : NoKnownDefect env) :
    FenceKnownGoodShape env := by
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

end ZiskFv.Compliance.Defects
