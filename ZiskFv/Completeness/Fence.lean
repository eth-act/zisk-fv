import ZiskFv.Completeness.Rv64imShapes
import ZiskFv.Compliance.Defects

/-!
# FENCE raw-shape completeness boundary

This module is the checked-in Lean counterpart of the generated Aeneas FENCE
experiment. It does not import the Aeneas-generated production decoder; instead
it records the raw-bit shape of the known FENCE decode gap used by the
`h_avoid_known_bugs` boundary.

The generated Aeneas harness checks that these shapes agree with the extracted
production ZisK decoder. This file keeps the main-tree theorem shape small and
toolchain-independent.
-/

namespace ZiskFv.Completeness.Fence

open ZiskFv.Completeness
open ZiskFv.Compliance

abbrev RawInstruction := Rv.RawInstruction

abbrev rawOpcode := Rv64imShapes.rawOpcode
abbrev rawFunct3 := Rv64imShapes.rawFunct3
abbrev rawRd := Rv64imShapes.rawRd
abbrev rawRs1 := Rv64imShapes.rawRs1
abbrev rawFm := Rv64imShapes.rawFm

/-- Sail's generic FENCE decode shape: opcode `0x0f`, `funct3 = 0`.

This intentionally includes shapes that ZisK v0.17.0 rejects. -/
def SailGenericFenceRaw (raw : RawInstruction) : Prop :=
  rawOpcode raw = 0x0f ∧ rawFunct3 raw = 0

/-- Current production-ZisK FENCE subset: generic FENCE with `fm = 0`,
`rd = x0`, and `rs1 = x0`. -/
def ZiskFenceSupportedRaw (raw : RawInstruction) : Prop :=
  SailGenericFenceRaw raw ∧ rawFm raw = 0 ∧ rawRd raw = 0 ∧ rawRs1 raw = 0

/-- Known FENCE decode gap: Sail-generic FENCE raw words outside the current
production-ZisK FENCE subset. -/
def KnownFenceDecodeGapRaw (raw : RawInstruction) : Prop :=
  SailGenericFenceRaw raw ∧ ¬ ZiskFenceSupportedRaw raw

def rawRegidx (n : Nat) : regidx :=
  regidx.Regidx (BitVec.ofNat 5 n)

def RawFenceKnownGoodShape (raw : RawInstruction) : Prop :=
  rawFm raw = 0 ∧
    Defects.IsX0Reg (rawRegidx (rawRs1 raw)) ∧
    Defects.IsX0Reg (rawRegidx (rawRd raw))

theorem isX0Reg_rawRegidx_of_eq_zero {n : Nat} (h : n = 0) :
    Defects.IsX0Reg (rawRegidx n) := by
  subst h
  simp [rawRegidx, Defects.IsX0Reg]

/-- Raw-field counterpart of `Compliance.Defects.FenceKnownGoodShape`. -/
theorem raw_fence_known_good_shape_of_supported
    {raw : RawInstruction} (h : ZiskFenceSupportedRaw raw) :
    RawFenceKnownGoodShape raw := by
  rcases h with ⟨_h_sail, h_fm, h_rd, h_rs1⟩
  exact
    ⟨h_fm,
      isX0Reg_rawRegidx_of_eq_zero h_rs1,
      isX0Reg_rawRegidx_of_eq_zero h_rd⟩

theorem supported_pred_succ_shape_supported
    {raw : RawInstruction} (h : Rv64imShapes.SupportedFencePredSuccShape raw) :
    ZiskFenceSupportedRaw raw := by
  rcases Rv64imShapes.supportedFencePredSuccShape_fields_ok h with
    ⟨h_opcode, h_funct3, h_fm, h_rd, h_rs1⟩
  exact ⟨⟨h_opcode, h_funct3⟩, h_fm, h_rd, h_rs1⟩

def fenceInterface : Rv.Interface where
  sailExecutable := SailGenericFenceRaw
  ziskDecodeSupported := ZiskFenceSupportedRaw
  ziskLowerable := ZiskFenceSupportedRaw
  ziskRowMaterialized := ZiskFenceSupportedRaw
  ziskOpcodeCovered := ZiskFenceSupportedRaw
  knownDecodeGap := KnownFenceDecodeGapRaw
  knownRowMaterializationGap := fun _ => False

theorem supported_pred_succ_shape_no_known_gap
    {raw : RawInstruction} (h : Rv64imShapes.SupportedFencePredSuccShape raw) :
    ¬ Rv.Interface.knownGap fenceInterface raw := by
  intro h_gap
  have h_supported := supported_pred_succ_shape_supported h
  have h_decode_gap : KnownFenceDecodeGapRaw raw := by
    simpa [Rv.Interface.knownGap, fenceInterface] using h_gap
  exact h_decode_gap.2 h_supported

theorem supported_pred_succ_shape_circuit_covered
    {raw : RawInstruction} (h : Rv64imShapes.SupportedFencePredSuccShape raw) :
    Rv.Interface.ziskCircuitCovered fenceInterface raw := by
  have h_supported := supported_pred_succ_shape_supported h
  simpa [Rv.Interface.ziskCircuitCovered, fenceInterface] using
    (show
      ZiskFenceSupportedRaw raw ∧ ZiskFenceSupportedRaw raw ∧
        ZiskFenceSupportedRaw raw ∧ ZiskFenceSupportedRaw raw from
      ⟨h_supported, h_supported, h_supported, h_supported⟩)

theorem supported_pred_succ_shape_circuit_covered_known_good :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      fenceInterface
      Rv64imShapes.SupportedFencePredSuccShape := by
  intro raw h_shape
  exact
    ⟨supported_pred_succ_shape_circuit_covered h_shape,
      supported_pred_succ_shape_no_known_gap h_shape⟩

theorem fence_avoid_known_bugs :
    Rv.Interface.AvoidKnownBugs fenceInterface := by
  intro raw h_sail h_not_gap
  by_cases h_supported : ZiskFenceSupportedRaw raw
  · exact h_supported
  · exact False.elim (h_not_gap (.inl ⟨h_sail, h_supported⟩))

theorem fence_lowering_complete :
    Rv.Interface.LoweringComplete fenceInterface := by
  intro raw h_supported
  exact h_supported

theorem fence_rows_complete :
    Rv.Interface.RowMaterializationComplete fenceInterface := by
  intro raw h_lowerable
  exact h_lowerable

theorem fence_opcode_coverage_complete :
    Rv.Interface.OpcodeCoverageComplete fenceInterface := by
  intro raw h_supported
  exact h_supported

theorem supported_pred_succ_shape_rows_complete :
    Rv.Interface.ShapeRowMaterializationComplete
      fenceInterface
      Rv64imShapes.SupportedFencePredSuccShape :=
  Rv.Interface.shape_row_materialization_of_circuit_covered_known_good
    fenceInterface
    Rv64imShapes.SupportedFencePredSuccShape
    supported_pred_succ_shape_circuit_covered_known_good

/-- FENCE-specific instance of the abstract RV completeness theorem, outside
the known production-ZisK FENCE decode gap. -/
theorem fence_completeness_avoiding_known_bugs :
    Rv.Interface.CompletenessAvoidingKnownBugs fenceInterface :=
  Rv.Interface.completeness_avoiding_known_bugs
    fenceInterface
    fence_avoid_known_bugs
    fence_lowering_complete
    fence_rows_complete
    fence_opcode_coverage_complete

/-- The supported FENCE pred/succ family from the broad RV64IM shape grid is
closed in the checked-in theorem surface. Generic FENCE encodings outside this
shape remain behind `KnownFenceDecodeGapRaw`. -/
theorem supported_pred_succ_shape_completeness :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      fenceInterface
      Rv64imShapes.SupportedFencePredSuccShape :=
  Rv.Interface.shape_completeness_of_circuit_covered_known_good
    fenceInterface
    Rv64imShapes.SupportedFencePredSuccShape
    supported_pred_succ_shape_circuit_covered_known_good

end ZiskFv.Completeness.Fence
