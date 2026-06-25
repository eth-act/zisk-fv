import ZiskFv.Completeness.Aspirational.MemoryRefinedAndImmediateEdges

/- ⚠ ASPIRATIONAL / QUARANTINED — not wired to any live completeness endpoint.
   Abstract `Rv.Interface`-parametrized route; no concrete `Interface` is ever
   built, and the live endpoints in `ZiskFv.Completeness`
   (`sail_executable_within_supported_decode_shape`, `root_completeness`)
   do not depend on it. Intended *eventual* composition machinery for when the
   Aeneas-extracted ZisK coverage proofs can be imported into this build. Kept
   compiling via `ZiskFv.lean` for preservation only.
   See `ZiskFv/Completeness/Aspirational/README.md`. -/

/-!
# RV64IM completeness — supported-decode of refined and memory-refined families

Theorem cluster split verbatim out of `ZiskFv/Completeness/Rv64im.lean`.
-/

namespace ZiskFv.Completeness.Rv64im

open ZiskFv.Completeness

theorem supported_decode_shape_avoid_of_refined_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_load :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
    (h_shift :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_store :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.StoreRegisterImmediateShape)
    (h_branch :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.SupportedDecodeShape :=
  supported_decode_shape_avoid_of_families
    iface
    h_r
    (i_type_register_immediate_shape_avoid_of_refined_families
      iface h_jalr h_alu h_load)
    h_shift
    h_store
    h_branch
    (upper_and_jump_immediate_shape_avoid_of_refined_families
      iface h_upper h_jump)
    h_fence

theorem supported_decode_shape_rows_of_refined_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_load :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
    (h_shift :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_store :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterImmediateShape)
    (h_branch :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.SupportedDecodeShape :=
  supported_decode_shape_rows_of_families
    iface
    h_r
    (i_type_register_immediate_shape_rows_of_refined_families
      iface h_jalr h_alu h_load)
    h_shift
    h_store
    h_branch
    (upper_and_jump_immediate_shape_rows_of_refined_families
      iface h_upper h_jump)
    h_fence

theorem supported_decode_shape_completeness_of_refined_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_r_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_load_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
    (h_shift_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_store_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.StoreRegisterImmediateShape)
    (h_branch_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_r_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_load_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
    (h_shift_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_store_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterImmediateShape)
    (h_branch_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    SupportedDecodeCompletenessAvoidingKnownBugs iface :=
  supported_decode_shape_completeness_of_shape_avoid_and_rows
    iface
    (supported_decode_shape_avoid_of_refined_families
      iface
      h_r_avoid
      h_jalr_avoid
      h_alu_avoid
      h_load_avoid
      h_shift_avoid
      h_store_avoid
      h_branch_avoid
      h_upper_avoid
      h_jump_avoid
      h_fence_avoid)
    h_lower
    (supported_decode_shape_rows_of_refined_families
      iface
      h_r_rows
      h_jalr_rows
      h_alu_rows
      h_load_rows
      h_shift_rows
      h_store_rows
      h_branch_rows
      h_upper_rows
      h_jump_rows
      h_fence_rows)
    h_opcode

theorem memory_refined_supported_decode_shape_avoid_of_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_shift :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.MemoryRefinedSupportedDecodeShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with
    h_r_shape | h_jalr_shape | h_alu_shape | h_memory_shape |
    h_shift_shape | h_branch_shape | h_upper_shape | h_jump_shape |
    h_fence_shape
  · exact h_r raw h_r_shape h_sail h_not_gap
  · exact h_jalr raw h_jalr_shape h_sail h_not_gap
  · exact h_alu raw h_alu_shape h_sail h_not_gap
  · exact h_memory raw h_memory_shape h_sail h_not_gap
  · exact h_shift raw h_shift_shape h_sail h_not_gap
  · exact h_branch raw h_branch_shape h_sail h_not_gap
  · exact h_upper raw h_upper_shape h_sail h_not_gap
  · exact h_jump raw h_jump_shape h_sail h_not_gap
  · exact h_fence raw h_fence_shape h_sail h_not_gap

theorem memory_refined_supported_decode_shape_no_known_gap_of_families
    (iface : Rv.Interface)
    (h_r : RTypeRegisterNoKnownGap iface)
    (h_jalr : JalrRegisterImmediateNoKnownGap iface)
    (h_alu : ImmediateAluRegisterNoKnownGap iface)
    (h_memory : MemoryRegisterImmediateNoKnownGap iface)
    (h_shift : ShiftRegisterNoKnownGap iface)
    (h_branch : BranchRegisterImmediateNoKnownGap iface)
    (h_upper : UpperRegisterImmediateNoKnownGap iface)
    (h_jump : JumpRegisterImmediateNoKnownGap iface)
    (h_fence : SupportedFencePredSuccNoKnownGap iface) :
    MemoryRefinedSupportedDecodeNoKnownGap iface := by
  intro raw h_shape
  rcases h_shape with
    h_r_shape | h_jalr_shape | h_alu_shape | h_memory_shape |
    h_shift_shape | h_branch_shape | h_upper_shape | h_jump_shape |
    h_fence_shape
  · exact h_r raw h_r_shape
  · exact h_jalr raw h_jalr_shape
  · exact h_alu raw h_alu_shape
  · exact h_memory raw h_memory_shape
  · exact h_shift raw h_shift_shape
  · exact h_branch raw h_branch_shape
  · exact h_upper raw h_upper_shape
  · exact h_jump raw h_jump_shape
  · exact h_fence raw h_fence_shape

theorem memory_refined_supported_decode_shape_sail_executable_of_families
    (iface : Rv.Interface)
    (h_r : RTypeRegisterSailExecutable iface)
    (h_jalr : JalrRegisterImmediateSailExecutable iface)
    (h_alu : ImmediateAluRegisterSailExecutable iface)
    (h_memory : MemoryRegisterImmediateSailExecutable iface)
    (h_shift : ShiftRegisterSailExecutable iface)
    (h_branch : BranchRegisterImmediateSailExecutable iface)
    (h_upper : UpperRegisterImmediateSailExecutable iface)
    (h_jump : JumpRegisterImmediateSailExecutable iface)
    (h_fence : SupportedFencePredSuccSailExecutable iface) :
    Rv.Interface.ShapeSailExecutable
      iface
      Rv64imShapes.MemoryRefinedSupportedDecodeShape := by
  intro raw h_shape
  rcases h_shape with
    h_r_shape | h_jalr_shape | h_alu_shape | h_memory_shape |
    h_shift_shape | h_branch_shape | h_upper_shape | h_jump_shape |
    h_fence_shape
  · exact h_r raw h_r_shape
  · exact h_jalr raw h_jalr_shape
  · exact h_alu raw h_alu_shape
  · exact h_memory raw h_memory_shape
  · exact h_shift raw h_shift_shape
  · exact h_branch raw h_branch_shape
  · exact h_upper raw h_upper_shape
  · exact h_jump raw h_jump_shape
  · exact h_fence raw h_fence_shape

theorem memory_refined_supported_decode_shape_rows_of_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_shift :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.MemoryRefinedSupportedDecodeShape := by
  intro raw h_shape h_lowerable
  rcases h_shape with
    h_r_shape | h_jalr_shape | h_alu_shape | h_memory_shape |
    h_shift_shape | h_branch_shape | h_upper_shape | h_jump_shape |
    h_fence_shape
  · exact h_r raw h_r_shape h_lowerable
  · exact h_jalr raw h_jalr_shape h_lowerable
  · exact h_alu raw h_alu_shape h_lowerable
  · exact h_memory raw h_memory_shape h_lowerable
  · exact h_shift raw h_shift_shape h_lowerable
  · exact h_branch raw h_branch_shape h_lowerable
  · exact h_upper raw h_upper_shape h_lowerable
  · exact h_jump raw h_jump_shape h_lowerable
  · exact h_fence raw h_fence_shape h_lowerable

theorem memory_refined_supported_decode_shape_circuit_covered_known_good_of_family_avoid_no_gap_sail_and_rows
    (iface : Rv.Interface)
    (h_r_no_gap : RTypeRegisterNoKnownGap iface)
    (h_jalr_no_gap : JalrRegisterImmediateNoKnownGap iface)
    (h_alu_no_gap : ImmediateAluRegisterNoKnownGap iface)
    (h_memory_no_gap : MemoryRegisterImmediateNoKnownGap iface)
    (h_shift_no_gap : ShiftRegisterNoKnownGap iface)
    (h_branch_no_gap : BranchRegisterImmediateNoKnownGap iface)
    (h_upper_no_gap : UpperRegisterImmediateNoKnownGap iface)
    (h_jump_no_gap : JumpRegisterImmediateNoKnownGap iface)
    (h_fence_no_gap : SupportedFencePredSuccNoKnownGap iface)
    (h_r_sail : RTypeRegisterSailExecutable iface)
    (h_jalr_sail : JalrRegisterImmediateSailExecutable iface)
    (h_alu_sail : ImmediateAluRegisterSailExecutable iface)
    (h_memory_sail : MemoryRegisterImmediateSailExecutable iface)
    (h_shift_sail : ShiftRegisterSailExecutable iface)
    (h_branch_sail : BranchRegisterImmediateSailExecutable iface)
    (h_upper_sail : UpperRegisterImmediateSailExecutable iface)
    (h_jump_sail : JumpRegisterImmediateSailExecutable iface)
    (h_fence_sail : SupportedFencePredSuccSailExecutable iface)
    (h_r_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_shift_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_r_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_shift_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    MemoryRefinedSupportedDecodeCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_of_shape_avoid_and_rows
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape
    (memory_refined_supported_decode_shape_no_known_gap_of_families
      iface
      h_r_no_gap
      h_jalr_no_gap
      h_alu_no_gap
      h_memory_no_gap
      h_shift_no_gap
      h_branch_no_gap
      h_upper_no_gap
      h_jump_no_gap
      h_fence_no_gap)
    (memory_refined_supported_decode_shape_sail_executable_of_families
      iface
      h_r_sail
      h_jalr_sail
      h_alu_sail
      h_memory_sail
      h_shift_sail
      h_branch_sail
      h_upper_sail
      h_jump_sail
      h_fence_sail)
    (memory_refined_supported_decode_shape_avoid_of_families
      iface
      h_r_avoid
      h_jalr_avoid
      h_alu_avoid
      h_memory_avoid
      h_shift_avoid
      h_branch_avoid
      h_upper_avoid
      h_jump_avoid
      h_fence_avoid)
    h_lower
    (memory_refined_supported_decode_shape_rows_of_families
      iface
      h_r_rows
      h_jalr_rows
      h_alu_rows
      h_memory_rows
      h_shift_rows
      h_branch_rows
      h_upper_rows
      h_jump_rows
      h_fence_rows)
    h_opcode

theorem memory_refined_supported_decode_shape_completeness_of_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory : MemoryRegisterImmediateCompletenessAvoidingKnownBugs iface)
    (h_shift :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with
    h_r_shape | h_jalr_shape | h_alu_shape | h_memory_shape |
    h_shift_shape | h_branch_shape | h_upper_shape | h_jump_shape |
    h_fence_shape
  · exact h_r raw h_r_shape h_sail h_not_gap
  · exact h_jalr raw h_jalr_shape h_sail h_not_gap
  · exact h_alu raw h_alu_shape h_sail h_not_gap
  · exact h_memory raw h_memory_shape h_sail h_not_gap
  · exact h_shift raw h_shift_shape h_sail h_not_gap
  · exact h_branch raw h_branch_shape h_sail h_not_gap
  · exact h_upper raw h_upper_shape h_sail h_not_gap
  · exact h_jump raw h_jump_shape h_sail h_not_gap
  · exact h_fence raw h_fence_shape h_sail h_not_gap

theorem memory_refined_supported_decode_shape_completeness_of_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_r_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_shift_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_r_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_shift_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface :=
  memory_refined_supported_decode_shape_completeness_of_shape_avoid_and_rows
    iface
    (memory_refined_supported_decode_shape_avoid_of_families
      iface
      h_r_avoid
      h_jalr_avoid
      h_alu_avoid
      h_memory_avoid
      h_shift_avoid
      h_branch_avoid
      h_upper_avoid
      h_jump_avoid
      h_fence_avoid)
    h_lower
    (memory_refined_supported_decode_shape_rows_of_families
      iface
      h_r_rows
      h_jalr_rows
      h_alu_rows
      h_memory_rows
      h_shift_rows
      h_branch_rows
      h_upper_rows
      h_jump_rows
      h_fence_rows)
    h_opcode

theorem supported_decode_shape_avoid_of_memory_refined_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_shift :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.SupportedDecodeShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with
    h_r_shape | h_i_shape | h_shift_shape | h_store_shape |
    h_branch_shape | h_upper_jump_shape | h_fence_shape
  · exact h_r raw h_r_shape h_sail h_not_gap
  · rcases Rv64imShapes.i_type_register_immediate_shape_cases h_i_shape with
      h_jalr_shape | h_alu_shape | h_load_shape
    · exact h_jalr raw h_jalr_shape h_sail h_not_gap
    · exact h_alu raw h_alu_shape h_sail h_not_gap
    · exact h_memory raw (.inl h_load_shape) h_sail h_not_gap
  · exact h_shift raw h_shift_shape h_sail h_not_gap
  · exact h_memory raw (.inr h_store_shape) h_sail h_not_gap
  · exact h_branch raw h_branch_shape h_sail h_not_gap
  · rcases h_upper_jump_shape with h_upper_shape | h_jump_shape
    · exact h_upper raw h_upper_shape h_sail h_not_gap
    · exact h_jump raw h_jump_shape h_sail h_not_gap
  · exact h_fence raw h_fence_shape h_sail h_not_gap

theorem supported_decode_shape_rows_of_memory_refined_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_shift :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.SupportedDecodeShape := by
  intro raw h_shape h_lowerable
  rcases h_shape with
    h_r_shape | h_i_shape | h_shift_shape | h_store_shape |
    h_branch_shape | h_upper_jump_shape | h_fence_shape
  · exact h_r raw h_r_shape h_lowerable
  · rcases Rv64imShapes.i_type_register_immediate_shape_cases h_i_shape with
      h_jalr_shape | h_alu_shape | h_load_shape
    · exact h_jalr raw h_jalr_shape h_lowerable
    · exact h_alu raw h_alu_shape h_lowerable
    · exact h_memory raw (.inl h_load_shape) h_lowerable
  · exact h_shift raw h_shift_shape h_lowerable
  · exact h_memory raw (.inr h_store_shape) h_lowerable
  · exact h_branch raw h_branch_shape h_lowerable
  · rcases h_upper_jump_shape with h_upper_shape | h_jump_shape
    · exact h_upper raw h_upper_shape h_lowerable
    · exact h_jump raw h_jump_shape h_lowerable
  · exact h_fence raw h_fence_shape h_lowerable

theorem supported_decode_shape_soundness_input_of_memory_refined_families
    (iface : Rv.Interface)
    (h_r : RTypeRegisterSoundnessInputComplete iface)
    (h_jalr : JalrRegisterImmediateSoundnessInputComplete iface)
    (h_alu : ImmediateAluRegisterSoundnessInputComplete iface)
    (h_memory : MemoryRegisterImmediateSoundnessInputComplete iface)
    (h_shift : ShiftRegisterSoundnessInputComplete iface)
    (h_branch : BranchRegisterImmediateSoundnessInputComplete iface)
    (h_upper : UpperRegisterImmediateSoundnessInputComplete iface)
    (h_jump : JumpRegisterImmediateSoundnessInputComplete iface)
    (h_fence : SupportedFencePredSuccSoundnessInputComplete iface) :
    SupportedDecodeSoundnessInputComplete iface := by
  intro raw h_shape h_lowerable
  rcases h_shape with
    h_r_shape | h_i_shape | h_shift_shape | h_store_shape |
    h_branch_shape | h_upper_jump_shape | h_fence_shape
  · exact h_r raw h_r_shape h_lowerable
  · rcases Rv64imShapes.i_type_register_immediate_shape_cases h_i_shape with
      h_jalr_shape | h_alu_shape | h_load_shape
    · exact h_jalr raw h_jalr_shape h_lowerable
    · exact h_alu raw h_alu_shape h_lowerable
    · exact h_memory raw (.inl h_load_shape) h_lowerable
  · exact h_shift raw h_shift_shape h_lowerable
  · exact h_memory raw (.inr h_store_shape) h_lowerable
  · exact h_branch raw h_branch_shape h_lowerable
  · rcases h_upper_jump_shape with h_upper_shape | h_jump_shape
    · exact h_upper raw h_upper_shape h_lowerable
    · exact h_jump raw h_jump_shape h_lowerable
  · exact h_fence raw h_fence_shape h_lowerable

theorem supported_decode_shape_completeness_of_memory_refined_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory : MemoryRegisterImmediateCompletenessAvoidingKnownBugs iface)
    (h_shift :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    SupportedDecodeCompletenessAvoidingKnownBugs iface := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with
    h_r_shape | h_i_shape | h_shift_shape | h_store_shape |
    h_branch_shape | h_upper_jump_shape | h_fence_shape
  · exact h_r raw h_r_shape h_sail h_not_gap
  · rcases Rv64imShapes.i_type_register_immediate_shape_cases h_i_shape with
      h_jalr_shape | h_alu_shape | h_load_shape
    · exact h_jalr raw h_jalr_shape h_sail h_not_gap
    · exact h_alu raw h_alu_shape h_sail h_not_gap
    · exact h_memory raw (.inl h_load_shape) h_sail h_not_gap
  · exact h_shift raw h_shift_shape h_sail h_not_gap
  · exact h_memory raw (.inr h_store_shape) h_sail h_not_gap
  · exact h_branch raw h_branch_shape h_sail h_not_gap
  · rcases h_upper_jump_shape with h_upper_shape | h_jump_shape
    · exact h_upper raw h_upper_shape h_sail h_not_gap
    · exact h_jump raw h_jump_shape h_sail h_not_gap
  · exact h_fence raw h_fence_shape h_sail h_not_gap

theorem supported_decode_shape_completeness_of_memory_refined_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_r_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_shift_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_r_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_jalr_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_memory_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_shift_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_branch_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterImmediateShape)
    (h_fence_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    SupportedDecodeCompletenessAvoidingKnownBugs iface :=
  supported_decode_shape_completeness_of_shape_avoid_and_rows
    iface
    (supported_decode_shape_avoid_of_memory_refined_families
      iface
      h_r_avoid
      h_jalr_avoid
      h_alu_avoid
      h_memory_avoid
      h_shift_avoid
      h_branch_avoid
      h_upper_avoid
      h_jump_avoid
      h_fence_avoid)
    h_lower
    (supported_decode_shape_rows_of_memory_refined_families
      iface
      h_r_rows
      h_jalr_rows
      h_alu_rows
      h_memory_rows
      h_shift_rows
      h_branch_rows
      h_upper_rows
      h_jump_rows
      h_fence_rows)
    h_opcode

end ZiskFv.Completeness.Rv64im
