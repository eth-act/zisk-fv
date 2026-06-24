import ZiskFv.Completeness.Rv64im.SupportedDecodeRefinedFamilies

/-!
# RV64IM completeness — global RV64IM completeness targets and stable theorem names

Theorem cluster split verbatim out of `ZiskFv/Completeness/Rv64im.lean`.
-/

namespace ZiskFv.Completeness.Rv64im

open ZiskFv.Completeness

/-- Global RV64IM completeness target in the current proof style.

The Sail-side premise says the Sail executable instruction domain is exactly
within the RV64IM supported-decode shape modeled here. The remaining premises
are the ZisK-side family obligations: each family must be accepted by the
extracted production decoder outside known gaps, and its lowering path must
materialize a row. -/
theorem rv64im_completeness_of_memory_refined_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInSupportedDecode iface)
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
    Rv64imCompletenessAvoidingKnownBugs iface :=
  rv64im_completeness_of_supported_decode_shape
    iface
    h_sail_subset
    (supported_decode_shape_completeness_of_memory_refined_family_avoid_and_rows
      iface
      h_r_avoid
      h_jalr_avoid
      h_alu_avoid
      h_memory_avoid
      h_shift_avoid
      h_branch_avoid
      h_upper_avoid
      h_jump_avoid
      h_fence_avoid
      h_lower
      h_r_rows
      h_jalr_rows
      h_alu_rows
      h_memory_rows
      h_shift_rows
      h_branch_rows
      h_upper_rows
      h_jump_rows
      h_fence_rows
      h_opcode)

/-- Stable name for the checked-in global RV64IM completeness theorem.

This is the same proof surface as
`rv64im_completeness_of_memory_refined_family_avoid_and_rows`: Sail raw words
are first contained in the checked RV64IM supported-decode shape, then the
production ZisK family obligations establish completeness outside explicit
known gaps such as generic FENCE restrictions. -/
theorem rv64im_global_completeness_avoiding_known_bugs
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInSupportedDecode iface)
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
    Rv64imCompletenessAvoidingKnownBugs iface :=
  rv64im_completeness_of_memory_refined_family_avoid_and_rows
    iface
    h_sail_subset
    h_r_avoid
    h_jalr_avoid
    h_alu_avoid
    h_memory_avoid
    h_shift_avoid
    h_branch_avoid
    h_upper_avoid
    h_jump_avoid
    h_fence_avoid
    h_lower
    h_r_rows
    h_jalr_rows
    h_alu_rows
    h_memory_rows
    h_shift_rows
    h_branch_rows
    h_upper_rows
    h_jump_rows
    h_fence_rows
    h_opcode

/-- Stable acceptance-focused global theorem.

Unlike `rv64im_global_completeness_avoiding_known_bugs`, this proof path does
not require per-family edge-grid row premises. The Sail-side containment
identifies the full supported-decode raw domain; the generated production
harness supplies decode support outside explicit decode gaps, universal
lowering, universal row materialization, and opcode coverage. -/
theorem rv64im_global_completeness_avoiding_known_decode_bugs
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInSupportedDecode iface)
    (h_supported : SupportedDecodeAvoidKnownDecodeBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows : Rv.Interface.RowMaterializationComplete iface)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv64imCompletenessAvoidingKnownDecodeBugs iface :=
  rv64im_completeness_of_supported_decode_avoid_known_decode_bugs
    iface
    h_sail_subset
    h_supported
    h_lower
    h_rows
    h_opcode

/-- Stable global route-completeness theorem.

This strengthens `rv64im_global_completeness_avoiding_known_decode_bugs` with
the static row contract needed by the opcode soundness interfaces.  Sail is
still the public source of valid raw words: `h_sail_subset` is the checked-in
Sail-to-shape bridge, while `h_soundness` is the generated production-ZisK
obligation over that full shape. -/
theorem rv64im_global_completeness_with_soundness_input_avoiding_known_decode_bugs
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInSupportedDecode iface)
    (h_supported : SupportedDecodeAvoidKnownDecodeBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows : Rv.Interface.RowMaterializationComplete iface)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface)
    (h_soundness : SupportedDecodeSoundnessInputComplete iface) :
    Rv64imCompletenessWithSoundnessInputAvoidingKnownDecodeBugs iface :=
  Rv.Interface.completeness_with_soundness_input_avoiding_known_decode_bugs
    iface
    Rv64imShapes.SupportedDecodeShape
    h_sail_subset
    h_supported
    h_lower
    h_rows
    h_opcode
    h_soundness

/-- Family-instantiated global route-completeness theorem.

This is only a helper for the generated route aggregation: each family proves
its own production-row soundness-input contract, and this theorem assembles
those contracts into the uniform completeness endpoint
(`ZiskFv.Completeness.root_completeness`). -/
theorem rv64im_global_completeness_with_family_soundness_inputs_avoiding_known_decode_bugs
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInSupportedDecode iface)
    (h_supported : SupportedDecodeAvoidKnownDecodeBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows : Rv.Interface.RowMaterializationComplete iface)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface)
    (h_r_soundness : RTypeRegisterSoundnessInputComplete iface)
    (h_jalr_soundness : JalrRegisterImmediateSoundnessInputComplete iface)
    (h_alu_soundness : ImmediateAluRegisterSoundnessInputComplete iface)
    (h_memory_soundness : MemoryRegisterImmediateSoundnessInputComplete iface)
    (h_shift_soundness : ShiftRegisterSoundnessInputComplete iface)
    (h_branch_soundness : BranchRegisterImmediateSoundnessInputComplete iface)
    (h_upper_soundness : UpperRegisterImmediateSoundnessInputComplete iface)
    (h_jump_soundness : JumpRegisterImmediateSoundnessInputComplete iface)
    (h_fence_soundness : SupportedFencePredSuccSoundnessInputComplete iface) :
    Rv64imCompletenessWithSoundnessInputAvoidingKnownDecodeBugs iface :=
  rv64im_global_completeness_with_soundness_input_avoiding_known_decode_bugs
    iface
    h_sail_subset
    h_supported
    h_lower
    h_rows
    h_opcode
    (supported_decode_shape_soundness_input_of_memory_refined_families
      iface
      h_r_soundness
      h_jalr_soundness
      h_alu_soundness
      h_memory_soundness
      h_shift_soundness
      h_branch_soundness
      h_upper_soundness
      h_jump_soundness
      h_fence_soundness)

theorem rv64im_completeness_of_memory_refined_family_avoid_no_gap_sail_and_rows
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInMemoryRefinedSupportedDecode iface)
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
    Rv64imCompletenessAvoidingKnownBugs iface :=
  rv64im_completeness_of_memory_refined_supported_decode_circuit_covered_known_good
    iface
    h_sail_subset
    (memory_refined_supported_decode_shape_circuit_covered_known_good_of_family_avoid_no_gap_sail_and_rows
      iface
      h_r_no_gap
      h_jalr_no_gap
      h_alu_no_gap
      h_memory_no_gap
      h_shift_no_gap
      h_branch_no_gap
      h_upper_no_gap
      h_jump_no_gap
      h_fence_no_gap
      h_r_sail
      h_jalr_sail
      h_alu_sail
      h_memory_sail
      h_shift_sail
      h_branch_sail
      h_upper_sail
      h_jump_sail
      h_fence_sail
      h_r_avoid
      h_jalr_avoid
      h_alu_avoid
      h_memory_avoid
      h_shift_avoid
      h_branch_avoid
      h_upper_avoid
      h_jump_avoid
      h_fence_avoid
      h_lower
      h_r_rows
      h_jalr_rows
      h_alu_rows
      h_memory_rows
      h_shift_rows
      h_branch_rows
      h_upper_rows
      h_jump_rows
      h_fence_rows
      h_opcode)


end ZiskFv.Completeness.Rv64im
