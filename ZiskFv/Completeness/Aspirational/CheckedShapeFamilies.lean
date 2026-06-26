import ZiskFv.Completeness.Aspirational.CoreAndShapeFamilies

/- ⚠ ASPIRATIONAL / QUARANTINED — not wired to any live completeness endpoint.
   Abstract `Rv.Interface`-parametrized route; no concrete `Interface` is ever
   built, and the live endpoints in `ZiskFv.Completeness`
   (`sail_executable_within_supported_decode_shape`, `skeletal_root_completeness`)
   do not depend on it. Intended *eventual* composition machinery for when the
   Aeneas-extracted ZisK coverage proofs can be imported into this build. Kept
   compiling via `ZiskFv.lean` for preservation only.
   See `ZiskFv/Completeness/Aspirational/README.md`. -/

/-!
# RV64IM completeness — exhaustive/edge/wide checked shape families and circuit-covered-known-good

Theorem cluster split verbatim out of `ZiskFv/Completeness/Rv64im.lean`.
-/

namespace ZiskFv.Completeness.Rv64im

open ZiskFv.Completeness

theorem exhaustive_checked_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ExhaustiveCheckedShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.ExhaustiveCheckedShape
    h_complete

theorem exhaustive_checked_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ExhaustiveCheckedShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.ExhaustiveCheckedShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem edge_checked_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.EdgeCheckedShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.EdgeCheckedShape
    h_complete

theorem edge_checked_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.EdgeCheckedShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.EdgeCheckedShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.EdgeCheckedShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem wide_checked_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.WideCheckedShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.WideCheckedShape
    h_complete

theorem wide_checked_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.WideCheckedShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.WideCheckedShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.WideCheckedShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem exhaustive_checked_shape_circuit_covered_known_good_of_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_shift :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_fence :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    ExhaustiveCheckedCircuitCoveredKnownGood iface := by
  intro raw h_shape
  rcases h_shape with h_r_shape | h_shift_shape | h_fence_shape
  · exact h_r raw h_r_shape
  · exact h_shift raw h_shift_shape
  · exact h_fence raw h_fence_shape

theorem edge_checked_shape_circuit_covered_known_good_of_families
    (iface : Rv.Interface)
    (h_i :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape)
    (h_store :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper_jump :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape) :
    EdgeCheckedCircuitCoveredKnownGood iface := by
  intro raw h_shape
  rcases h_shape with h_i_shape | h_store_shape | h_branch_shape | h_upper_jump_shape
  · exact h_i raw h_i_shape
  · exact h_store raw h_store_shape
  · exact h_branch raw h_branch_shape
  · exact h_upper_jump raw h_upper_jump_shape

theorem refined_edge_checked_shape_circuit_covered_known_good_of_families
    (iface : Rv.Interface)
    (h_jalr :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.JalrRegisterEdgeImmediateShape)
    (h_alu :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape)
    (h_load :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.LoadRegisterEdgeImmediateShape)
    (h_store :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.UpperRegisterEdgeImmediateShape)
    (h_jump :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.JumpRegisterEdgeImmediateShape) :
    RefinedEdgeCheckedCircuitCoveredKnownGood iface := by
  intro raw h_shape
  rcases h_shape with
    h_jalr_shape | h_alu_shape | h_load_shape | h_store_shape |
    h_branch_shape | h_upper_shape | h_jump_shape
  · exact h_jalr raw h_jalr_shape
  · exact h_alu raw h_alu_shape
  · exact h_load raw h_load_shape
  · exact h_store raw h_store_shape
  · exact h_branch raw h_branch_shape
  · exact h_upper raw h_upper_shape
  · exact h_jump raw h_jump_shape

theorem wide_checked_shape_circuit_covered_known_good_of_families
    (iface : Rv.Interface)
    (h_exhaustive : ExhaustiveCheckedCircuitCoveredKnownGood iface)
    (h_edge : EdgeCheckedCircuitCoveredKnownGood iface) :
    WideCheckedCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_or
    iface
    h_exhaustive
    h_edge

theorem wide_refined_checked_shape_circuit_covered_known_good_of_families
    (iface : Rv.Interface)
    (h_exhaustive : ExhaustiveCheckedCircuitCoveredKnownGood iface)
    (h_edge : RefinedEdgeCheckedCircuitCoveredKnownGood iface) :
    WideRefinedCheckedCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_or
    iface
    h_exhaustive
    h_edge

theorem memory_register_immediate_shape_circuit_covered_known_good_of_families
    (iface : Rv.Interface)
    (h_load : LoadRegisterImmediateCircuitCoveredKnownGood iface)
    (h_store : StoreRegisterImmediateCircuitCoveredKnownGood iface) :
    MemoryRegisterImmediateCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_or iface h_load h_store

theorem memory_refined_supported_decode_shape_circuit_covered_known_good_of_families
    (iface : Rv.Interface)
    (h_r : RTypeRegisterCircuitCoveredKnownGood iface)
    (h_jalr : JalrRegisterImmediateCircuitCoveredKnownGood iface)
    (h_alu : ImmediateAluRegisterCircuitCoveredKnownGood iface)
    (h_memory : MemoryRegisterImmediateCircuitCoveredKnownGood iface)
    (h_shift : ShiftRegisterCircuitCoveredKnownGood iface)
    (h_branch : BranchRegisterImmediateCircuitCoveredKnownGood iface)
    (h_upper : UpperRegisterImmediateCircuitCoveredKnownGood iface)
    (h_jump : JumpRegisterImmediateCircuitCoveredKnownGood iface)
    (h_fence : SupportedFencePredSuccCircuitCoveredKnownGood iface) :
    MemoryRefinedSupportedDecodeCircuitCoveredKnownGood iface := by
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

theorem supported_decode_shape_circuit_covered_known_good_of_memory_refined_families
    (iface : Rv.Interface)
    (h_r : RTypeRegisterCircuitCoveredKnownGood iface)
    (h_jalr : JalrRegisterImmediateCircuitCoveredKnownGood iface)
    (h_alu : ImmediateAluRegisterCircuitCoveredKnownGood iface)
    (h_memory : MemoryRegisterImmediateCircuitCoveredKnownGood iface)
    (h_shift : ShiftRegisterCircuitCoveredKnownGood iface)
    (h_branch : BranchRegisterImmediateCircuitCoveredKnownGood iface)
    (h_upper : UpperRegisterImmediateCircuitCoveredKnownGood iface)
    (h_jump : JumpRegisterImmediateCircuitCoveredKnownGood iface)
    (h_fence : SupportedFencePredSuccCircuitCoveredKnownGood iface) :
    SupportedDecodeCircuitCoveredKnownGood iface := by
  intro raw h_shape
  rcases h_shape with
    h_r_shape | h_i_shape | h_shift_shape | h_store_shape |
    h_branch_shape | h_upper_jump_shape | h_fence_shape
  · exact h_r raw h_r_shape
  · rcases Rv64imShapes.i_type_register_immediate_shape_cases h_i_shape with
      h_jalr_shape | h_alu_shape | h_load_shape
    · exact h_jalr raw h_jalr_shape
    · exact h_alu raw h_alu_shape
    · exact h_memory raw (.inl h_load_shape)
  · exact h_shift raw h_shift_shape
  · exact h_memory raw (.inr h_store_shape)
  · exact h_branch raw h_branch_shape
  · rcases h_upper_jump_shape with h_upper_shape | h_jump_shape
    · exact h_upper raw h_upper_shape
    · exact h_jump raw h_jump_shape
  · exact h_fence raw h_fence_shape

theorem supported_decode_shape_circuit_covered_known_good_of_memory_refined_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : MemoryRefinedSupportedDecodeCircuitCoveredKnownGood iface) :
    SupportedDecodeCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.supported_decode_shape_subset_memory_refined_supported_decode_shape
        h_shape)
    h_covered

theorem memory_refined_supported_decode_shape_circuit_covered_known_good_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : SupportedDecodeCircuitCoveredKnownGood iface) :
    MemoryRefinedSupportedDecodeCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.memory_refined_supported_decode_shape_subset_supported_decode
        h_shape)
    h_covered

theorem r_type_register_shape_circuit_covered_known_good_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : SupportedDecodeCircuitCoveredKnownGood iface) :
    RTypeRegisterCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape => Or.inl h_shape)
    h_covered

theorem jalr_register_immediate_shape_circuit_covered_known_good_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : SupportedDecodeCircuitCoveredKnownGood iface) :
    JalrRegisterImmediateCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jalr_register_immediate_shape_subset_supported_decode
        h_shape)
    h_covered

theorem immediate_alu_register_shape_circuit_covered_known_good_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : SupportedDecodeCircuitCoveredKnownGood iface) :
    ImmediateAluRegisterCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.immediate_alu_register_shape_subset_supported_decode
        h_shape)
    h_covered

theorem memory_register_immediate_shape_circuit_covered_known_good_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : SupportedDecodeCircuitCoveredKnownGood iface) :
    MemoryRegisterImmediateCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.memory_register_immediate_shape_subset_supported_decode
        h_shape)
    h_covered

theorem shift_register_shape_circuit_covered_known_good_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : SupportedDecodeCircuitCoveredKnownGood iface) :
    ShiftRegisterCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape => Or.inr (Or.inr (Or.inl h_shape)))
    h_covered

theorem branch_register_immediate_shape_circuit_covered_known_good_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : SupportedDecodeCircuitCoveredKnownGood iface) :
    BranchRegisterImmediateCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_shape)))))
    h_covered

theorem upper_register_immediate_shape_circuit_covered_known_good_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : SupportedDecodeCircuitCoveredKnownGood iface) :
    UpperRegisterImmediateCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.upper_register_immediate_shape_subset_supported_decode
        h_shape)
    h_covered

theorem jump_register_immediate_shape_circuit_covered_known_good_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : SupportedDecodeCircuitCoveredKnownGood iface) :
    JumpRegisterImmediateCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jump_register_immediate_shape_subset_supported_decode
        h_shape)
    h_covered

theorem supported_fence_pred_succ_shape_circuit_covered_known_good_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_covered : SupportedDecodeCircuitCoveredKnownGood iface) :
    SupportedFencePredSuccCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _raw h_shape =>
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_shape))))))
    h_covered

theorem rv64im_completeness_of_memory_refined_family_circuit_covered_known_good
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInSupportedDecode iface)
    (h_r : RTypeRegisterCircuitCoveredKnownGood iface)
    (h_jalr : JalrRegisterImmediateCircuitCoveredKnownGood iface)
    (h_alu : ImmediateAluRegisterCircuitCoveredKnownGood iface)
    (h_memory : MemoryRegisterImmediateCircuitCoveredKnownGood iface)
    (h_shift : ShiftRegisterCircuitCoveredKnownGood iface)
    (h_branch : BranchRegisterImmediateCircuitCoveredKnownGood iface)
    (h_upper : UpperRegisterImmediateCircuitCoveredKnownGood iface)
    (h_jump : JumpRegisterImmediateCircuitCoveredKnownGood iface)
    (h_fence : SupportedFencePredSuccCircuitCoveredKnownGood iface) :
    Rv64imCompletenessAvoidingKnownBugs iface :=
  rv64im_completeness_of_supported_decode_circuit_covered_known_good
    iface
    h_sail_subset
    (supported_decode_shape_circuit_covered_known_good_of_memory_refined_families
      iface
      h_r
      h_jalr
      h_alu
      h_memory
      h_shift
      h_branch
      h_upper
      h_jump
      h_fence)

theorem rv64im_completeness_of_memory_refined_family_circuit_covered_known_good_of_memory_refined_sail
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInMemoryRefinedSupportedDecode iface)
    (h_r : RTypeRegisterCircuitCoveredKnownGood iface)
    (h_jalr : JalrRegisterImmediateCircuitCoveredKnownGood iface)
    (h_alu : ImmediateAluRegisterCircuitCoveredKnownGood iface)
    (h_memory : MemoryRegisterImmediateCircuitCoveredKnownGood iface)
    (h_shift : ShiftRegisterCircuitCoveredKnownGood iface)
    (h_branch : BranchRegisterImmediateCircuitCoveredKnownGood iface)
    (h_upper : UpperRegisterImmediateCircuitCoveredKnownGood iface)
    (h_jump : JumpRegisterImmediateCircuitCoveredKnownGood iface)
    (h_fence : SupportedFencePredSuccCircuitCoveredKnownGood iface) :
    Rv64imCompletenessAvoidingKnownBugs iface :=
  rv64im_completeness_of_memory_refined_supported_decode_circuit_covered_known_good
    iface
    h_sail_subset
    (memory_refined_supported_decode_shape_circuit_covered_known_good_of_families
      iface
      h_r
      h_jalr
      h_alu
      h_memory
      h_shift
      h_branch
      h_upper
      h_jump
      h_fence)

theorem exhaustive_checked_shape_completeness_of_circuit_covered_known_good
    (iface : Rv.Interface)
    (h_covered : ExhaustiveCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ExhaustiveCheckedShape :=
  shape_family_completeness_of_circuit_covered_known_good
    iface
    Rv64imShapes.ExhaustiveCheckedShape
    h_covered

theorem edge_checked_shape_completeness_of_circuit_covered_known_good
    (iface : Rv.Interface)
    (h_covered : EdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.EdgeCheckedShape :=
  shape_family_completeness_of_circuit_covered_known_good
    iface
    Rv64imShapes.EdgeCheckedShape
    h_covered

theorem refined_edge_checked_shape_completeness_of_circuit_covered_known_good
    (iface : Rv.Interface)
    (h_covered : RefinedEdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.RefinedEdgeCheckedShape :=
  shape_family_completeness_of_circuit_covered_known_good
    iface
    Rv64imShapes.RefinedEdgeCheckedShape
    h_covered

theorem wide_checked_shape_completeness_of_circuit_covered_known_good
    (iface : Rv.Interface)
    (h_covered : WideCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.WideCheckedShape :=
  shape_family_completeness_of_circuit_covered_known_good
    iface
    Rv64imShapes.WideCheckedShape
    h_covered

theorem wide_refined_checked_shape_completeness_of_circuit_covered_known_good
    (iface : Rv.Interface)
    (h_covered : WideRefinedCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.WideRefinedCheckedShape :=
  shape_family_completeness_of_circuit_covered_known_good
    iface
    Rv64imShapes.WideRefinedCheckedShape
    h_covered

theorem exhaustive_checked_shape_circuit_covered_known_good_of_wide_checked_shape
    (iface : Rv.Interface)
    (h_covered : WideCheckedCircuitCoveredKnownGood iface) :
    ExhaustiveCheckedCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inl h_shape)
    h_covered

theorem edge_checked_shape_circuit_covered_known_good_of_wide_checked_shape
    (iface : Rv.Interface)
    (h_covered : WideCheckedCircuitCoveredKnownGood iface) :
    EdgeCheckedCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr h_shape)
    h_covered

theorem refined_edge_checked_shape_circuit_covered_known_good_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : EdgeCheckedCircuitCoveredKnownGood iface) :
    RefinedEdgeCheckedCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.refined_edge_checked_shape_subset_edge_checked h_shape)
    h_covered

theorem edge_checked_shape_circuit_covered_known_good_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : RefinedEdgeCheckedCircuitCoveredKnownGood iface) :
    EdgeCheckedCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.edge_checked_shape_subset_refined_edge_checked h_shape)
    h_covered

theorem wide_refined_checked_shape_circuit_covered_known_good_of_wide_checked_shape
    (iface : Rv.Interface)
    (h_covered : WideCheckedCircuitCoveredKnownGood iface) :
    WideRefinedCheckedCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.wide_refined_checked_shape_subset_wide_checked h_shape)
    h_covered

theorem wide_checked_shape_circuit_covered_known_good_of_wide_refined_checked_shape
    (iface : Rv.Interface)
    (h_covered : WideRefinedCheckedCircuitCoveredKnownGood iface) :
    WideCheckedCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.wide_checked_shape_subset_wide_refined_checked h_shape)
    h_covered

theorem exhaustive_checked_shape_circuit_covered_known_good_of_wide_refined_checked_shape
    (iface : Rv.Interface)
    (h_covered : WideRefinedCheckedCircuitCoveredKnownGood iface) :
    ExhaustiveCheckedCircuitCoveredKnownGood iface :=
  exhaustive_checked_shape_circuit_covered_known_good_of_wide_checked_shape
    iface
    (wide_checked_shape_circuit_covered_known_good_of_wide_refined_checked_shape
      iface h_covered)

theorem refined_edge_checked_shape_circuit_covered_known_good_of_wide_refined_checked_shape
    (iface : Rv.Interface)
    (h_covered : WideRefinedCheckedCircuitCoveredKnownGood iface) :
    RefinedEdgeCheckedCircuitCoveredKnownGood iface :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr h_shape)
    h_covered

theorem r_type_register_shape_circuit_covered_known_good_of_exhaustive_checked_shape
    (iface : Rv.Interface)
    (h_covered : ExhaustiveCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.RTypeRegisterShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inl h_shape)
    h_covered

theorem shift_register_shape_circuit_covered_known_good_of_exhaustive_checked_shape
    (iface : Rv.Interface)
    (h_covered : ExhaustiveCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.ShiftRegisterShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inl h_shape))
    h_covered

theorem supported_fence_pred_succ_shape_circuit_covered_known_good_of_exhaustive_checked_shape
    (iface : Rv.Interface)
    (h_covered : ExhaustiveCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.SupportedFencePredSuccShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inr h_shape))
    h_covered

theorem i_type_register_edge_immediate_shape_circuit_covered_known_good_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : EdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.ITypeRegisterEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inl h_shape)
    h_covered

theorem store_register_edge_immediate_shape_circuit_covered_known_good_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : EdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.StoreRegisterEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inl h_shape))
    h_covered

theorem branch_register_edge_immediate_shape_circuit_covered_known_good_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : EdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.BranchRegisterEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inl h_shape)))
    h_covered

theorem upper_and_jump_edge_immediate_shape_circuit_covered_known_good_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : EdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.UpperAndJumpEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr h_shape)))
    h_covered

theorem jalr_register_edge_immediate_shape_circuit_covered_known_good_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : RefinedEdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.JalrRegisterEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inl h_shape)
    h_covered

theorem immediate_alu_register_edge_immediate_shape_circuit_covered_known_good_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : RefinedEdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inl h_shape))
    h_covered

theorem load_register_edge_immediate_shape_circuit_covered_known_good_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : RefinedEdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.LoadRegisterEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inl h_shape)))
    h_covered

theorem store_register_edge_immediate_shape_circuit_covered_known_good_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : RefinedEdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.StoreRegisterEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inl h_shape))))
    h_covered

theorem branch_register_edge_immediate_shape_circuit_covered_known_good_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : RefinedEdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.BranchRegisterEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_shape)))))
    h_covered

theorem upper_register_edge_immediate_shape_circuit_covered_known_good_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : RefinedEdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.UpperRegisterEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_shape))))))
    h_covered

theorem jump_register_edge_immediate_shape_circuit_covered_known_good_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_covered : RefinedEdgeCheckedCircuitCoveredKnownGood iface) :
    Rv.Interface.ShapeCircuitCoveredKnownGood
      iface
      Rv64imShapes.JumpRegisterEdgeImmediateShape :=
  Rv.Interface.shape_circuit_covered_known_good_mono
    iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_shape))))))
    h_covered

end ZiskFv.Completeness.Rv64im
