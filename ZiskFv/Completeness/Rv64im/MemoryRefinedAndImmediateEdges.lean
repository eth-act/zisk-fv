import ZiskFv.Completeness.Rv64im.SupportedDecodeShape

/-!
# RV64IM completeness — memory-register-immediate, refined/wide-refined edge, and immediate/upper-jump edge families

Theorem cluster split verbatim out of `ZiskFv/Completeness/Rv64im.lean`.
-/

namespace ZiskFv.Completeness.Rv64im

open ZiskFv.Completeness

theorem load_register_immediate_shape_completeness_of_i_type_register_immediate_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.LoadRegisterImmediateShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape =>
      Rv64imShapes.load_register_immediate_shape_subset h_shape)
    h_complete

theorem memory_register_immediate_shape_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    MemoryRegisterImmediateCompletenessAvoidingKnownBugs iface :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape =>
      Rv64imShapes.memory_register_immediate_shape_subset_supported_decode
        h_shape)
    h_complete

theorem memory_register_immediate_shape_completeness_of_families
    (iface : Rv.Interface)
    (h_load :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
    (h_store :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.StoreRegisterImmediateShape) :
    MemoryRegisterImmediateCompletenessAvoidingKnownBugs iface := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_load_shape | h_store_shape
  · exact h_load raw h_load_shape h_sail h_not_gap
  · exact h_store raw h_store_shape h_sail h_not_gap

theorem load_register_immediate_shape_avoid_of_i_type_register_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.LoadRegisterImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape =>
      Rv64imShapes.load_register_immediate_shape_subset h_shape)
    h_avoid

theorem jalr_register_immediate_shape_avoid_of_i_type_register_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.JalrRegisterImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape =>
      Rv64imShapes.jalr_register_immediate_shape_subset h_shape)
    h_avoid

theorem immediate_alu_register_shape_avoid_of_i_type_register_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.ImmediateAluRegisterShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape =>
      Rv64imShapes.immediate_alu_register_shape_subset h_shape)
    h_avoid

theorem memory_register_immediate_shape_avoid_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.MemoryRegisterImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape =>
      Rv64imShapes.memory_register_immediate_shape_subset_supported_decode
        h_shape)
    h_avoid

theorem memory_register_immediate_shape_avoid_of_families
    (iface : Rv.Interface)
    (h_load :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
    (h_store :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.StoreRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.MemoryRegisterImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_or iface h_load h_store

theorem load_register_immediate_shape_rows_of_i_type_register_immediate_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.LoadRegisterImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape =>
      Rv64imShapes.load_register_immediate_shape_subset h_shape)
    h_rows

theorem jalr_register_immediate_shape_rows_of_i_type_register_immediate_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.JalrRegisterImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape =>
      Rv64imShapes.jalr_register_immediate_shape_subset h_shape)
    h_rows

theorem immediate_alu_register_shape_rows_of_i_type_register_immediate_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ImmediateAluRegisterShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape =>
      Rv64imShapes.immediate_alu_register_shape_subset h_shape)
    h_rows

theorem memory_register_immediate_shape_rows_of_supported_decode_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.MemoryRegisterImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape =>
      Rv64imShapes.memory_register_immediate_shape_subset_supported_decode
        h_shape)
    h_rows

theorem memory_register_immediate_shape_rows_of_families
    (iface : Rv.Interface)
    (h_load :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
    (h_store :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.MemoryRegisterImmediateShape := by
  intro raw h_shape h_lowerable
  rcases h_shape with h_load_shape | h_store_shape
  · exact h_load raw h_load_shape h_lowerable
  · exact h_store raw h_store_shape h_lowerable

theorem memory_register_immediate_shape_completeness_of_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_load_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
    (h_store_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.StoreRegisterImmediateShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_load_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
    (h_store_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    MemoryRegisterImmediateCompletenessAvoidingKnownBugs iface :=
  shape_family_completeness_of_shape_avoid_and_rows
    iface
    Rv64imShapes.MemoryRegisterImmediateShape
    (memory_register_immediate_shape_avoid_of_families
      iface
      h_load_avoid
      h_store_avoid)
    h_lower
    (memory_register_immediate_shape_rows_of_families
      iface
      h_load_rows
      h_store_rows)
    h_opcode

theorem memory_register_immediate_shape_completeness_of_avoid_and_family_rows
    (iface : Rv.Interface)
    (h_memory_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.MemoryRegisterImmediateShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_load_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
    (h_store_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    MemoryRegisterImmediateCompletenessAvoidingKnownBugs iface :=
  shape_family_completeness_of_shape_avoid_and_rows
    iface
    Rv64imShapes.MemoryRegisterImmediateShape
    h_memory_avoid
    h_lower
    (memory_register_immediate_shape_rows_of_families
      iface
      h_load_rows
      h_store_rows)
    h_opcode

theorem refined_edge_checked_shape_completeness_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.EdgeCheckedShape) :
    RefinedEdgeCheckedCompletenessAvoidingKnownBugs iface :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.refined_edge_checked_shape_subset_edge_checked h_shape)
    h_complete

theorem edge_checked_shape_completeness_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_complete : RefinedEdgeCheckedCompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.EdgeCheckedShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.edge_checked_shape_subset_refined_edge_checked h_shape)
    h_complete

theorem refined_edge_checked_shape_avoid_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.RefinedEdgeCheckedShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.refined_edge_checked_shape_subset_edge_checked h_shape)
    h_avoid

theorem edge_checked_shape_avoid_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RefinedEdgeCheckedShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.EdgeCheckedShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.edge_checked_shape_subset_refined_edge_checked h_shape)
    h_avoid

theorem refined_edge_checked_shape_rows_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.RefinedEdgeCheckedShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.refined_edge_checked_shape_subset_edge_checked h_shape)
    h_rows

theorem edge_checked_shape_rows_of_refined_edge_checked_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RefinedEdgeCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.EdgeCheckedShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.edge_checked_shape_subset_refined_edge_checked h_shape)
    h_rows

theorem wide_refined_checked_shape_completeness_of_wide_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.WideCheckedShape) :
    WideRefinedCheckedCompletenessAvoidingKnownBugs iface :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.wide_refined_checked_shape_subset_wide_checked h_shape)
    h_complete

theorem wide_checked_shape_completeness_of_wide_refined_checked_shape
    (iface : Rv.Interface)
    (h_complete : WideRefinedCheckedCompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.WideCheckedShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.wide_checked_shape_subset_wide_refined_checked h_shape)
    h_complete

theorem wide_refined_checked_shape_avoid_of_wide_checked_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.WideCheckedShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.WideRefinedCheckedShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.wide_refined_checked_shape_subset_wide_checked h_shape)
    h_avoid

theorem wide_checked_shape_avoid_of_wide_refined_checked_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.WideRefinedCheckedShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.WideCheckedShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.wide_checked_shape_subset_wide_refined_checked h_shape)
    h_avoid

theorem wide_refined_checked_shape_rows_of_wide_checked_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.WideCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.WideRefinedCheckedShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.wide_refined_checked_shape_subset_wide_checked h_shape)
    h_rows

theorem wide_checked_shape_rows_of_wide_refined_checked_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.WideRefinedCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.WideCheckedShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _ h_shape =>
      Rv64imShapes.wide_checked_shape_subset_wide_refined_checked h_shape)
    h_rows

theorem refined_edge_checked_shape_completeness_of_families
    (iface : Rv.Interface)
    (h_jalr :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.JalrRegisterEdgeImmediateShape)
    (h_alu :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape)
    (h_load :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.LoadRegisterEdgeImmediateShape)
    (h_store :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperRegisterEdgeImmediateShape)
    (h_jump :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.JumpRegisterEdgeImmediateShape) :
    RefinedEdgeCheckedCompletenessAvoidingKnownBugs iface := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with
    h_jalr_shape | h_alu_shape | h_load_shape | h_store_shape |
    h_branch_shape | h_upper_shape | h_jump_shape
  · exact h_jalr raw h_jalr_shape h_sail h_not_gap
  · exact h_alu raw h_alu_shape h_sail h_not_gap
  · exact h_load raw h_load_shape h_sail h_not_gap
  · exact h_store raw h_store_shape h_sail h_not_gap
  · exact h_branch raw h_branch_shape h_sail h_not_gap
  · exact h_upper raw h_upper_shape h_sail h_not_gap
  · exact h_jump raw h_jump_shape h_sail h_not_gap

theorem refined_edge_checked_shape_avoid_of_families
    (iface : Rv.Interface)
    (h_jalr :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JalrRegisterEdgeImmediateShape)
    (h_alu :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape)
    (h_load :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.LoadRegisterEdgeImmediateShape)
    (h_store :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterEdgeImmediateShape)
    (h_jump :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.RefinedEdgeCheckedShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with
    h_jalr_shape | h_alu_shape | h_load_shape | h_store_shape |
    h_branch_shape | h_upper_shape | h_jump_shape
  · exact h_jalr raw h_jalr_shape h_sail h_not_gap
  · exact h_alu raw h_alu_shape h_sail h_not_gap
  · exact h_load raw h_load_shape h_sail h_not_gap
  · exact h_store raw h_store_shape h_sail h_not_gap
  · exact h_branch raw h_branch_shape h_sail h_not_gap
  · exact h_upper raw h_upper_shape h_sail h_not_gap
  · exact h_jump raw h_jump_shape h_sail h_not_gap

theorem refined_edge_checked_shape_rows_of_families
    (iface : Rv.Interface)
    (h_jalr :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JalrRegisterEdgeImmediateShape)
    (h_alu :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape)
    (h_load :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.LoadRegisterEdgeImmediateShape)
    (h_store :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterEdgeImmediateShape)
    (h_jump :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.RefinedEdgeCheckedShape := by
  intro raw h_shape h_lowerable
  rcases h_shape with
    h_jalr_shape | h_alu_shape | h_load_shape | h_store_shape |
    h_branch_shape | h_upper_shape | h_jump_shape
  · exact h_jalr raw h_jalr_shape h_lowerable
  · exact h_alu raw h_alu_shape h_lowerable
  · exact h_load raw h_load_shape h_lowerable
  · exact h_store raw h_store_shape h_lowerable
  · exact h_branch raw h_branch_shape h_lowerable
  · exact h_upper raw h_upper_shape h_lowerable
  · exact h_jump raw h_jump_shape h_lowerable

theorem refined_edge_checked_shape_completeness_of_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_jalr_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JalrRegisterEdgeImmediateShape)
    (h_alu_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape)
    (h_load_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.LoadRegisterEdgeImmediateShape)
    (h_store_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterEdgeImmediateShape)
    (h_jump_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterEdgeImmediateShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_jalr_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JalrRegisterEdgeImmediateShape)
    (h_alu_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape)
    (h_load_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.LoadRegisterEdgeImmediateShape)
    (h_store_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterEdgeImmediateShape)
    (h_jump_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterEdgeImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    RefinedEdgeCheckedCompletenessAvoidingKnownBugs iface :=
  shape_family_completeness_of_shape_avoid_and_rows
    iface
    Rv64imShapes.RefinedEdgeCheckedShape
    (refined_edge_checked_shape_avoid_of_families
      iface
      h_jalr_avoid
      h_alu_avoid
      h_load_avoid
      h_store_avoid
      h_branch_avoid
      h_upper_avoid
      h_jump_avoid)
    h_lower
    (refined_edge_checked_shape_rows_of_families
      iface
      h_jalr_rows
      h_alu_rows
      h_load_rows
      h_store_rows
      h_branch_rows
      h_upper_rows
      h_jump_rows)
    h_opcode

theorem wide_refined_checked_shape_completeness_of_families
    (iface : Rv.Interface)
    (h_exhaustive :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_refined_edge : RefinedEdgeCheckedCompletenessAvoidingKnownBugs iface) :
    WideRefinedCheckedCompletenessAvoidingKnownBugs iface := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_exhaustive_shape | h_edge_shape
  · exact h_exhaustive raw h_exhaustive_shape h_sail h_not_gap
  · exact h_refined_edge raw h_edge_shape h_sail h_not_gap

theorem wide_refined_checked_shape_avoid_of_families
    (iface : Rv.Interface)
    (h_exhaustive :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_refined_edge :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RefinedEdgeCheckedShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.WideRefinedCheckedShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_exhaustive_shape | h_edge_shape
  · exact h_exhaustive raw h_exhaustive_shape h_sail h_not_gap
  · exact h_refined_edge raw h_edge_shape h_sail h_not_gap

theorem wide_refined_checked_shape_rows_of_families
    (iface : Rv.Interface)
    (h_exhaustive :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_refined_edge :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RefinedEdgeCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.WideRefinedCheckedShape := by
  intro raw h_shape h_lowerable
  rcases h_shape with h_exhaustive_shape | h_edge_shape
  · exact h_exhaustive raw h_exhaustive_shape h_lowerable
  · exact h_refined_edge raw h_edge_shape h_lowerable

theorem wide_refined_checked_shape_completeness_of_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_exhaustive_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_refined_edge_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RefinedEdgeCheckedShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_exhaustive_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_refined_edge_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RefinedEdgeCheckedShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    WideRefinedCheckedCompletenessAvoidingKnownBugs iface :=
  shape_family_completeness_of_shape_avoid_and_rows
    iface
    Rv64imShapes.WideRefinedCheckedShape
    (wide_refined_checked_shape_avoid_of_families
      iface
      h_exhaustive_avoid
      h_refined_edge_avoid)
    h_lower
    (wide_refined_checked_shape_rows_of_families
      iface
      h_exhaustive_rows
      h_refined_edge_rows)
    h_opcode

theorem i_type_register_immediate_shape_avoid_of_refined_families
    (iface : Rv.Interface)
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
        Rv64imShapes.LoadRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.ITypeRegisterImmediateShape := by
  intro raw h_shape h_sail h_not_gap
  rcases Rv64imShapes.i_type_register_immediate_shape_cases h_shape with
    h_jalr_shape | h_alu_shape | h_load_shape
  · exact h_jalr raw h_jalr_shape h_sail h_not_gap
  · exact h_alu raw h_alu_shape h_sail h_not_gap
  · exact h_load raw h_load_shape h_sail h_not_gap

theorem jalr_register_edge_immediate_shape_avoid_of_i_type_edge
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.JalrRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jalr_register_edge_immediate_shape_subset_i_type_edge
        h_shape)
    h_avoid

theorem immediate_alu_register_edge_immediate_shape_avoid_of_i_type_edge
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.immediate_alu_register_edge_immediate_shape_subset_i_type_edge
        h_shape)
    h_avoid

theorem load_register_edge_immediate_shape_avoid_of_i_type_edge
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.LoadRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.load_register_edge_immediate_shape_subset_i_type_edge
        h_shape)
    h_avoid

theorem i_type_register_edge_immediate_shape_avoid_of_i_type_register_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.ITypeRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.i_type_register_edge_immediate_shape_subset h_shape)
    h_avoid

theorem jalr_register_edge_immediate_shape_avoid_of_jalr_register_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.JalrRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jalr_register_edge_immediate_shape_subset h_shape)
    h_avoid

theorem immediate_alu_register_edge_immediate_shape_avoid_of_immediate_alu_register_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.immediate_alu_register_edge_immediate_shape_subset h_shape)
    h_avoid

theorem load_register_edge_immediate_shape_avoid_of_load_register_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.LoadRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.LoadRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.load_register_edge_immediate_shape_subset h_shape)
    h_avoid

theorem i_type_register_immediate_shape_rows_of_refined_families
    (iface : Rv.Interface)
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
        Rv64imShapes.LoadRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ITypeRegisterImmediateShape := by
  intro raw h_shape h_lowerable
  rcases Rv64imShapes.i_type_register_immediate_shape_cases h_shape with
    h_jalr_shape | h_alu_shape | h_load_shape
  · exact h_jalr raw h_jalr_shape h_lowerable
  · exact h_alu raw h_alu_shape h_lowerable
  · exact h_load raw h_load_shape h_lowerable

theorem jalr_register_edge_immediate_shape_rows_of_i_type_edge
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.JalrRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jalr_register_edge_immediate_shape_subset_i_type_edge
        h_shape)
    h_rows

theorem immediate_alu_register_edge_immediate_shape_rows_of_i_type_edge
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.immediate_alu_register_edge_immediate_shape_subset_i_type_edge
        h_shape)
    h_rows

theorem load_register_edge_immediate_shape_rows_of_i_type_edge
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.LoadRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.load_register_edge_immediate_shape_subset_i_type_edge
        h_shape)
    h_rows

theorem i_type_register_edge_immediate_shape_rows_of_i_type_register_immediate_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ITypeRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.i_type_register_edge_immediate_shape_subset h_shape)
    h_rows

theorem jalr_register_edge_immediate_shape_rows_of_jalr_register_immediate_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JalrRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.JalrRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jalr_register_edge_immediate_shape_subset h_shape)
    h_rows

theorem immediate_alu_register_edge_immediate_shape_rows_of_immediate_alu_register_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ImmediateAluRegisterShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.immediate_alu_register_edge_immediate_shape_subset h_shape)
    h_rows

theorem load_register_edge_immediate_shape_rows_of_load_register_immediate_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.LoadRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.LoadRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.load_register_edge_immediate_shape_subset h_shape)
    h_rows

theorem upper_and_jump_immediate_shape_avoid_of_refined_families
    (iface : Rv.Interface)
    (h_upper :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.UpperAndJumpImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_or iface h_upper h_jump

theorem upper_register_immediate_shape_avoid_of_upper_and_jump
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperAndJumpImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.UpperRegisterImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape => Or.inl h_shape)
    h_avoid

theorem jump_register_immediate_shape_avoid_of_upper_and_jump
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperAndJumpImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.JumpRegisterImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape => Or.inr h_shape)
    h_avoid

theorem upper_register_edge_immediate_shape_avoid_of_upper_and_jump_edge
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.UpperRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.upper_register_edge_immediate_shape_subset_upper_and_jump_edge
        h_shape)
    h_avoid

theorem jump_register_edge_immediate_shape_avoid_of_upper_and_jump_edge
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.JumpRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jump_register_edge_immediate_shape_subset_upper_and_jump_edge
        h_shape)
    h_avoid

theorem store_register_edge_immediate_shape_avoid_of_store_register_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.StoreRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.StoreRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.store_register_edge_immediate_shape_subset h_shape)
    h_avoid

theorem branch_register_edge_immediate_shape_avoid_of_branch_register_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.BranchRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.branch_register_edge_immediate_shape_subset h_shape)
    h_avoid

theorem upper_and_jump_edge_immediate_shape_avoid_of_upper_and_jump_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperAndJumpImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.UpperAndJumpEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.upper_and_jump_edge_immediate_shape_subset h_shape)
    h_avoid

theorem upper_register_edge_immediate_shape_avoid_of_upper_register_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.UpperRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.upper_register_edge_immediate_shape_subset h_shape)
    h_avoid

theorem jump_register_edge_immediate_shape_avoid_of_jump_register_immediate_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.JumpRegisterEdgeImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jump_register_edge_immediate_shape_subset h_shape)
    h_avoid

theorem upper_and_jump_immediate_shape_rows_of_refined_families
    (iface : Rv.Interface)
    (h_upper :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.UpperAndJumpImmediateShape :=
  Rv.Interface.shape_row_materialization_or iface h_upper h_jump

theorem upper_register_immediate_shape_rows_of_upper_and_jump
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.UpperRegisterImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape => Or.inl h_shape)
    h_rows

theorem jump_register_immediate_shape_rows_of_upper_and_jump
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.JumpRegisterImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape => Or.inr h_shape)
    h_rows

theorem upper_register_edge_immediate_shape_rows_of_upper_and_jump_edge
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.UpperRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.upper_register_edge_immediate_shape_subset_upper_and_jump_edge
        h_shape)
    h_rows

theorem jump_register_edge_immediate_shape_rows_of_upper_and_jump_edge
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.JumpRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jump_register_edge_immediate_shape_subset_upper_and_jump_edge
        h_shape)
    h_rows

theorem store_register_edge_immediate_shape_rows_of_store_register_immediate_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.StoreRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.store_register_edge_immediate_shape_subset h_shape)
    h_rows

theorem branch_register_edge_immediate_shape_rows_of_branch_register_immediate_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.BranchRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.branch_register_edge_immediate_shape_subset h_shape)
    h_rows

theorem upper_and_jump_edge_immediate_shape_rows_of_upper_and_jump_immediate_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.UpperAndJumpEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.upper_and_jump_edge_immediate_shape_subset h_shape)
    h_rows

theorem upper_register_edge_immediate_shape_rows_of_upper_register_immediate_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.UpperRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.upper_register_edge_immediate_shape_subset h_shape)
    h_rows

theorem jump_register_edge_immediate_shape_rows_of_jump_register_immediate_shape
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.JumpRegisterImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.JumpRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jump_register_edge_immediate_shape_subset h_shape)
    h_rows

end ZiskFv.Completeness.Rv64im
