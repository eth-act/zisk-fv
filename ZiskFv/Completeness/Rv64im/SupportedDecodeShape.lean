import ZiskFv.Completeness.Rv64im.CheckedShapeFamilies

/- ⚠ ASPIRATIONAL / QUARANTINED — not wired to any live completeness endpoint.
   Abstract `Rv.Interface`-parametrized route; no concrete `Interface` is ever
   built, and the live endpoints in `ZiskFv.Completeness`
   (`root_completeness_sail`, `eventual_zisk_coverage`, `eventual_root_completeness`)
   do not depend on it. Intended *eventual* composition machinery for when the
   Aeneas-extracted ZisK coverage proofs can be imported into this build. Kept
   compiling via `ZiskFv.lean` for preservation only.
   See `ZiskFv/Completeness/Rv64im/ASPIRATIONAL.md`. -/

/-!
# RV64IM completeness — supported-decode and memory-refined supported-decode shape completeness/rows/avoid

Theorem cluster split verbatim out of `ZiskFv/Completeness/Rv64im.lean`.
-/

namespace ZiskFv.Completeness.Rv64im

open ZiskFv.Completeness

theorem supported_decode_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.SupportedDecodeShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.SupportedDecodeShape
    h_complete

theorem memory_refined_supported_decode_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape
    h_complete

theorem supported_decode_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.SupportedDecodeShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.SupportedDecodeShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem memory_refined_supported_decode_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.MemoryRefinedSupportedDecodeShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem supported_decode_shape_completeness_of_row_gap
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows : Rv.Interface.RowMaterializationCompleteAvoidingKnownBugs iface)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    SupportedDecodeCompletenessAvoidingKnownBugs iface :=
  shape_family_completeness_of_row_gap
    iface
    Rv64imShapes.SupportedDecodeShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem memory_refined_supported_decode_shape_completeness_of_row_gap
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows : Rv.Interface.RowMaterializationCompleteAvoidingKnownBugs iface)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface :=
  shape_family_completeness_of_row_gap
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem memory_refined_supported_decode_shape_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.memory_refined_supported_decode_shape_subset_supported_decode
        h_shape)
    h_complete

theorem supported_decode_shape_completeness_of_memory_refined_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete : MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface) :
    SupportedDecodeCompletenessAvoidingKnownBugs iface :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.supported_decode_shape_subset_memory_refined_supported_decode_shape
        h_shape)
    h_complete

theorem supported_decode_shape_completeness_of_shape_avoid_and_rows
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    SupportedDecodeCompletenessAvoidingKnownBugs iface :=
  shape_family_completeness_of_shape_avoid_and_rows
    iface
    Rv64imShapes.SupportedDecodeShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem memory_refined_supported_decode_shape_completeness_of_shape_avoid_and_rows
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.MemoryRefinedSupportedDecodeShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.MemoryRefinedSupportedDecodeShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface :=
  shape_family_completeness_of_shape_avoid_and_rows
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem wide_checked_shape_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_supported :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.WideCheckedShape := by
  intro raw h_wide h_sail h_not_gap
  exact h_supported raw
    (Rv64imShapes.wide_checked_shape_subset_supported_decode h_wide)
    h_sail
    h_not_gap

theorem exhaustive_checked_shape_completeness_of_memory_refined_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete : MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ExhaustiveCheckedShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.exhaustive_checked_shape_subset_memory_refined_supported_decode
        h_shape)
    h_complete

theorem edge_checked_shape_completeness_of_memory_refined_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete : MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.EdgeCheckedShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.edge_checked_shape_subset_memory_refined_supported_decode
        h_shape)
    h_complete

theorem refined_edge_checked_shape_completeness_of_memory_refined_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete : MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.RefinedEdgeCheckedShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.refined_edge_checked_shape_subset_memory_refined_supported_decode
        h_shape)
    h_complete

theorem wide_checked_shape_completeness_of_memory_refined_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete : MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.WideCheckedShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.wide_checked_shape_subset_memory_refined_supported_decode
        h_shape)
    h_complete

theorem wide_refined_checked_shape_completeness_of_memory_refined_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete : MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.WideRefinedCheckedShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.wide_refined_checked_shape_subset_memory_refined_supported_decode
        h_shape)
    h_complete

theorem r_type_register_shape_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.RTypeRegisterShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inl h_shape)
    h_complete

theorem i_type_register_immediate_shape_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ITypeRegisterImmediateShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inl h_shape))
    h_complete

theorem shift_register_shape_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ShiftRegisterShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inl h_shape)))
    h_complete

theorem store_register_immediate_shape_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.StoreRegisterImmediateShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inl h_shape))))
    h_complete

theorem branch_register_immediate_shape_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.BranchRegisterImmediateShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_shape)))))
    h_complete

theorem upper_and_jump_immediate_shape_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperAndJumpImmediateShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_shape))))))
    h_complete

theorem supported_fence_pred_succ_shape_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.SupportedFencePredSuccShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_shape))))))
    h_complete

theorem r_type_register_shape_completeness_of_exhaustive_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ExhaustiveCheckedShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.RTypeRegisterShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inl h_shape)
    h_complete

theorem shift_register_shape_completeness_of_exhaustive_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ExhaustiveCheckedShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ShiftRegisterShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inl h_shape))
    h_complete

theorem supported_fence_pred_succ_shape_completeness_of_exhaustive_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ExhaustiveCheckedShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.SupportedFencePredSuccShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inr h_shape))
    h_complete

theorem i_type_register_edge_immediate_shape_completeness_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ITypeRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inl h_shape)
    h_complete

theorem store_register_edge_immediate_shape_completeness_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.StoreRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inl h_shape))
    h_complete

theorem branch_register_edge_immediate_shape_completeness_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.BranchRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inl h_shape)))
    h_complete

theorem upper_and_jump_edge_immediate_shape_completeness_of_edge_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperAndJumpEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr h_shape)))
    h_complete

theorem exhaustive_checked_shape_completeness_of_wide_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.WideCheckedShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ExhaustiveCheckedShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inl h_shape)
    h_complete

theorem edge_checked_shape_completeness_of_wide_checked_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.WideCheckedShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.EdgeCheckedShape :=
  Rv.Interface.shape_completeness_mono iface
    (fun _ h_shape => Or.inr h_shape)
    h_complete

theorem r_type_register_shape_rows_of_exhaustive_checked_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ExhaustiveCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.RTypeRegisterShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inl h_shape)
    h_rows

theorem shift_register_shape_rows_of_exhaustive_checked_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ExhaustiveCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ShiftRegisterShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inl h_shape))
    h_rows

theorem supported_fence_pred_succ_shape_rows_of_exhaustive_checked_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ExhaustiveCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.SupportedFencePredSuccShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inr h_shape))
    h_rows

theorem i_type_register_edge_immediate_shape_rows_of_edge_checked_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ITypeRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inl h_shape)
    h_rows

theorem store_register_edge_immediate_shape_rows_of_edge_checked_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.StoreRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inl h_shape))
    h_rows

theorem branch_register_edge_immediate_shape_rows_of_edge_checked_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.BranchRegisterEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inl h_shape)))
    h_rows

theorem upper_and_jump_edge_immediate_shape_rows_of_edge_checked_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.UpperAndJumpEdgeImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr h_shape)))
    h_rows

theorem exhaustive_checked_shape_rows_of_wide_checked_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.WideCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ExhaustiveCheckedShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inl h_shape)
    h_rows

theorem edge_checked_shape_rows_of_wide_checked_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.WideCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.EdgeCheckedShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr h_shape)
    h_rows

theorem r_type_register_shape_rows_of_supported_decode_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.RTypeRegisterShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inl h_shape)
    h_rows

theorem i_type_register_immediate_shape_rows_of_supported_decode_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ITypeRegisterImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inl h_shape))
    h_rows

theorem shift_register_shape_rows_of_supported_decode_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ShiftRegisterShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inl h_shape)))
    h_rows

theorem store_register_immediate_shape_rows_of_supported_decode_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.StoreRegisterImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inl h_shape))))
    h_rows

theorem branch_register_immediate_shape_rows_of_supported_decode_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.BranchRegisterImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_shape)))))
    h_rows

theorem upper_and_jump_immediate_shape_rows_of_supported_decode_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.UpperAndJumpImmediateShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_shape))))))
    h_rows

theorem supported_fence_pred_succ_shape_rows_of_supported_decode_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.SupportedFencePredSuccShape :=
  Rv.Interface.shape_row_materialization_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_shape))))))
    h_rows

theorem memory_refined_supported_decode_shape_rows_of_supported_decode_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.MemoryRefinedSupportedDecodeShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.memory_refined_supported_decode_shape_subset_supported_decode
        h_shape)
    h_rows

theorem supported_decode_shape_rows_of_memory_refined_supported_decode_shape_rows
    (iface : Rv.Interface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.MemoryRefinedSupportedDecodeShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.SupportedDecodeShape :=
  Rv.Interface.shape_row_materialization_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.supported_decode_shape_subset_memory_refined_supported_decode_shape
        h_shape)
    h_rows

theorem exhaustive_checked_shape_completeness_of_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_shift :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_fence :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ExhaustiveCheckedShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_shape | h_shape | h_shape
  · exact h_r raw h_shape h_sail h_not_gap
  · exact h_shift raw h_shape h_sail h_not_gap
  · exact h_fence raw h_shape h_sail h_not_gap

theorem edge_checked_shape_completeness_of_families
    (iface : Rv.Interface)
    (h_i :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape)
    (h_store :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper_jump :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.EdgeCheckedShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_shape | h_shape | h_shape | h_shape
  · exact h_i raw h_shape h_sail h_not_gap
  · exact h_store raw h_shape h_sail h_not_gap
  · exact h_branch raw h_shape h_sail h_not_gap
  · exact h_upper_jump raw h_shape h_sail h_not_gap

theorem wide_checked_shape_completeness_of_families
    (iface : Rv.Interface)
    (h_exhaustive :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_edge :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.WideCheckedShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_exhaustive_shape | h_edge_shape
  · exact h_exhaustive raw h_exhaustive_shape h_sail h_not_gap
  · exact h_edge raw h_edge_shape h_sail h_not_gap

theorem supported_decode_shape_completeness_of_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_i :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape)
    (h_shift :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_store :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.StoreRegisterImmediateShape)
    (h_branch :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_upper_jump :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperAndJumpImmediateShape)
    (h_fence :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.SupportedDecodeShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with
    h_shape | h_shape | h_shape | h_shape | h_shape | h_shape | h_shape
  · exact h_r raw h_shape h_sail h_not_gap
  · exact h_i raw h_shape h_sail h_not_gap
  · exact h_shift raw h_shape h_sail h_not_gap
  · exact h_store raw h_shape h_sail h_not_gap
  · exact h_branch raw h_shape h_sail h_not_gap
  · exact h_upper_jump raw h_shape h_sail h_not_gap
  · exact h_fence raw h_shape h_sail h_not_gap

theorem exhaustive_checked_shape_rows_of_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_shift :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_fence :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.ExhaustiveCheckedShape := by
  intro raw h_shape h_lowerable
  rcases h_shape with h_shape | h_shape | h_shape
  · exact h_r raw h_shape h_lowerable
  · exact h_shift raw h_shape h_lowerable
  · exact h_fence raw h_shape h_lowerable

theorem edge_checked_shape_rows_of_families
    (iface : Rv.Interface)
    (h_i :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape)
    (h_store :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper_jump :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.EdgeCheckedShape := by
  intro raw h_shape h_lowerable
  rcases h_shape with h_shape | h_shape | h_shape | h_shape
  · exact h_i raw h_shape h_lowerable
  · exact h_store raw h_shape h_lowerable
  · exact h_branch raw h_shape h_lowerable
  · exact h_upper_jump raw h_shape h_lowerable

theorem wide_checked_shape_rows_of_families
    (iface : Rv.Interface)
    (h_exhaustive :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_edge :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.WideCheckedShape := by
  intro raw h_shape h_lowerable
  rcases h_shape with h_exhaustive_shape | h_edge_shape
  · exact h_exhaustive raw h_exhaustive_shape h_lowerable
  · exact h_edge raw h_edge_shape h_lowerable

theorem supported_decode_shape_rows_of_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_i :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterImmediateShape)
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
    (h_upper_jump :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpImmediateShape)
    (h_fence :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeRowMaterializationComplete
      iface
      Rv64imShapes.SupportedDecodeShape := by
  intro raw h_shape h_lowerable
  rcases h_shape with
    h_shape | h_shape | h_shape | h_shape | h_shape | h_shape | h_shape
  · exact h_r raw h_shape h_lowerable
  · exact h_i raw h_shape h_lowerable
  · exact h_shift raw h_shape h_lowerable
  · exact h_store raw h_shape h_lowerable
  · exact h_branch raw h_shape h_lowerable
  · exact h_upper_jump raw h_shape h_lowerable
  · exact h_fence raw h_shape h_lowerable

theorem r_type_register_shape_avoid_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.RTypeRegisterShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape => Or.inl h_shape)
    h_avoid

theorem i_type_register_immediate_shape_avoid_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.ITypeRegisterImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape => Or.inr (Or.inl h_shape))
    h_avoid

theorem shift_register_shape_avoid_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.ShiftRegisterShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inl h_shape)))
    h_avoid

theorem store_register_immediate_shape_avoid_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.StoreRegisterImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inl h_shape))))
    h_avoid

theorem branch_register_immediate_shape_avoid_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.BranchRegisterImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_shape)))))
    h_avoid

theorem upper_and_jump_immediate_shape_avoid_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.UpperAndJumpImmediateShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_shape))))))
    h_avoid

theorem supported_fence_pred_succ_shape_avoid_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.SupportedFencePredSuccShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_shape))))))
    h_avoid

theorem memory_refined_supported_decode_shape_avoid_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.MemoryRefinedSupportedDecodeShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.memory_refined_supported_decode_shape_subset_supported_decode
        h_shape)
    h_avoid

theorem supported_decode_shape_avoid_of_memory_refined_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.MemoryRefinedSupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.SupportedDecodeShape :=
  Rv.Interface.shape_avoid_known_bugs_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.supported_decode_shape_subset_memory_refined_supported_decode_shape
        h_shape)
    h_avoid

theorem wide_checked_shape_avoid_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.WideCheckedShape :=
  Rv.Interface.shape_avoid_known_bugs_mono iface
    (fun _ h_shape =>
      Rv64imShapes.wide_checked_shape_subset_supported_decode h_shape)
    h_avoid

theorem exhaustive_checked_shape_avoid_of_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_shift :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_fence :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.ExhaustiveCheckedShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_shape | h_shape | h_shape
  · exact h_r raw h_shape h_sail h_not_gap
  · exact h_shift raw h_shape h_sail h_not_gap
  · exact h_fence raw h_shape h_sail h_not_gap

theorem edge_checked_shape_avoid_of_families
    (iface : Rv.Interface)
    (h_i :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape)
    (h_store :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper_jump :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.EdgeCheckedShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_shape | h_shape | h_shape | h_shape
  · exact h_i raw h_shape h_sail h_not_gap
  · exact h_store raw h_shape h_sail h_not_gap
  · exact h_branch raw h_shape h_sail h_not_gap
  · exact h_upper_jump raw h_shape h_sail h_not_gap

theorem wide_checked_shape_avoid_of_families
    (iface : Rv.Interface)
    (h_exhaustive :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_edge :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.EdgeCheckedShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.WideCheckedShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_exhaustive_shape | h_edge_shape
  · exact h_exhaustive raw h_exhaustive_shape h_sail h_not_gap
  · exact h_edge raw h_edge_shape h_sail h_not_gap

theorem supported_decode_shape_avoid_of_families
    (iface : Rv.Interface)
    (h_r :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_i :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape)
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
    (h_upper_jump :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperAndJumpImmediateShape)
    (h_fence :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape) :
    Rv.Interface.ShapeAvoidKnownBugs
      iface
      Rv64imShapes.SupportedDecodeShape := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with
    h_shape | h_shape | h_shape | h_shape | h_shape | h_shape | h_shape
  · exact h_r raw h_shape h_sail h_not_gap
  · exact h_i raw h_shape h_sail h_not_gap
  · exact h_shift raw h_shape h_sail h_not_gap
  · exact h_store raw h_shape h_sail h_not_gap
  · exact h_branch raw h_shape h_sail h_not_gap
  · exact h_upper_jump raw h_shape h_sail h_not_gap
  · exact h_fence raw h_shape h_sail h_not_gap

theorem exhaustive_checked_shape_completeness_of_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_r_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_shift_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_fence_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_r_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_shift_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_fence_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ExhaustiveCheckedShape :=
  shape_family_completeness_of_shape_avoid_and_rows
    iface
    Rv64imShapes.ExhaustiveCheckedShape
    (exhaustive_checked_shape_avoid_of_families
      iface
      h_r_avoid
      h_shift_avoid
      h_fence_avoid)
    h_lower
    (exhaustive_checked_shape_rows_of_families
      iface
      h_r_rows
      h_shift_rows
      h_fence_rows)
    h_opcode

theorem edge_checked_shape_completeness_of_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_i_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape)
    (h_store_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper_jump_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_i_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape)
    (h_store_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_branch_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_upper_jump_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.EdgeCheckedShape :=
  shape_family_completeness_of_shape_avoid_and_rows
    iface
    Rv64imShapes.EdgeCheckedShape
    (edge_checked_shape_avoid_of_families
      iface
      h_i_avoid
      h_store_avoid
      h_branch_avoid
      h_upper_jump_avoid)
    h_lower
    (edge_checked_shape_rows_of_families
      iface
      h_i_rows
      h_store_rows
      h_branch_rows
      h_upper_jump_rows)
    h_opcode

theorem wide_checked_shape_completeness_of_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_exhaustive_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_edge_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.EdgeCheckedShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_exhaustive_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ExhaustiveCheckedShape)
    (h_edge_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.EdgeCheckedShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.WideCheckedShape :=
  shape_family_completeness_of_shape_avoid_and_rows
    iface
    Rv64imShapes.WideCheckedShape
    (wide_checked_shape_avoid_of_families
      iface
      h_exhaustive_avoid
      h_edge_avoid)
    h_lower
    (wide_checked_shape_rows_of_families
      iface
      h_exhaustive_rows
      h_edge_rows)
    h_opcode

theorem supported_decode_shape_completeness_of_family_avoid_and_rows
    (iface : Rv.Interface)
    (h_r_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_i_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape)
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
    (h_upper_jump_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.UpperAndJumpImmediateShape)
    (h_fence_avoid :
      Rv.Interface.ShapeAvoidKnownBugs
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_r_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_i_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterImmediateShape)
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
    (h_upper_jump_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpImmediateShape)
    (h_fence_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    SupportedDecodeCompletenessAvoidingKnownBugs iface :=
  supported_decode_shape_completeness_of_shape_avoid_and_rows
    iface
    (supported_decode_shape_avoid_of_families
      iface
      h_r_avoid
      h_i_avoid
      h_shift_avoid
      h_store_avoid
      h_branch_avoid
      h_upper_jump_avoid
      h_fence_avoid)
    h_lower
    (supported_decode_shape_rows_of_families
      iface
      h_r_rows
      h_i_rows
      h_shift_rows
      h_store_rows
      h_branch_rows
      h_upper_jump_rows
      h_fence_rows)
    h_opcode

end ZiskFv.Completeness.Rv64im
