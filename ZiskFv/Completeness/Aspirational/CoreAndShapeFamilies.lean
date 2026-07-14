import ZiskFv.Completeness.Aspirational.Defs

/- ⚠ ASPIRATIONAL / QUARANTINED — not wired to any live completeness endpoint.
   Abstract `Rv.Interface`-parametrized route; no concrete `Interface` is ever
   built, and the live endpoints in `ZiskFv.Completeness`
   (`sail_executable_within_supported_decode_shape`, `root_completeness`)
   do not depend on it. Intended *eventual* composition machinery for when the
   Aeneas-extracted ZisK coverage proofs can be imported into this build. Kept
   compiling via `ZiskFv.lean` for preservation only.
   See `ZiskFv/Completeness/Aspirational/README.md`. -/

/-!
# RV64IM completeness — core forwarding lemmas and per-family shape completeness

Theorem cluster split verbatim out of `ZiskFv/Completeness/Rv64im.lean`.
-/

namespace ZiskFv.Completeness.Rv64im

open ZiskFv.Completeness

theorem shape_family_completeness_of_shape_rows
    (iface : Rv.Interface)
    (shape : RawInstruction → Prop)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows : Rv.Interface.ShapeRowMaterializationComplete iface shape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs iface shape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs_of_shape_rows
    iface
    shape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem shape_family_completeness_of_shape_avoid_and_rows
    (iface : Rv.Interface)
    (shape : RawInstruction → Prop)
    (h_avoid : Rv.Interface.ShapeAvoidKnownBugs iface shape)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows : Rv.Interface.ShapeRowMaterializationComplete iface shape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs iface shape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs_of_shape_avoid_and_rows
    iface
    shape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem shape_family_completeness_of_circuit_covered_known_good
    (iface : Rv.Interface)
    (shape : RawInstruction → Prop)
    (h_covered :
      Rv.Interface.ShapeCircuitCoveredKnownGood iface shape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs iface shape :=
  Rv.Interface.shape_completeness_of_circuit_covered_known_good
    iface
    shape
    h_covered

theorem rv64im_completeness_of_supported_decode_shape
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInSupportedDecode iface)
    (h_supported : SupportedDecodeCompletenessAvoidingKnownBugs iface) :
    Rv64imCompletenessAvoidingKnownBugs iface :=
  Rv.Interface.completeness_of_shape_completeness
    iface
    Rv64imShapes.SupportedDecodeShape
    h_sail_subset
    h_supported

theorem rv64im_completeness_of_supported_decode_circuit_covered_known_good
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInSupportedDecode iface)
    (h_covered :
      Rv.Interface.ShapeCircuitCoveredKnownGood
        iface
        Rv64imShapes.SupportedDecodeShape) :
    Rv64imCompletenessAvoidingKnownBugs iface :=
  Rv.Interface.completeness_of_circuit_covered_known_good
    iface
    Rv64imShapes.SupportedDecodeShape
    h_sail_subset
    h_covered

/-- Acceptance-focused RV64IM completeness target.

This theorem is the checked-in counterpart of the generated
`rv_completeness_avoiding_known_decode_bugs` Aeneas theorem: Sail is the source
of truth for the raw instruction domain, the only excluded raw words are known
decode gaps, and row materialization is a ZisK-side universal obligation rather
than a way to narrow the Sail acceptance set. -/
theorem rv64im_completeness_of_supported_decode_avoid_known_decode_bugs
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInSupportedDecode iface)
    (h_supported : SupportedDecodeAvoidKnownDecodeBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows : Rv.Interface.RowMaterializationComplete iface)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv64imCompletenessAvoidingKnownDecodeBugs iface :=
  Rv.Interface.completeness_avoiding_known_decode_bugs
    iface
    Rv64imShapes.SupportedDecodeShape
    h_sail_subset
    h_supported
    h_lower
    h_rows
    h_opcode

theorem rv64im_completeness_of_memory_refined_supported_decode_shape
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInMemoryRefinedSupportedDecode iface)
    (h_supported :
      MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs iface) :
    Rv64imCompletenessAvoidingKnownBugs iface :=
  Rv.Interface.completeness_of_shape_completeness
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape
    h_sail_subset
    h_supported

theorem sail_executable_contained_in_supported_decode_of_memory_refined
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInMemoryRefinedSupportedDecode iface) :
    SailExecutableContainedInSupportedDecode iface :=
  Rv.Interface.sail_executable_contained_in_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.memory_refined_supported_decode_shape_subset_supported_decode
        h_shape)
    h_sail_subset

theorem rv64im_completeness_of_memory_refined_supported_decode_circuit_covered_known_good
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInMemoryRefinedSupportedDecode iface)
    (h_covered : MemoryRefinedSupportedDecodeCircuitCoveredKnownGood iface) :
    Rv64imCompletenessAvoidingKnownBugs iface :=
  Rv.Interface.completeness_of_circuit_covered_known_good
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape
    h_sail_subset
    h_covered

theorem shape_family_completeness_of_row_gap
    (iface : Rv.Interface)
    (shape : RawInstruction → Prop)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows : Rv.Interface.RowMaterializationCompleteAvoidingKnownBugs iface)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs iface shape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs_of_row_gap
    iface
    shape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem r_type_register_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.RTypeRegisterShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.RTypeRegisterShape
    h_complete

theorem r_type_register_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.RTypeRegisterShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.RTypeRegisterShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.RTypeRegisterShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem i_type_register_edge_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ITypeRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.ITypeRegisterEdgeImmediateShape
    h_complete

theorem i_type_register_edge_immediate_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ITypeRegisterEdgeImmediateShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.ITypeRegisterEdgeImmediateShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem i_type_register_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ITypeRegisterImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.ITypeRegisterImmediateShape
    h_complete

theorem i_type_register_immediate_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ITypeRegisterImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ITypeRegisterImmediateShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.ITypeRegisterImmediateShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem jalr_register_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.JalrRegisterImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.JalrRegisterImmediateShape
    h_complete

theorem jalr_register_immediate_shape_completeness_of_i_type
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.JalrRegisterImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jalr_register_immediate_shape_subset h_shape)
    h_complete

theorem immediate_alu_register_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ImmediateAluRegisterShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.ImmediateAluRegisterShape
    h_complete

theorem immediate_alu_register_shape_completeness_of_i_type
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ImmediateAluRegisterShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.immediate_alu_register_shape_subset h_shape)
    h_complete

theorem i_type_register_immediate_shape_completeness_of_families
    (iface : Rv.Interface)
    (h_jalr :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape)
    (h_alu :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape)
    (h_load :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.LoadRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ITypeRegisterImmediateShape := by
  intro raw h_shape h_sail h_not_gap
  rcases Rv64imShapes.i_type_register_immediate_shape_cases h_shape with
    h_jalr_shape | h_alu_shape | h_load_shape
  · exact h_jalr raw h_jalr_shape h_sail h_not_gap
  · exact h_alu raw h_alu_shape h_sail h_not_gap
  · exact h_load raw h_load_shape h_sail h_not_gap

theorem jalr_register_edge_immediate_shape_completeness_of_i_type_edge
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.JalrRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jalr_register_edge_immediate_shape_subset_i_type_edge
        h_shape)
    h_complete

theorem immediate_alu_register_edge_immediate_shape_completeness_of_i_type_edge
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.immediate_alu_register_edge_immediate_shape_subset_i_type_edge
        h_shape)
    h_complete

theorem load_register_edge_immediate_shape_completeness_of_i_type_edge
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ITypeRegisterEdgeImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.LoadRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.load_register_edge_immediate_shape_subset_i_type_edge
        h_shape)
    h_complete

theorem i_type_register_edge_immediate_shape_completeness_of_i_type_register_immediate_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ITypeRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ITypeRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.i_type_register_edge_immediate_shape_subset h_shape)
    h_complete

theorem jalr_register_edge_immediate_shape_completeness_of_jalr_register_immediate_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.JalrRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.JalrRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jalr_register_edge_immediate_shape_subset h_shape)
    h_complete

theorem immediate_alu_register_edge_immediate_shape_completeness_of_immediate_alu_register_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.ImmediateAluRegisterShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ImmediateAluRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.immediate_alu_register_edge_immediate_shape_subset h_shape)
    h_complete

theorem load_register_edge_immediate_shape_completeness_of_load_register_immediate_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.LoadRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.LoadRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.load_register_edge_immediate_shape_subset h_shape)
    h_complete

theorem shift_register_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ShiftRegisterShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.ShiftRegisterShape
    h_complete

theorem shift_register_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.ShiftRegisterShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.ShiftRegisterShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.ShiftRegisterShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem store_register_edge_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.StoreRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.StoreRegisterEdgeImmediateShape
    h_complete

theorem store_register_edge_immediate_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterEdgeImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.StoreRegisterEdgeImmediateShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.StoreRegisterEdgeImmediateShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem store_register_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.StoreRegisterImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.StoreRegisterImmediateShape
    h_complete

theorem store_register_immediate_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.StoreRegisterImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.StoreRegisterImmediateShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.StoreRegisterImmediateShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem store_register_edge_immediate_shape_completeness_of_store_register_immediate_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.StoreRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.StoreRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.store_register_edge_immediate_shape_subset h_shape)
    h_complete

theorem branch_register_edge_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.BranchRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.BranchRegisterEdgeImmediateShape
    h_complete

theorem branch_register_edge_immediate_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterEdgeImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.BranchRegisterEdgeImmediateShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.BranchRegisterEdgeImmediateShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem branch_register_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.BranchRegisterImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.BranchRegisterImmediateShape
    h_complete

theorem branch_register_immediate_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.BranchRegisterImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.BranchRegisterImmediateShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.BranchRegisterImmediateShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem branch_register_edge_immediate_shape_completeness_of_branch_register_immediate_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.BranchRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.BranchRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.branch_register_edge_immediate_shape_subset h_shape)
    h_complete

theorem upper_and_jump_edge_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperAndJumpEdgeImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.UpperAndJumpEdgeImmediateShape
    h_complete

theorem upper_and_jump_edge_immediate_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperAndJumpEdgeImmediateShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.UpperAndJumpEdgeImmediateShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem upper_and_jump_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperAndJumpImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.UpperAndJumpImmediateShape
    h_complete

theorem upper_and_jump_immediate_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.UpperAndJumpImmediateShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperAndJumpImmediateShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.UpperAndJumpImmediateShape
    h_avoid
    h_lower
    h_rows
    h_opcode

theorem upper_register_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperRegisterImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.UpperRegisterImmediateShape
    h_complete

theorem upper_register_immediate_shape_completeness_of_upper_and_jump
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperAndJumpImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperRegisterImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape => Or.inl h_shape)
    h_complete

theorem jump_register_immediate_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.JumpRegisterImmediateShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.JumpRegisterImmediateShape
    h_complete

theorem jump_register_immediate_shape_completeness_of_upper_and_jump
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperAndJumpImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.JumpRegisterImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape => Or.inr h_shape)
    h_complete

theorem upper_and_jump_immediate_shape_completeness_of_families
    (iface : Rv.Interface)
    (h_upper :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape)
    (h_jump :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperAndJumpImmediateShape :=
  Rv.Interface.shape_completeness_or iface h_upper h_jump

theorem upper_register_edge_immediate_shape_completeness_of_upper_and_jump_edge
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.upper_register_edge_immediate_shape_subset_upper_and_jump_edge
        h_shape)
    h_complete

theorem jump_register_edge_immediate_shape_completeness_of_upper_and_jump_edge
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperAndJumpEdgeImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.JumpRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jump_register_edge_immediate_shape_subset_upper_and_jump_edge
        h_shape)
    h_complete

theorem upper_and_jump_edge_immediate_shape_completeness_of_upper_and_jump_immediate_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperAndJumpImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperAndJumpEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.upper_and_jump_edge_immediate_shape_subset h_shape)
    h_complete

theorem upper_register_edge_immediate_shape_completeness_of_upper_register_immediate_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.UpperRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.UpperRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.upper_register_edge_immediate_shape_subset h_shape)
    h_complete

theorem jump_register_edge_immediate_shape_completeness_of_jump_register_immediate_shape
    (iface : Rv.Interface)
    (h_complete :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.JumpRegisterImmediateShape) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.JumpRegisterEdgeImmediateShape :=
  Rv.Interface.shape_completeness_mono
    iface
    (fun _raw h_shape =>
      Rv64imShapes.jump_register_edge_immediate_shape_subset h_shape)
    h_complete

theorem supported_decode_shape_completeness_of_refined_families
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
    (h_load :
      Rv.Interface.ShapeCompletenessAvoidingKnownBugs
        iface
        Rv64imShapes.LoadRegisterImmediateShape)
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
  · exact
      (i_type_register_immediate_shape_completeness_of_families
        iface h_jalr h_alu h_load) raw h_i_shape h_sail h_not_gap
  · exact h_shift raw h_shift_shape h_sail h_not_gap
  · exact h_store raw h_store_shape h_sail h_not_gap
  · exact h_branch raw h_branch_shape h_sail h_not_gap
  · exact
      (upper_and_jump_immediate_shape_completeness_of_families
        iface h_upper h_jump) raw h_upper_jump_shape h_sail h_not_gap
  · exact h_fence raw h_fence_shape h_sail h_not_gap

theorem supported_fence_pred_succ_shape_completeness
    (iface : Rv.Interface)
    (h_complete : Rv.Interface.CompletenessAvoidingKnownBugs iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.SupportedFencePredSuccShape :=
  Rv.Interface.shape_completeness_avoiding_known_bugs
    iface
    Rv64imShapes.SupportedFencePredSuccShape
    h_complete

theorem supported_fence_pred_succ_shape_completeness_of_shape_rows
    (iface : Rv.Interface)
    (h_avoid : Rv.Interface.AvoidKnownBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows :
      Rv.Interface.ShapeRowMaterializationComplete
        iface
        Rv64imShapes.SupportedFencePredSuccShape)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface) :
    Rv.Interface.ShapeCompletenessAvoidingKnownBugs
      iface
      Rv64imShapes.SupportedFencePredSuccShape :=
  shape_family_completeness_of_shape_rows
    iface
    Rv64imShapes.SupportedFencePredSuccShape
    h_avoid
    h_lower
    h_rows
    h_opcode

end ZiskFv.Completeness.Rv64im
