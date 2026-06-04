import ZiskFv.Completeness.Rv64imShapes

/-!
# RV64IM shape-family completeness

This module states the checked-in theorem surface for the RV64IM raw-shape
families exercised by the generated Aeneas production-transpiler harness.

The concrete generated predicates live outside the repository in the
reproducible extraction workspace. Here we keep the shape-family closure
statements in the normal Lean build. The main RV target is the
`SupportedDecodeShape`: every Sail-executable instruction in that decoded
RV64IM surface should be circuit-covered, except for explicitly recorded ZisK
gaps.
-/

namespace ZiskFv.Completeness.Rv64im

open ZiskFv.Completeness

abbrev RawInstruction := Rv.RawInstruction

def SupportedDecodeCompletenessAvoidingKnownBugs
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCompletenessAvoidingKnownBugs
    iface
    Rv64imShapes.SupportedDecodeShape

/-- Sail decoder bridge needed for the global RV64IM completeness target:
every Sail-executable raw word belongs to the RV64IM supported-decode surface
modeled in this module. This is intentionally separate from the ZisK-side
Aeneas obligations. -/
def SailExecutableContainedInSupportedDecode
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.SailExecutableContainedIn
    iface
    Rv64imShapes.SupportedDecodeShape

def Rv64imCompletenessAvoidingKnownBugs
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.CompletenessAvoidingKnownBugs iface

def MemoryRefinedSupportedDecodeCompletenessAvoidingKnownBugs
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCompletenessAvoidingKnownBugs
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape

def SailExecutableContainedInMemoryRefinedSupportedDecode
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.SailExecutableContainedIn
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape

def ExhaustiveCheckedCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.ExhaustiveCheckedShape

def EdgeCheckedCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.EdgeCheckedShape

def RefinedEdgeCheckedCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.RefinedEdgeCheckedShape

def WideCheckedCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.WideCheckedShape

def WideRefinedCheckedCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.WideRefinedCheckedShape

def RTypeRegisterCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.RTypeRegisterShape

def JalrRegisterImmediateCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.JalrRegisterImmediateShape

def ImmediateAluRegisterCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.ImmediateAluRegisterShape

def LoadRegisterImmediateCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.LoadRegisterImmediateShape

def StoreRegisterImmediateCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.StoreRegisterImmediateShape

def MemoryRegisterImmediateCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.MemoryRegisterImmediateShape

def ShiftRegisterCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.ShiftRegisterShape

def BranchRegisterImmediateCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.BranchRegisterImmediateShape

def UpperRegisterImmediateCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.UpperRegisterImmediateShape

def JumpRegisterImmediateCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.JumpRegisterImmediateShape

def SupportedFencePredSuccCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.SupportedFencePredSuccShape

def MemoryRefinedSupportedDecodeCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape

def SupportedDecodeCircuitCoveredKnownGood
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCircuitCoveredKnownGood
    iface
    Rv64imShapes.SupportedDecodeShape

def RTypeRegisterNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap iface Rv64imShapes.RTypeRegisterShape

def JalrRegisterImmediateNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap iface Rv64imShapes.JalrRegisterImmediateShape

def ImmediateAluRegisterNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap iface Rv64imShapes.ImmediateAluRegisterShape

def MemoryRegisterImmediateNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap iface Rv64imShapes.MemoryRegisterImmediateShape

def ShiftRegisterNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap iface Rv64imShapes.ShiftRegisterShape

def BranchRegisterImmediateNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap iface Rv64imShapes.BranchRegisterImmediateShape

def UpperRegisterImmediateNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap iface Rv64imShapes.UpperRegisterImmediateShape

def JumpRegisterImmediateNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap iface Rv64imShapes.JumpRegisterImmediateShape

def SupportedFencePredSuccNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap iface Rv64imShapes.SupportedFencePredSuccShape

def MemoryRefinedSupportedDecodeNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap
    iface
    Rv64imShapes.MemoryRefinedSupportedDecodeShape

def SupportedDecodeNoKnownGap
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeNoKnownGap iface Rv64imShapes.SupportedDecodeShape

def RTypeRegisterSailExecutable
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSailExecutable iface Rv64imShapes.RTypeRegisterShape

def JalrRegisterImmediateSailExecutable
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSailExecutable
    iface
    Rv64imShapes.JalrRegisterImmediateShape

def ImmediateAluRegisterSailExecutable
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSailExecutable
    iface
    Rv64imShapes.ImmediateAluRegisterShape

def MemoryRegisterImmediateSailExecutable
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSailExecutable
    iface
    Rv64imShapes.MemoryRegisterImmediateShape

def ShiftRegisterSailExecutable
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSailExecutable iface Rv64imShapes.ShiftRegisterShape

def BranchRegisterImmediateSailExecutable
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSailExecutable
    iface
    Rv64imShapes.BranchRegisterImmediateShape

def UpperRegisterImmediateSailExecutable
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSailExecutable
    iface
    Rv64imShapes.UpperRegisterImmediateShape

def JumpRegisterImmediateSailExecutable
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSailExecutable
    iface
    Rv64imShapes.JumpRegisterImmediateShape

def SupportedFencePredSuccSailExecutable
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSailExecutable
    iface
    Rv64imShapes.SupportedFencePredSuccShape

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

def MemoryRegisterImmediateCompletenessAvoidingKnownBugs
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCompletenessAvoidingKnownBugs
    iface
    Rv64imShapes.MemoryRegisterImmediateShape

def RefinedEdgeCheckedCompletenessAvoidingKnownBugs
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCompletenessAvoidingKnownBugs
    iface
    Rv64imShapes.RefinedEdgeCheckedShape

def WideRefinedCheckedCompletenessAvoidingKnownBugs
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeCompletenessAvoidingKnownBugs
    iface
    Rv64imShapes.WideRefinedCheckedShape

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
