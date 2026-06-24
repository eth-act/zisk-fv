import ZiskFv.Completeness.Rv64im.Shapes
import ZiskFv.Completeness.Aspirational.Interface

/- ⚠ ASPIRATIONAL / QUARANTINED — not wired to any live completeness endpoint.
   Abstract `Rv.Interface`-parametrized route; no concrete `Interface` is ever
   built, and the live endpoints in `ZiskFv.Completeness`
   (`root_completeness_sail`, `eventual_zisk_coverage`, `eventual_root_completeness`)
   do not depend on it. Intended *eventual* composition machinery for when the
   Aeneas-extracted ZisK coverage proofs can be imported into this build. Kept
   compiling via `ZiskFv.lean` for preservation only.
   See `ZiskFv/Completeness/Aspirational/README.md`. -/

/-!
# RV64IM completeness — predicate definitions

Predicate `def`/`abbrev` declarations shared by the RV64IM completeness
proof parts. Split verbatim out of `ZiskFv/Completeness/Rv64im.lean`.
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

def Rv64imCompletenessAvoidingKnownDecodeBugs
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.CompletenessAvoidingKnownDecodeBugs iface

def Rv64imCompletenessWithSoundnessInputAvoidingKnownDecodeBugs
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.CompletenessWithSoundnessInputAvoidingKnownDecodeBugs iface

def SupportedDecodeAvoidKnownDecodeBugs
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeAvoidKnownDecodeBugs
    iface
    Rv64imShapes.SupportedDecodeShape

def SupportedDecodeSoundnessInputComplete
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSoundnessInputComplete
    iface
    Rv64imShapes.SupportedDecodeShape

def RTypeRegisterSoundnessInputComplete
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSoundnessInputComplete
    iface
    Rv64imShapes.RTypeRegisterShape

def JalrRegisterImmediateSoundnessInputComplete
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSoundnessInputComplete
    iface
    Rv64imShapes.JalrRegisterImmediateShape

def ImmediateAluRegisterSoundnessInputComplete
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSoundnessInputComplete
    iface
    Rv64imShapes.ImmediateAluRegisterShape

def MemoryRegisterImmediateSoundnessInputComplete
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSoundnessInputComplete
    iface
    Rv64imShapes.MemoryRegisterImmediateShape

def ShiftRegisterSoundnessInputComplete
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSoundnessInputComplete
    iface
    Rv64imShapes.ShiftRegisterShape

def BranchRegisterImmediateSoundnessInputComplete
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSoundnessInputComplete
    iface
    Rv64imShapes.BranchRegisterImmediateShape

def UpperRegisterImmediateSoundnessInputComplete
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSoundnessInputComplete
    iface
    Rv64imShapes.UpperRegisterImmediateShape

def JumpRegisterImmediateSoundnessInputComplete
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSoundnessInputComplete
    iface
    Rv64imShapes.JumpRegisterImmediateShape

def SupportedFencePredSuccSoundnessInputComplete
    (iface : Rv.Interface) : Prop :=
  Rv.Interface.ShapeSoundnessInputComplete
    iface
    Rv64imShapes.SupportedFencePredSuccShape

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

end ZiskFv.Completeness.Rv64im
