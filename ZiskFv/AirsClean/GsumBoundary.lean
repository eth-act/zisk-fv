import ZiskFv.AirsClean.GsumBoundary.Model
import Extraction.Main
import Extraction.Binary
import Extraction.BinaryAdd
import Extraction.BinaryExtension
import Extraction.MemAlign
import Extraction.MemAlignByte
import Extraction.MemAlignReadByte
import Extraction.MemAlignWriteByte
import Extraction.LookupWiring

/-!
# Source-local global-sum boundary

`std_sum.pil:688-696` closes each AIR's running sum with its direct AIR-value
terms. These are local stage-2 source-fidelity theorems, not a proof that the
numeric sum implements Clean channel balance. Clean omits these protocol
columns and continues to assume channel balance independently.

The equation and each AIR's cell layout below are maintained independently of
the generated constraint/template. In particular, the direct terms are fixed
here, not read back from the generated link. Changing a coefficient, sign,
selector, group-value index, or term in PIL must break the corresponding weld.
Keep this a leaf import: generated constraints have global simp attributes.
-/

namespace ZiskFv.AirsClean.GsumBoundary

open Extraction.LookupWiring

set_option maxRecDepth 4000

section Source

variable {C : Type → Type → Sort u} {F : Type} [Field F]
  [Extraction.Circuit F F C] (c : C F F) (row : ℕ)

/-- Main's 96 direct intermediates: c47/c48 and the 31 reload triples,
`std_sum.pil:656`; exposed indices 101--196, in source addition order. -/
def mainDirectSum : F :=
  ((List.range 95).map (fun index => Extraction.Circuit.exposed c (index := 102 + index))).foldl
    (· + ·) (Extraction.Circuit.exposed c (index := 101))

/-- Main c143: __L1__ is fixed column 2; gsum is stage 2 column 0;
Zisk.gsum_result is air-group value 0; Main.im_direct spans AIR indices 101--196. -/
theorem main_finalizer_source_iff :
    Main.extraction.constraint_143_every_row c row ↔
      Closed (Extraction.Circuit.preprocessed c (column := 2) (row := row + 1) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.main c (id := 2) (column := 0) (row := row) (rotation := 0))
        (mainDirectSum c) := by
  rfl

/-- Binary c13, `std_sum.pil:696`: im_direct is AIR value 1. -/
theorem binary_finalizer_source_iff :
    Binary.extraction.constraint_13_every_row c row ↔
      Closed (Extraction.Circuit.preprocessed c (column := 0) (row := row + 1) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.main c (id := 2) (column := 0) (row := row) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 1)) := by
  rfl

/-- BinaryAdd c8 has the same scalar layout, independently source-pinned. -/
theorem binaryAdd_finalizer_source_iff :
    BinaryAdd.extraction.constraint_8_every_row c row ↔
      Closed (Extraction.Circuit.preprocessed c (column := 0) (row := row + 1) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.main c (id := 2) (column := 0) (row := row) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 1)) := by
  rfl

/-- BinaryExtension c7: its own im_direct is AIR value 1. -/
theorem binaryExtension_finalizer_source_iff :
    BinaryExtension.extraction.constraint_7_every_row c row ↔
      Closed (Extraction.Circuit.preprocessed c (column := 0) (row := row + 1) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.main c (id := 2) (column := 0) (row := row) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 1)) := by
  rfl

/-- MemAlign c39 has no direct contribution; __L1__ is fixed column 1. -/
theorem memAlign_finalizer_source_iff :
    MemAlign.extraction.constraint_39_every_row c row ↔
      Closed (Extraction.Circuit.preprocessed c (column := 1) (row := row + 1) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.main c (id := 2) (column := 0) (row := row) (rotation := 0)) 0 := by
  simp only [MemAlign.extraction.constraint_39_every_row, Closed, sub_zero]

/-- MemAlignByte c15: the two direct padding adjustments are AIR values 1,2. -/
theorem memAlignByte_finalizer_source_iff :
    MemAlignByte.extraction.constraint_15_every_row c row ↔
      Closed (Extraction.Circuit.preprocessed c (column := 0) (row := row + 1) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.main c (id := 2) (column := 0) (row := row) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 1) + Extraction.Circuit.exposed c (index := 2)) := by
  rfl

/-- MemAlignReadByte c9: both direct padding adjustments, in source order. -/
theorem memAlignReadByte_finalizer_source_iff :
    MemAlignReadByte.extraction.constraint_9_every_row c row ↔
      Closed (Extraction.Circuit.preprocessed c (column := 0) (row := row + 1) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.main c (id := 2) (column := 0) (row := row) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 1) + Extraction.Circuit.exposed c (index := 2)) := by
  rfl

/-- MemAlignWriteByte c14: all three direct intermediates, with source's
left-associated addition and no omitted padding adjustment. -/
theorem memAlignWriteByte_finalizer_source_iff :
    MemAlignWriteByte.extraction.constraint_14_every_row c row ↔
      Closed (Extraction.Circuit.preprocessed c (column := 0) (row := row + 1) (rotation := 0))
        (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.main c (id := 2) (column := 0) (row := row) (rotation := 0))
        ((Extraction.Circuit.exposed c (index := 1) + Extraction.Circuit.exposed c (index := 2)) +
          Extraction.Circuit.exposed c (index := 3)) := by
  rfl

end Source

def mainTypedDirectSum {F : Type} [Field F] (source : Source F) : F :=
  ((List.range 95).map (fun index => source.airValue (102 + index))).foldl
    (· + ·) (source.airValue 101)

section TypedSource

variable {F : Type} [Field F] (source : Source F)

/-- These welds interpret the actual lossless constraint, not `link.template`
or its unconstrained direct-term list. Every expected source cell is fixed in
the conclusion independently of generation. -/
theorem main_finalizer_typed_source_iff :
    source.Holds link_Main_143.constraint ↔
      Closed (source.fixed 2 1) (source.airGroupValue 0)
        (source.witness 2 0 0) (mainTypedDirectSum source) := by
  change some (source.fixed 2 1 *
    (source.airGroupValue 0 - source.witness 2 0 0 - mainTypedDirectSum source)) = some 0 ↔ _
  simp only [Option.some.injEq, Closed]

theorem binary_finalizer_typed_source_iff :
    source.Holds link_Binary_13.constraint ↔
      Closed (source.fixed 0 1) (source.airGroupValue 0)
        (source.witness 2 0 0) (source.airValue 1) := by
  change some (source.fixed 0 1 *
    (source.airGroupValue 0 - source.witness 2 0 0 - source.airValue 1)) = some 0 ↔ _
  simp only [Option.some.injEq, Closed]

theorem binaryAdd_finalizer_typed_source_iff :
    source.Holds link_BinaryAdd_8.constraint ↔
      Closed (source.fixed 0 1) (source.airGroupValue 0)
        (source.witness 2 0 0) (source.airValue 1) := by
  change some (source.fixed 0 1 *
    (source.airGroupValue 0 - source.witness 2 0 0 - source.airValue 1)) = some 0 ↔ _
  simp only [Option.some.injEq, Closed]

theorem binaryExtension_finalizer_typed_source_iff :
    source.Holds link_BinaryExtension_7.constraint ↔
      Closed (source.fixed 0 1) (source.airGroupValue 0)
        (source.witness 2 0 0) (source.airValue 1) := by
  change some (source.fixed 0 1 *
    (source.airGroupValue 0 - source.witness 2 0 0 - source.airValue 1)) = some 0 ↔ _
  simp only [Option.some.injEq, Closed]

theorem memAlign_finalizer_typed_source_iff :
    source.Holds link_MemAlign_39.constraint ↔
      Closed (source.fixed 1 1) (source.airGroupValue 0) (source.witness 2 0 0) 0 := by
  change some (source.fixed 1 1 *
    (source.airGroupValue 0 - source.witness 2 0 0)) = some 0 ↔ _
  simp only [Option.some.injEq, Closed, sub_zero]

theorem memAlignByte_finalizer_typed_source_iff :
    source.Holds link_MemAlignByte_15.constraint ↔
      Closed (source.fixed 0 1) (source.airGroupValue 0)
        (source.witness 2 0 0) (source.airValue 1 + source.airValue 2) := by
  change some (source.fixed 0 1 *
    (source.airGroupValue 0 - source.witness 2 0 0 -
      (source.airValue 1 + source.airValue 2))) = some 0 ↔ _
  simp only [Option.some.injEq, Closed]

theorem memAlignReadByte_finalizer_typed_source_iff :
    source.Holds link_MemAlignReadByte_9.constraint ↔
      Closed (source.fixed 0 1) (source.airGroupValue 0)
        (source.witness 2 0 0) (source.airValue 1 + source.airValue 2) := by
  change some (source.fixed 0 1 *
    (source.airGroupValue 0 - source.witness 2 0 0 -
      (source.airValue 1 + source.airValue 2))) = some 0 ↔ _
  simp only [Option.some.injEq, Closed]

theorem memAlignWriteByte_finalizer_typed_source_iff :
    source.Holds link_MemAlignWriteByte_14.constraint ↔
      Closed (source.fixed 0 1) (source.airGroupValue 0)
        (source.witness 2 0 0) ((source.airValue 1 + source.airValue 2) + source.airValue 3) := by
  change some (source.fixed 0 1 *
    (source.airGroupValue 0 - source.witness 2 0 0 -
      ((source.airValue 1 + source.airValue 2) + source.airValue 3))) = some 0 ↔ _
  simp only [Option.some.injEq, Closed]

end TypedSource

/-- Independent AST cell pins distinguish AIR-group contribution 0 from AIR
value 0 even though the legacy single-field Circuit shim projects both through
`exposed`. The source correspondence above is not allowed to erase this pin. -/
theorem binary_finalizer_cells :
    link_Binary_13.selector = .fixed 0 1 ∧
    link_Binary_13.groupValue = .airGroupValue 0 ∧
    link_Binary_13.gsum = .witness 2 0 0 ∧
    link_Binary_13.directTerms = [.airValue 1] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem main_finalizer_cells :
    link_Main_143.selector = .fixed 2 1 ∧
    link_Main_143.groupValue = .airGroupValue 0 ∧
    link_Main_143.gsum = .witness 2 0 0 ∧
    link_Main_143.directTerms = (List.range 96).map (fun index => Expr.airValue (101 + index)) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem binaryAdd_finalizer_cells :
    link_BinaryAdd_8.selector = .fixed 0 1 ∧
    link_BinaryAdd_8.groupValue = .airGroupValue 0 ∧
    link_BinaryAdd_8.gsum = .witness 2 0 0 ∧
    link_BinaryAdd_8.directTerms = [.airValue 1] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem binaryExtension_finalizer_cells :
    link_BinaryExtension_7.selector = .fixed 0 1 ∧
    link_BinaryExtension_7.groupValue = .airGroupValue 0 ∧
    link_BinaryExtension_7.gsum = .witness 2 0 0 ∧
    link_BinaryExtension_7.directTerms = [.airValue 1] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem memAlign_finalizer_cells :
    link_MemAlign_39.selector = .fixed 1 1 ∧
    link_MemAlign_39.groupValue = .airGroupValue 0 ∧
    link_MemAlign_39.gsum = .witness 2 0 0 ∧
    link_MemAlign_39.directTerms = [] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem memAlignByte_finalizer_cells :
    link_MemAlignByte_15.selector = .fixed 0 1 ∧
    link_MemAlignByte_15.groupValue = .airGroupValue 0 ∧
    link_MemAlignByte_15.gsum = .witness 2 0 0 ∧
    link_MemAlignByte_15.directTerms = [.airValue 1, .airValue 2] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem memAlignReadByte_finalizer_cells :
    link_MemAlignReadByte_9.selector = .fixed 0 1 ∧
    link_MemAlignReadByte_9.groupValue = .airGroupValue 0 ∧
    link_MemAlignReadByte_9.gsum = .witness 2 0 0 ∧
    link_MemAlignReadByte_9.directTerms = [.airValue 1, .airValue 2] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem memAlignWriteByte_finalizer_cells :
    link_MemAlignWriteByte_14.selector = .fixed 0 1 ∧
    link_MemAlignWriteByte_14.groupValue = .airGroupValue 0 ∧
    link_MemAlignWriteByte_14.gsum = .witness 2 0 0 ∧
    link_MemAlignWriteByte_14.directTerms = [.airValue 1, .airValue 2, .airValue 3] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- All declarations participating in the final-row protocol: the selected
fixed column, stage-2 running sum, complete group-value roster, and complete
stage-2 AIR-value roster. Names are not used to select the expected cells. -/
def protocolSchema (schema : SourceSchema.Air) (selectorIndex : Nat) :
    List SourceSchema.Symbol :=
  schema.symbols.filter fun symbol =>
    (symbol.kind == .fixed && symbol.index == selectorIndex) ||
    (symbol.kind == .witness && symbol.stage == some 2 && symbol.index == 0) ||
    symbol.kind == .airGroupValue ||
    (symbol.kind == .airValue && symbol.stage == some 2)

/-- Actual public source symbols name this array `Main.im_direct`, not the
internal `im_airvals` alias in std_sum. Its base index and full array roster
jointly cover the 96 independently pinned direct-term operands above. -/
theorem main_finalizer_schema :
    link_Main_143.air = "Main" ∧ link_Main_143.constraintIndex = 143 ∧
    (SourceSchema.air_Main.groupIndex, SourceSchema.air_Main.airIndex,
      SourceSchema.air_Main.groupName, SourceSchema.air_Main.airName) = (0, 12, "Zisk", "Main") ∧
    protocolSchema SourceSchema.air_Main 2 =
      [ ⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩
      , ⟨some 0, some 12, "gsum", .witness, some 2, 0, 0, []⟩
      , ⟨some 0, some 12, "__L1__", .fixed, some 0, 2, 0, []⟩
      , ⟨some 0, some 12, "Main.im_direct", .airValue, some 2, 101, 1, [96]⟩ ] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem binary_finalizer_schema :
    link_Binary_13.air = "Binary" ∧ link_Binary_13.constraintIndex = 13 ∧
    (SourceSchema.air_Binary.groupIndex, SourceSchema.air_Binary.airIndex,
      SourceSchema.air_Binary.groupName, SourceSchema.air_Binary.airName) = (0, 22, "Zisk", "Binary") ∧
    protocolSchema SourceSchema.air_Binary 0 =
      [ ⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩
      , ⟨some 0, some 22, "gsum", .witness, some 2, 0, 0, []⟩
      , ⟨some 0, some 22, "__L1__", .fixed, some 0, 0, 0, []⟩
      , ⟨some 0, some 22, "Binary.im_direct", .airValue, some 2, 1, 1, [1]⟩ ] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem binaryAdd_finalizer_schema :
    link_BinaryAdd_8.air = "BinaryAdd" ∧ link_BinaryAdd_8.constraintIndex = 8 ∧
    (SourceSchema.air_BinaryAdd.groupIndex, SourceSchema.air_BinaryAdd.airIndex,
      SourceSchema.air_BinaryAdd.groupName, SourceSchema.air_BinaryAdd.airName) = (0, 23, "Zisk", "BinaryAdd") ∧
    protocolSchema SourceSchema.air_BinaryAdd 0 =
      [ ⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩
      , ⟨some 0, some 23, "gsum", .witness, some 2, 0, 0, []⟩
      , ⟨some 0, some 23, "__L1__", .fixed, some 0, 0, 0, []⟩
      , ⟨some 0, some 23, "BinaryAdd.im_direct", .airValue, some 2, 1, 1, [1]⟩ ] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem binaryExtension_finalizer_schema :
    link_BinaryExtension_7.air = "BinaryExtension" ∧ link_BinaryExtension_7.constraintIndex = 7 ∧
    (SourceSchema.air_BinaryExtension.groupIndex, SourceSchema.air_BinaryExtension.airIndex,
      SourceSchema.air_BinaryExtension.groupName, SourceSchema.air_BinaryExtension.airName) =
        (0, 24, "Zisk", "BinaryExtension") ∧
    protocolSchema SourceSchema.air_BinaryExtension 0 =
      [ ⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩
      , ⟨some 0, some 24, "gsum", .witness, some 2, 0, 0, []⟩
      , ⟨some 0, some 24, "__L1__", .fixed, some 0, 0, 0, []⟩
      , ⟨some 0, some 24, "BinaryExtension.im_direct", .airValue, some 2, 1, 1, [1]⟩ ] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem memAlign_finalizer_schema :
    link_MemAlign_39.air = "MemAlign" ∧ link_MemAlign_39.constraintIndex = 39 ∧
    (SourceSchema.air_MemAlign.groupIndex, SourceSchema.air_MemAlign.airIndex,
      SourceSchema.air_MemAlign.groupName, SourceSchema.air_MemAlign.airName) = (0, 17, "Zisk", "MemAlign") ∧
    protocolSchema SourceSchema.air_MemAlign 1 =
      [ ⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩
      , ⟨some 0, some 17, "gsum", .witness, some 2, 0, 0, []⟩
      , ⟨some 0, some 17, "__L1__", .fixed, some 0, 1, 0, []⟩ ] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem memAlignByte_finalizer_schema :
    link_MemAlignByte_15.air = "MemAlignByte" ∧ link_MemAlignByte_15.constraintIndex = 15 ∧
    (SourceSchema.air_MemAlignByte.groupIndex, SourceSchema.air_MemAlignByte.airIndex,
      SourceSchema.air_MemAlignByte.groupName, SourceSchema.air_MemAlignByte.airName) = (0, 18, "Zisk", "MemAlignByte") ∧
    protocolSchema SourceSchema.air_MemAlignByte 0 =
      [ ⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩
      , ⟨some 0, some 18, "gsum", .witness, some 2, 0, 0, []⟩
      , ⟨some 0, some 18, "__L1__", .fixed, some 0, 0, 0, []⟩
      , ⟨some 0, some 18, "MemAlignByte.im_direct", .airValue, some 2, 1, 1, [2]⟩ ] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem memAlignReadByte_finalizer_schema :
    link_MemAlignReadByte_9.air = "MemAlignReadByte" ∧ link_MemAlignReadByte_9.constraintIndex = 9 ∧
    (SourceSchema.air_MemAlignReadByte.groupIndex, SourceSchema.air_MemAlignReadByte.airIndex,
      SourceSchema.air_MemAlignReadByte.groupName, SourceSchema.air_MemAlignReadByte.airName) =
        (0, 19, "Zisk", "MemAlignReadByte") ∧
    protocolSchema SourceSchema.air_MemAlignReadByte 0 =
      [ ⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩
      , ⟨some 0, some 19, "gsum", .witness, some 2, 0, 0, []⟩
      , ⟨some 0, some 19, "__L1__", .fixed, some 0, 0, 0, []⟩
      , ⟨some 0, some 19, "MemAlignReadByte.im_direct", .airValue, some 2, 1, 1, [2]⟩ ] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem memAlignWriteByte_finalizer_schema :
    link_MemAlignWriteByte_14.air = "MemAlignWriteByte" ∧ link_MemAlignWriteByte_14.constraintIndex = 14 ∧
    (SourceSchema.air_MemAlignWriteByte.groupIndex, SourceSchema.air_MemAlignWriteByte.airIndex,
      SourceSchema.air_MemAlignWriteByte.groupName, SourceSchema.air_MemAlignWriteByte.airName) =
        (0, 20, "Zisk", "MemAlignWriteByte") ∧
    protocolSchema SourceSchema.air_MemAlignWriteByte 0 =
      [ ⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩
      , ⟨some 0, some 20, "gsum", .witness, some 2, 0, 0, []⟩
      , ⟨some 0, some 20, "__L1__", .fixed, some 0, 0, 0, []⟩
      , ⟨some 0, some 20, "MemAlignWriteByte.im_direct", .airValue, some 2, 1, 1, [3]⟩ ] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end ZiskFv.AirsClean.GsumBoundary
