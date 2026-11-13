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

/-- The final-row invariant, including the source's selector guard. -/
def Closed {F : Type} [Field F] (selector contribution running direct : F) : Prop :=
  selector * (contribution - running - direct) = 0

/-- A closure has a witness for every running sum and direct contribution;
this is only constructibility of the local boundary, not logUp soundness. -/
theorem closed_constructible {F : Type} [Field F] (selector running direct : F) :
    Closed selector (running + direct) running direct := by
  simp [Closed]

/-- With the actual final-row selector enabled, the contribution is exactly
running sum plus direct terms, not merely an unconstrained exposed value. -/
theorem closed_at_final_row {F : Type} [Field F] (contribution running direct : F) :
    Closed 1 contribution running direct ↔ contribution = running + direct := by
  simp only [Closed, one_mul, sub_sub, sub_eq_zero]

section Source

variable {C : Type → Type → Sort u} {F : Type} [Field F]
  [Extraction.Circuit F F C] (c : C F F) (row : ℕ)

/-- Main's 96 direct intermediates: c47/c48 and the 31 reload triples,
`std_sum.pil:656`; exposed indices 101--196, in source addition order. -/
def mainDirectSum : F :=
  ((List.range 95).map (fun index => Extraction.Circuit.exposed c (index := 102 + index))).foldl
    (· + ·) (Extraction.Circuit.exposed c (index := 101))

/-- Main c143: __L1__ is fixed column 2; gsum is stage 2 column 0;
gsum_result is air-group value 0; direct im_airvals occupy 101--196. -/
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

end ZiskFv.AirsClean.GsumBoundary
