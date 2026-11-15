import ZiskFv.AirsClean.GsumBoundary.Model
import ZiskFv.AirsClean.MemAlignWriteByte.Direct

/-! Lossless local segment boundary. The actual source object supplies all AIR
and AIR-group cells; AIR0 is the unrestricted Direct scalar, GROUP0 is the
independent finalizer result. No witness-builder count is an acceptance premise.
The common GsumBoundary module owns the finalizer equation and its source weld. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte
open Goldilocks
open Extraction.LookupWiring
open ZiskFv.AirsClean.GsumBoundary (Source Closed)

/-- Source Direct syntax extends the shared finalizer view only with the actual
challenge/literal forms used by c11-c13. Unsupported forms return none. AIR and
AIR-group cells are always read through their distinct shared source functions. -/
def evalDirectSource (source : Source FGL) (alpha gamma : FGL) : Expr → Option FGL
  | .constant "0" => some 0
  | .constant "1" => some 1
  | .constant "2" => some 2
  | .constant "8" => some 8
  | .constant "10" => some 10
  | .challenge 2 0 => some alpha
  | .challenge 2 1 => some gamma
  | .airValue index => source.eval (.airValue index)
  | .airGroupValue index => source.eval (.airGroupValue index)
  | .witness stage column offset => source.eval (.witness stage column offset)
  | .fixed column offset => source.eval (.fixed column offset)
  | .add lhs rhs => return (← evalDirectSource source alpha gamma lhs) +
      (← evalDirectSource source alpha gamma rhs)
  | .sub lhs rhs => return (← evalDirectSource source alpha gamma lhs) -
      (← evalDirectSource source alpha gamma rhs)
  | .mul lhs rhs => return (← evalDirectSource source alpha gamma lhs) *
      (← evalDirectSource source alpha gamma rhs)
  | _ => none

def SourceDirectsHold (source : Source FGL) (alpha gamma : FGL) : Prop :=
  evalDirectSource source alpha gamma link_MemAlignWriteByte_11.constraint = some 0 ∧
  evalDirectSource source alpha gamma link_MemAlignWriteByte_12.constraint = some 0 ∧
  evalDirectSource source alpha gamma link_MemAlignWriteByte_13.constraint = some 0

/-- The actual c11-c13 expressions read the shared object's exact AIR cells.
Their scalar is not substituted by a population count. -/
theorem sourceDirects_iff_model (source : Source FGL) (alpha gamma : FGL) :
    SourceDirectsHold source alpha gamma ↔
      DirectSpec (source.airValue 0) (source.airValue 1)
        (source.airValue 2) (source.airValue 3) alpha gamma := by
  change
    (some (source.airValue 1 * loadPaddingDenominator alpha gamma - source.airValue 0) = some 0 ∧
    some (source.airValue 2 * selectedStorePaddingDenominator alpha gamma - (0 - source.airValue 0)) = some 0 ∧
    some (source.airValue 3 * alignedStorePaddingDenominator alpha gamma - source.airValue 0) = some 0) ↔ _
  simp only [Option.some.injEq, DirectSpec]

def sourceDirectInteractions (source : Source FGL) := directInteractions (source.airValue 0)

def sourceDirectMain (source : Source FGL) := directMain (source.airValue 0)

theorem sourceDirectMain_operations (source : Source FGL) (offset : ℕ) :
    (sourceDirectMain source).operations offset =
      (sourceDirectInteractions source).map (fun interaction => Operation.interact interaction.toRaw) := rfl

/-- The two source kinds remain independent even when their indices coincide. -/
theorem source_kind_cells (source : Source FGL) (alpha gamma : FGL) :
    evalDirectSource source alpha gamma (.airValue 0) = some (source.airValue 0) ∧
    evalDirectSource source alpha gamma (.airGroupValue 0) = some (source.airGroupValue 0) := ⟨rfl, rfl⟩

/-- Arbitrary source AIR scalar has actual Direct witnesses; this is deliberately
not a proof that the scalar counts physical unused rows. -/
theorem sourceDirects_constructible (source : Source FGL) (alpha gamma : FGL)
    (hload : loadPaddingDenominator alpha gamma ≠ 0)
    (hselected : selectedStorePaddingDenominator alpha gamma ≠ 0)
    (haligned : alignedStorePaddingDenominator alpha gamma ≠ 0) :
    ∃ imLoad imSelected imAligned,
      DirectSpec (source.airValue 0) imLoad imSelected imAligned alpha gamma :=
  directSpec_constructible_arbitrary_count (source.airValue 0) alpha gamma hload hselected haligned

end ZiskFv.AirsClean.MemAlignWriteByte
