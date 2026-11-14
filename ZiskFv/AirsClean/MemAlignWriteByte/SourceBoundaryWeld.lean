import ZiskFv.AirsClean.MemAlignWriteByte.SourceBoundary
import ZiskFv.AirsClean.GsumBoundary

/-! Leaf packet reusing the shared typed finalizer source proof. There is one
source object throughout: Direct AIR0/1/2/3 and the distinct result GROUP0.
Actual occurrence in an accepted ensemble is deliberately not asserted here. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte
open Goldilocks
open Extraction.LookupWiring
open ZiskFv.AirsClean.GsumBoundary (Source Closed)

/-- The source Direct and finalizer equations for the very same source object.
No exposed-value alias identifies AIR0 with GROUP0, and no population count is
substituted for AIR0. The shared eight-finalizer machinery owns the c14 weld. -/
theorem sourceBoundary_packet (source : Source FGL) (alpha gamma : FGL)
    (h_direct : SourceDirectsHold source alpha gamma)
    (h_finalizer : source.Holds link_MemAlignWriteByte_14.constraint) :
    DirectSpec (source.airValue 0) (source.airValue 1)
      (source.airValue 2) (source.airValue 3) alpha gamma ∧
    Closed (source.fixed 0 1) (source.airGroupValue 0)
      (source.witness 2 0 0) ((source.airValue 1 + source.airValue 2) + source.airValue 3) := by
  exact ⟨(sourceDirects_iff_model source alpha gamma).mp h_direct,
    (GsumBoundary.memAlignWriteByte_finalizer_typed_source_iff source).mp h_finalizer⟩

end ZiskFv.AirsClean.MemAlignWriteByte
