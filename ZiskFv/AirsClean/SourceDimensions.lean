import Extraction.SourceDimensions
import ZiskFv.AirsClean.Main.Circuit
import ZiskFv.AirsClean.Mem.GeneratedTransition
import ZiskFv.AirsClean.MemAlign.Circuit

/-!
# Physical model capacities match compiled source dimensions

Pilout's `numRows` stores an exponent, not a capacity. These kernel-checked
identities bind the live fixed-column schemas to the generated physical row
counts. A compiler dimension change therefore fails the normal Lake build,
even when every row polynomial is unchanged.

Virtual lookup tables have their own source-defined domains and are not
physical AIRs in this metadata. RegisterBoundary is a source loop, not an AIR.
-/

namespace ZiskFv.AirsClean.SourceDimensions

theorem mainFixedCapacity_eq_source :
    Main.mainFixedCapacity = Extraction.SourceDimensions.Main.rowCount := rfl

theorem memFixedCapacity_eq_source :
    Mem.memFixedCapacity = Extraction.SourceDimensions.Mem.rowCount := rfl

theorem memAlignFixedCapacity_eq_source :
    MemAlign.memAlignFixedCapacity = Extraction.SourceDimensions.MemAlign.rowCount := rfl

end ZiskFv.AirsClean.SourceDimensions
