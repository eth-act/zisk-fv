import ZiskFv.Completeness.Aspirational.Interface
import ZiskFv.Completeness.Aspirational.Defs
import ZiskFv.Completeness.Aspirational.CoreAndShapeFamilies
import ZiskFv.Completeness.Aspirational.CheckedShapeFamilies
import ZiskFv.Completeness.Aspirational.SupportedDecodeShape
import ZiskFv.Completeness.Aspirational.MemoryRefinedAndImmediateEdges
import ZiskFv.Completeness.Aspirational.SupportedDecodeRefinedFamilies
import ZiskFv.Completeness.Aspirational.GlobalTargets

/- ⚠ ASPIRATIONAL / QUARANTINED — aggregator for the abstract `Rv.Interface`
   completeness route. None of the modules above are used by the live endpoints
   in `ZiskFv.Completeness` (`sail_executable_within_supported_decode_shape`,
   `skeletal_root_completeness`). This aggregator is imported only by `ZiskFv.lean`
   so the route stays built and verified for preservation, not because anything
   depends on it. See `ZiskFv/Completeness/Aspirational/README.md`. -/
