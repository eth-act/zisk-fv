import ZiskFv.Completeness.Rv64im.Defs
import ZiskFv.Completeness.Rv64im.CoreAndShapeFamilies
import ZiskFv.Completeness.Rv64im.CheckedShapeFamilies
import ZiskFv.Completeness.Rv64im.SupportedDecodeShape
import ZiskFv.Completeness.Rv64im.MemoryRefinedAndImmediateEdges
import ZiskFv.Completeness.Rv64im.SupportedDecodeRefinedFamilies
import ZiskFv.Completeness.Rv64im.GlobalTargets

/- ⚠ ASPIRATIONAL / QUARANTINED — aggregator for the abstract `Rv.Interface`
   completeness route. None of the modules below are used by the live endpoints
   in `ZiskFv.Completeness` (`root_completeness_sail`, `eventual_zisk_coverage`,
   `eventual_root_completeness`). This aggregator is imported only by `ZiskFv.lean`
   so the route stays built and verified for preservation, not because anything
   depends on it. See `ZiskFv/Completeness/Rv64im/ASPIRATIONAL.md`. -/

/-!
# RV64IM completeness

This module states the checked-in RV64IM completeness theorem surface.

The concrete generated predicates live outside the repository in the
reproducible extraction workspace. Here we keep the uniform theorem in the
normal Lean build: every Sail-executable RV64IM raw instruction is covered by
the production ZisK decode/lower/materialize/soundness-input surface, except
for explicitly recorded ZisK decode gaps.

This file is a thin aggregator: the declarations now live in the
`ZiskFv.Completeness.Rv64im.*` parts, re-exported here so the module name
`ZiskFv.Completeness.Rv64im` continues to provide every declaration to existing
consumers.
-/
