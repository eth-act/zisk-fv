import Source415DomainComparison.Old16
import Source415DomainComparison.Accepted16
import Source415DomainComparison.FieldTransport
import Source415DomainComparison.PhysicalCompletion
import Source415DomainComparison.WitnessSplice
import Source415DomainComparison.RowCompatibility
import Source415DomainComparison.TransitionCompatibility
import Source415DomainComparison.OldChannelStreams
import Source415DomainComparison.SevenWitnesses
import Source415DomainComparison.BalancedCounts
import Source415DomainComparison.MainCapacity
import Source415DomainComparison.ReplayFieldPreservation
import Source415DomainComparison.OldOperationCounts
import Source415DomainComparison.ForwardRequests
import Source415DomainComparison.ForwardCompletion
import Source415DomainComparison.ReverseProjection
import Source415DomainComparison.ReverseStreams
import Source415DomainComparison.ReverseFields
import Source415DomainComparison.ProjectionRetraction
import Source415DomainComparison.SourceCommitmentBoundary

/-! Historical comparative proof root. Both endpoints are frozen: historical45
old16 and historical457 old18 retain the original numeric Mem D1. The reverse
old18→old16 theorem and the seven genuine old-domain constructions therefore
do not silently acquire the corrected production Mem domain. ConcreteOldWorlds
also retains the original ADD prefix-one case and proves old Sd/Ld numeric D1
on the original rows/data. Forward completion chooses genuine ordered request
histograms; it is not equality to arbitrary committed provider raw. Reverse
projection allows arbitrary accepted source prefixes. The separate Source458
transport is one-way old18→corrected18, not an inverse numeric reconstruction.
No production root or protected acceptance contract is changed here. -/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

 theorem concrete_splice_constraints_and_mem_guard {p : Nat} {program : Program p}
    (old : OldWitness p program) (raw : PackedVirtualTableSources.Witness FGL)
    (constraints : old.Constraints) :
    (completedWitness old raw).Constraints ∧
      (ZiskFv.Compliance.Legacy45.MutableMemPresent old ↔
        ZiskFv.Compliance.Legacy457.MutableMemPresent (completedWitness old raw)) :=
  ⟨completed_constraints old raw constraints, completed_mutableMemPresent old raw⟩

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
