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

/-! PRIVATE comparative proof root. This deliberately does not change the
production root or claim that the two Accepted contracts are interchangeable.
All comparison declarations, including snapshots and seven genuine current
constructions, are reachable for elaboration and complete raw trust auditing.
Forward completion chooses genuine ordered request histograms; it is not
equality to an arbitrary committed source-provider raw. Reverse projection
allows arbitrary accepted source prefixes. No definitional equality, equality
of discarded provider commitments, or protected public cutover is claimed. -/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

 theorem concrete_splice_constraints_and_mem_guard {p : Nat} {program : Program p}
    (old : OldWitness p program) (raw : PackedVirtualTableSources.Witness FGL)
    (constraints : old.Constraints) :
    (completedWitness old raw).Constraints ∧
      (ZiskFv.Compliance.Legacy45.MutableMemPresent old ↔
        ZiskFv.Compliance.MutableMemPresent (completedWitness old raw)) :=
  ⟨completed_constraints old raw constraints, completed_mutableMemPresent old raw⟩

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
