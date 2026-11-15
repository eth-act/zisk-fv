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

/-! PRIVATE comparative proof root. This deliberately does not change the
production root or claim that the two Accepted contracts are interchangeable.
All comparison declarations, including snapshots and seven genuine current
constructions, are reachable for elaboration and complete raw trust auditing.
The accepted-domain counting/request extraction and reverse-direction proof
obligations remain explicit in the comparative evidence ledger. -/

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
