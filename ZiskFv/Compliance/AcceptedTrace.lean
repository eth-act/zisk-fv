import ZiskFv.AirsClean.FullEnsemble

/-!
# Accepted trace

The committed full-ensemble trace: a Clean ensemble witness for some RV64IM
`program` together with the proofs that it satisfies the per-table constraints
and spec and that all of its channels balance. It is the single object the
soundness development quantifies over — everything downstream (`ProgramBinding`,
the provider-match wrappers, the per-op constructions) is built relative to one
of these.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.AirsClean.FullEnsemble

/-- Accepted committed trace for the full RV64IM Clean ensemble. -/
structure AcceptedTrace where
  length : Nat
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program length
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble
  constraints : witness.Constraints
  spec : witness.Spec
  balanced : witness.BalancedChannels

end ZiskFv.Compliance
