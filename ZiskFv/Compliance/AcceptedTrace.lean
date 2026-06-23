import ZiskFv.AirsClean.FullEnsemble

/-!
# Accepted trace

An `AcceptedTrace` is one fully-populated, verifier-accepted run of the RV64IM
circuit for a fixed `program` of `length` instructions.

The circuit is an **Air.Flat ensemble**: a collection of AIRs (the Main table
plus the binary / arithmetic / memory / lookup tables) wired together by shared
*channels* — the operation bus and the lookup / permutation buses.
`(fullRv64imEnsemble length program).ensemble` is just that collection of column
layouts and channels; it holds no data of its own.

The `witness` is the ensemble *filled in* with concrete Goldilocks values: every
AIR's grid of rows. The remaining three fields are the proofs that make the
witness "accepted" — exactly what a real ZisK proof certifies:

* `constraints_hold : witness.Constraints` — every per-row algebraic gate of every
  table holds (the polynomial constraint equations are satisfied).
* `spec_holds : witness.Spec` — every table additionally meets its higher-level *spec*
  predicate: the semantic relation each AIR is meant to encode (e.g. a Binary
  row really computes AND/OR/XOR; an ArithMul row's lanes are a correct
  product). It is the meaning the constraints exist to enforce, stated directly
  rather than as gate polynomials.
* `channels_balanced : witness.BalancedChannels` — despite the name, **not a boolean**: it
  is the *proposition* that every cross-table channel balances, i.e. for each bus
  the multiset of messages sent equals the multiset received (the logUp /
  permutation argument). This is what stops a table from fabricating or dropping
  a bus message, gluing the otherwise-independent AIRs into one sound machine.

It is the single object the soundness development quantifies over; everything
downstream (`ProgramBinding`, the provider-match wrappers, the per-op
constructions) is built relative to one of these.
-/

namespace ZiskFv.Compliance

/-- Accepted committed trace for the full RV64IM Clean ensemble. -/
structure AcceptedTrace where
  numInstructions : Nat
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program numInstructions
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble numInstructions program).ensemble
  constraints_hold : witness.Constraints
  spec_holds : witness.Spec
  channels_balanced : witness.BalancedChannels

end ZiskFv.Compliance
