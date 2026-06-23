import ZiskFv.Compliance.AcceptedTrace.Spec
import ZiskFv.SailSpec.Auxiliaries

/-!
# Program binding

The table-skeleton premise an `AcceptedTrace` is interpreted against: a Sail
state sequence over the trace, the selected Main table, and the facts pinning
that table into the witness (membership, component identity, per-row index
bound). It is the bucket-(b) input to the per-op constructions; the decode and
Sail-binding residuals are supplied separately as honest top-level binders (see
`ZiskFv/Compliance/ConstructionSub.lean`), not as projections of this record.
-/

namespace ZiskFv.Compliance

/-- The named program-binding premise for the P4 construction (table skeleton).

It supplies the Sail state sequence, the selected Main table, and the table's
membership / component / index facts. -/
structure ProgramBinding (trace : AcceptedTrace) where
  stateAt :
    Fin trace.numInstructions →
      PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  mainTable : Air.Flat.Table FGL
  mainTable_mem : mainTable ∈ trace.witness.allTables
  mainTable_component :
    mainTable.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        trace.numInstructions trace.program
  mainTable_index : ∀ i : Fin trace.numInstructions, i.val < mainTable.table.length

end ZiskFv.Compliance
