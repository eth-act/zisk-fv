import ZiskFv.Compliance.AcceptedTrace.MainTable
import ZiskFv.SailSpec.Auxiliaries

/-!
A `ProgramBinding` ties a trace to a concrete run, supplying the sequence of Sail machine states the
program steps through (`stateAt`) plus the lone external assumption about the derived Main table —
that it has one row per instruction (`mainTable_index`). Which witness table is the Main execution
table is now derived on `AcceptedTrace` (`trace.mainTable`, with its membership and component facts),
no longer a `ProgramBinding` field.
-/

namespace ZiskFv.Compliance

/-- Binds an `AcceptedTrace` to a concrete program run: the per-instruction Sail
    state sequence, plus the row-count assumption on the derived Main table. -/
structure ProgramBinding (trace : AcceptedTrace) where
  stateAt :
    Fin trace.numInstructions →
      PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  mainTable_index : ∀ i : Fin trace.numInstructions, i.val < trace.mainTable.table.length

end ZiskFv.Compliance
