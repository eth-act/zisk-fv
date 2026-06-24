import ZiskFv.Compliance.AcceptedTrace.Spec
import ZiskFv.SailSpec.Auxiliaries

/-!
A `ProgramBinding` ties a trace to a concrete run, supplying the sequence of Sail machine states the
program steps through (`stateAt`) and a choice of which witness table is the Main execution table
(`mainTable`) — with the facts pinning that table down : that it really occurs in the witness
(`mainTable_mem`), really is the Main component (`mainTable_component`), and has one row per
instruction (`mainTable_index`).
-/

namespace ZiskFv.Compliance

/-- Binds an `AcceptedTrace` to a concrete program run: the per-instruction Sail
    state sequence and the chosen Main execution table inside the witness. -/
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
