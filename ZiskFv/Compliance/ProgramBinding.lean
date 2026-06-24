import ZiskFv.Compliance.AcceptedTrace.MainTable
import ZiskFv.SailSpec.Auxiliaries

/-!
A `ProgramBinding` supplies the one thing the circuit witness doesn't contain: the
sequence of Sail machine states the program steps through (`stateAt`). Everything
about the Main execution table — which witness table it is, and that it has a row
per instruction — is now derived on `AcceptedTrace` (`trace.mainTable*`,
`trace.main_height`/`trace.mainTable_index`), no longer a `ProgramBinding` field.
-/

namespace ZiskFv.Compliance

/-- Binds an `AcceptedTrace` to a concrete program run: the per-instruction Sail
    machine-state sequence. -/
structure ProgramBinding (trace : AcceptedTrace) where
  stateAt :
    Fin trace.numInstructions →
      PreSail.SequentialState RegisterType Sail.trivialChoiceSource

end ZiskFv.Compliance
