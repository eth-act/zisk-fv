import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.SailSpec.Auxiliaries

/-!
A `SailTrace` is the Sail side of an `AcceptedZiskTrace`: it supplies the one
thing the circuit witness doesn't contain — the per-instruction sequence of Sail
machine states the program steps through. It is a plain function from an
instruction index to the Sail machine state at that instruction, so applying a
`binding : SailTrace trace` to an index `i` is the state access. Everything about
the Main execution table — which witness table it is, and that it has a row per
instruction — is derived on `AcceptedZiskTrace` (`trace.mainTable*`,
`trace.main_height`/`trace.mainTable_index`), not a `SailTrace` field.
-/

namespace ZiskFv.Compliance

/-- The Sail side of an `AcceptedZiskTrace`: the per-instruction Sail
    machine-state sequence, indexed by instruction. -/
abbrev SailTrace (trace : AcceptedZiskTrace) :=
  Fin trace.numInstructions →
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource

end ZiskFv.Compliance
