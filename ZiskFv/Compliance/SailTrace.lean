import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.SailSpec.Auxiliaries

/-!
A `SailTrace` is the Sail side of an `AcceptedZiskTrace`: the per-executed-step
sequence of Sail machine states. It depends only on the executed-step count
(`AcceptedZiskTrace.numInstructions`), not the whole trace — so
it is a plain function from an instruction index to the Sail machine state, and
applying a `binding : SailTrace n` to an index `i : Fin n` is the state access.
Everything about the Main execution table — which witness table it is, and that it
has a row per executed step — is derived on `AcceptedZiskTrace`, not a `SailTrace`
field.
-/

namespace ZiskFv.Compliance

/-- The Sail side of an `AcceptedZiskTrace`: the per-executed-step Sail
    machine-state sequence, indexed by executed step. Parameterized by the
    executed-step count (pass `trace.numInstructions`), not the trace itself. -/
abbrev SailTrace (numInstructions : Nat) :=
  Fin numInstructions →
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource

end ZiskFv.Compliance
