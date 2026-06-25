import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.SailSpec.Auxiliaries

/-!
A `SailTrace` is the Sail side of an `AcceptedZiskTrace`: the per-instruction
sequence of Sail machine states the program steps through. It depends only on the
instruction count (`AcceptedZiskTrace.numInstructions`), not the whole trace — so
it is a plain function from an instruction index to the Sail machine state, and
applying a `binding : SailTrace n` to an index `i : Fin n` is the state access.
Everything about the Main execution table — which witness table it is, and that it
has a row per instruction — is derived on `AcceptedZiskTrace`, not a `SailTrace`
field.
-/

namespace ZiskFv.Compliance

/-- The Sail side of an `AcceptedZiskTrace`: the per-instruction Sail
    machine-state sequence, indexed by instruction. Parameterized by the
    instruction count (pass `trace.numInstructions`), not the trace itself. -/
abbrev SailTrace (numInstructions : Nat) :=
  Fin numInstructions →
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource

end ZiskFv.Compliance
