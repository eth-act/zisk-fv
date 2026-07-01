import ZiskFv.ZiskCircuit.MemTimeline.CoherenceSpike
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Channels.StateEffect

/-!
# Issue #115 Phase-A make-or-break — derive the load memory equation in-export (scratch)

**Exploratory (Phase A of the #115 rewire plan). Built via explicit target, NOT added to the ZiskFv
aggregator. No axioms, no `sorry` at completion.**

Goal: show that `state.mem = replayMemoryAfterBusRows initialMemory priorRows` — the single residual
`CoherenceSpike.loadEvidence_of_loadMemReplay` consumes — is derivable from accepted-trace data plus a
named memory-coherence premise, rather than caller-supplied per load.

Step 1 (this file, first): the store-mem projection — one width-independent lemma that the fold uses
to know what each prior store wrote into the Sail memory. `bus_effect`'s `as=2/mult=1` write branch is
definitionally `writeMemoryOfEntry`, isolated by `bus_effect_matches_sail_store_rrrw`.
-/

namespace ZiskFv.ZiskCircuit.MemTimeline.TraceMemDerivation

open Goldilocks
open Interaction
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Airs.Bus

/-- Memory of the post-state of a Sail execution result (`none` on error). The fold only cares about
the memory component, so this ignores `regs`/`nextPC`. -/
def resultMem
    (r : EStateM.Result (Sail.Error exception)
      (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult) :
    Option (Std.ExtHashMap Nat (BitVec 8)) :=
  match r with
  | .ok _ s => some s.mem
  | .error _ _ => none

/-- **Store-mem projection.** For any store-shaped bus emission (two register-read entries `e0,e1`
and one memory-write entry `e2`), the post-state memory of `bus_effect` is exactly
`writeMemoryOfEntry state.mem e2`. Width-independent: the `as=2` branch always writes the full eight
lanes; narrow-store width lives on the Sail side, not here. -/
theorem store_bus_effect_mem
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val)) = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) :
    resultMem (bus_effect exec_row [e0, e1, e2] state).2
      = some (writeMemoryOfEntry state.mem e2) := by
  rw [BusEmission.bus_effect_matches_sail_store_rrrw state exec_row e0 e1 e2 nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [resultMem, writeMemoryOfEntry, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure, EStateM.bind, EStateM.pure]

#print axioms store_bus_effect_mem

end ZiskFv.ZiskCircuit.MemTimeline.TraceMemDerivation
