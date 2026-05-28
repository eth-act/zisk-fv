import ZiskFv.AirsClean.Main.Circuit
import ZiskFv.AirsClean.Mem.Circuit
import ZiskFv.AirsClean.MemAlign.Circuit
import ZiskFv.AirsClean.MemAlignByte.Circuit
import ZiskFv.AirsClean.MemAlignReadByte.Circuit
import Clean.Air.Vm

/-!
# Memory-family memory-bus ensemble (Phase T4.1)

Memory-family ensemble for the shared memory bus (`MemBusChannel`,
`bus_id = MEMORY_ID = 10`). Assembles the migrated Main consumer-side
component (`Main.componentWithRomAndMemBus` — 3 per-row memory-bus
emissions plus the ZisK instruction ROM lookup) with the Mem,
MemAlign, MemAlignByte, and MemAlignReadByte provider-side components.

Sub-doubleword loads (LB/LH/LW/LBU/LHU/LWU) are handled by the
**MemAlign\*** family on the same unified `MemBusChannel`; the
MemAlign-family provider path is a parallel deliverable in T4.1.

## Trust note

This file introduces no new axioms. The Main and Mem Components
already carry their (soundness-only) completeness axioms in
`AirsClean/Completeness.lean`; this ensemble file only assembles
them. The Main side's `mainWithRomAndMemBus_circuit_completeness`
sits in `trust/tolerated-completeness-axioms.txt` until T4.4 routes
the memory-family canonical theorems through this ensemble.

## Phase T4.1 status

This is the doubleword Main+Mem ensemble. It does NOT by itself
retire `lookup_consumer_matches_provider_load` or any
`main_*_emission_bundle` axiom — those retirements happen at T4.7
once the canonical opcode closures lose them. T4.2 (Clean balance
projects active Main mem-bus rows to concrete Mem provider rows)
is the next step.
-/

namespace ZiskFv.AirsClean.MemFamily

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- The doubleword memory-bus ensemble: Main consumer + Mem provider
    on `MemBusChannel`. Parameterised by the program (the ZisK
    instruction ROM contents) so the same ensemble shape covers any
    compiled program. -/
def memBusEnsemble (length : ℕ) (program : Program length) :
    FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable (ZiskFv.AirsClean.Main.componentWithRomAndMemBus length program)
        (by simp [circuit_norm,
              ZiskFv.AirsClean.Main.componentWithRomAndMemBus,
              ZiskFv.AirsClean.Main.circuitWithRomAndMemBus,
              ZiskFv.AirsClean.Main.mainWithRomAndMemBusElaborated])
        (by simp [circuit_norm,
              ZiskFv.AirsClean.Main.componentWithRomAndMemBus,
              ZiskFv.AirsClean.Main.circuitWithRomAndMemBus,
              ZiskFv.AirsClean.Main.mainWithRomAndMemBusElaborated])
    |>.addTable ZiskFv.AirsClean.Mem.componentWithMemBus
        (by simp [circuit_norm,
              ZiskFv.AirsClean.Mem.componentWithMemBus,
              ZiskFv.AirsClean.Mem.circuitWithMemBus,
              ZiskFv.AirsClean.Mem.memWithMemBusElaborated])
        (by simp [circuit_norm,
              ZiskFv.AirsClean.Mem.componentWithMemBus,
              ZiskFv.AirsClean.Mem.circuitWithMemBus,
              ZiskFv.AirsClean.Mem.memWithMemBusElaborated])
    |>.addTable ZiskFv.AirsClean.MemAlign.component
        (by simp [circuit_norm,
              ZiskFv.AirsClean.MemAlign.component,
              ZiskFv.AirsClean.MemAlign.circuit,
              ZiskFv.AirsClean.MemAlign.memAlignWithMemBusElaborated])
        (by simp [circuit_norm,
              ZiskFv.AirsClean.MemAlign.component,
              ZiskFv.AirsClean.MemAlign.circuit,
              ZiskFv.AirsClean.MemAlign.memAlignWithMemBusElaborated])
    |>.addTable ZiskFv.AirsClean.MemAlignByte.component
        (by simp [circuit_norm,
              ZiskFv.AirsClean.MemAlignByte.component,
              ZiskFv.AirsClean.MemAlignByte.circuit,
              ZiskFv.AirsClean.MemAlignByte.memAlignByteElaborated])
        (by simp [circuit_norm,
              ZiskFv.AirsClean.MemAlignByte.component,
              ZiskFv.AirsClean.MemAlignByte.circuit,
              ZiskFv.AirsClean.MemAlignByte.memAlignByteElaborated])
    |>.addTable ZiskFv.AirsClean.MemAlignReadByte.component
        (by simp [circuit_norm,
              ZiskFv.AirsClean.MemAlignReadByte.component,
              ZiskFv.AirsClean.MemAlignReadByte.circuit,
              ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByteElaborated])
        (by simp [circuit_norm,
              ZiskFv.AirsClean.MemAlignReadByte.component,
              ZiskFv.AirsClean.MemAlignReadByte.circuit,
              ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByteElaborated])
    |>.addFinishedChannel MemBusChannel.toRaw
    |>.toFormal (fun _ => True) (fun _ => True)
        (by
          intro _ _ table h_mem row _
          have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
          clear h_mem
          simp only [circuit_norm, Ensemble.allTables] at h
          -- Components appear newest-first after the verifier table.
          rcases h with h | h | h | h | h | h <;>
            (rw [h]
             simp [circuit_norm, Air.Flat.Component.Assumptions,
               ZiskFv.AirsClean.MemAlignReadByte.component,
               ZiskFv.AirsClean.MemAlignReadByte.circuit,
               ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByteElaborated,
               ZiskFv.AirsClean.MemAlignByte.component,
               ZiskFv.AirsClean.MemAlignByte.circuit,
               ZiskFv.AirsClean.MemAlignByte.memAlignByteElaborated,
               ZiskFv.AirsClean.MemAlign.component,
               ZiskFv.AirsClean.MemAlign.circuit,
               ZiskFv.AirsClean.MemAlign.memAlignWithMemBusElaborated,
               ZiskFv.AirsClean.Mem.componentWithMemBus,
               ZiskFv.AirsClean.Mem.circuitWithMemBus,
               ZiskFv.AirsClean.Mem.memWithMemBusElaborated,
               ZiskFv.AirsClean.Main.componentWithRomAndMemBus,
               ZiskFv.AirsClean.Main.circuitWithRomAndMemBus,
               ZiskFv.AirsClean.Main.mainWithRomAndMemBusElaborated]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.MemFamily
