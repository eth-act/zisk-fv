import ZiskFv.AirsClean.MemAlignReadByte.Circuit
import Clean.Air.Vm

/-!
# MemAlignReadByte minimal ensemble (Phase C2 — D-5)

Assembles MemAlignReadByte's Clean `Component` into a minimal `Air.Flat`
ensemble — the MemAlignReadByte provider Component plus a deliberately
trivial memory-bus consumer, with `MemBusChannel` finished. Proves
the ensemble-assembly API (`SoundEnsemble` / `addTable` /
`addFinishedChannel` / `toFormal`) composes for the MemAlignReadByte AIR
Component.

The real memory-bus consumer is the Main AIR (a much later phase); the
trivial consumer here stands in for it so C2 can exercise the assembly
end-to-end. Mirrors `AirsClean/MemAlignByte/Ensemble.lean`.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks
open ZiskFv.Channels.MemoryBus
open Air.Flat

/-- A deliberately trivial memory-bus consumer: pulls one
    `MemBusMessage`. Stands in for the real Main consumer (a
    later phase). -/
def memAlignBusConsumer : GeneralFormalCircuit FGL MemBusMessage unit where
  name := "MemAlignReadByteBusConsumer"
  main msg := do MemBusChannel.pull msg
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [MemBusChannel.toRaw]
  channelsLawful := by simp only [circuit_norm, MemBusChannel]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [MemBusChannel]
  completeness := by circuit_proof_start [MemBusChannel]

/-- The minimal MemAlignReadByte ensemble: the MemAlignReadByte provider
    Component + the trivial memory-bus consumer, `MemBusChannel`
    finished, taken all the way through `toFormal` to a `FormalEnsemble`.

    `toFormal`'s `AssumptionsConsistency` obligation discharges because both
    Components carry `Assumptions := True` (plan D-2 / F-4 — MemAlignReadByte's
    algebraic Spec follows from its definitional constraint alone, no caller
    assumption). The resulting ensemble soundness is genuine — *not* vacuous:
    its trust closure is the per-Component completeness axiom only, no
    `sorry`, no `False`-style assumption. This is the C2 D-5 deliverable. -/
def memAlignReadByteEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable component
        (by simp [circuit_norm, component, circuit, memAlignReadByteElaborated])
        (by simp [circuit_norm, component, circuit, memAlignReadByteElaborated])
    |>.addFinishedChannel MemBusChannel.toRaw
    |>.addTable ⟨ memAlignBusConsumer ⟩
        (by simp [circuit_norm, memAlignBusConsumer])
        (by simp [circuit_norm, memAlignBusConsumer])
    |>.toFormal (fun _ => True) (fun _ => True)
        (by
          -- AssumptionsConsistency: every component carries `Assumptions := True`,
          -- so every witness table's per-row assumption is `True`.
          intro _ _ table h_mem row _
          have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
          simp only [circuit_norm, Ensemble.allTables] at h
          rcases h with h | h | h <;>
            (rw [h]
             simp [circuit_norm, Air.Flat.Component.Assumptions,
               component, circuit, memAlignBusConsumer, memAlignReadByteElaborated]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.MemAlignReadByte
