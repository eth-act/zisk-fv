import ZiskFv.AirsClean.MemAlignByte.Circuit
import Clean.Air.Vm

/-!
# MemAlignByte minimal ensemble (Phase C1 — D-5)

Assembles MemAlignByte's Clean `Component` into a minimal `Air.Flat`
ensemble — the MemAlignByte provider Component plus a deliberately
trivial memory-bus consumer, with `MemAlignBusChannel` finished.
Proves the ensemble-assembly API (`SoundEnsemble` / `addTable` /
`addFinishedChannel` / `toFormal`) composes for the MemAlignByte AIR
Component.

The real memory-bus consumer is the Main AIR (a much later phase);
the trivial consumer here stands in for it so C1 can exercise the
assembly end-to-end. Mirrors `AirsClean/BinaryAdd/Ensemble.lean`.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks
open ZiskFv.Channels.MemAlignBus
open Air.Flat

/-- A deliberately trivial memory-bus consumer: pulls one
    `MemAlignBusMessage`. Stands in for the real Main consumer (a
    later phase). -/
def memAlignBusConsumer : GeneralFormalCircuit FGL MemAlignBusMessage unit where
  name := "MemAlignBusConsumer"
  main msg := do MemAlignBusChannel.pull msg
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [MemAlignBusChannel.toRaw]
  channelsLawful := by simp only [circuit_norm, MemAlignBusChannel]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [MemAlignBusChannel]
  completeness := by circuit_proof_start [MemAlignBusChannel]

/-- The minimal MemAlignByte ensemble: the MemAlignByte provider Component
    + the trivial memory-bus consumer, `MemAlignBusChannel` finished, taken
    all the way through `toFormal` to a `FormalEnsemble`.

    `toFormal`'s `AssumptionsConsistency` obligation discharges because both
    Components carry `Assumptions := True` (plan D-2 / F-4 — MemAlignByte's
    algebraic Spec follows from its definitional constraints alone, no caller
    assumption). The resulting ensemble soundness is genuine — *not* vacuous:
    its trust closure is the per-Component completeness axiom only, no
    `sorry`, no `False`-style assumption. This is the C1 D-5 deliverable. -/
def memAlignByteEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable component
        (by simp [circuit_norm, component, circuit, memAlignByteElaborated])
        (by simp [circuit_norm, component, circuit, memAlignByteElaborated])
    |>.addFinishedChannel MemAlignBusChannel.toRaw
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
               component, circuit, memAlignBusConsumer, memAlignByteElaborated]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.MemAlignByte
