import ZiskFv.AirsClean.BinaryAdd.Circuit
import Clean.Air.Vm

/-!
# BinaryAdd minimal ensemble (Phase C0c — de-risk pilot)

Assembles BinaryAdd's Clean `Component` into a minimal `Air.Flat` ensemble —
the BinaryAdd provider Component plus a deliberately trivial op-bus consumer,
with `OpBusChannel` finished. Proves the ensemble-assembly API
(`SoundEnsemble` / `addTable` / `addFinishedChannel` / `toFormal`) composes
for a ZisK AIR Component.

The real op-bus consumer is the Main AIR (a much later phase); the trivial
consumer here stands in for it so C0 can exercise the assembly end-to-end.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks
open ZiskFv.Channels.OperationBus
open Air.Flat

/-- A deliberately trivial op-bus consumer: pulls one `OpBusMessage`.
    Stands in for the real Main consumer (a later phase). -/
def opBusConsumer : GeneralFormalCircuit FGL OpBusMessage unit where
  name := "OpBusConsumer"
  main msg := do OpBusChannel.pull msg
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [OpBusChannel.toRaw]
  channelsLawful := by simp only [circuit_norm, OpBusChannel]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [OpBusChannel]
  completeness := by circuit_proof_start [OpBusChannel]

/-- The minimal BinaryAdd ensemble: the BinaryAdd provider Component + the
    trivial op-bus consumer, `OpBusChannel` finished, taken all the way
    through `toFormal` to a `FormalEnsemble`.

    `toFormal`'s `AssumptionsConsistency` obligation discharges because both
    Components carry `Assumptions := True` (plan D-2 — BinaryAdd's column
    range bounds are sourced inside `soundness` from concrete Clean static
    range lookups, not from a caller assumption). The resulting ensemble
    soundness is genuine — not vacuous: its ZiskFv closure contains the
    per-Component completeness axiom, no `range_bus_sound`, no `sorry`, and
    no `False`-style assumption. -/
def binaryAddEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable component
        (by simp [circuit_norm, component, circuit, binaryAddElaborated])
        (by simp [circuit_norm, component, circuit, binaryAddElaborated])
    |>.addFinishedChannel OpBusChannel.toRaw
    |>.addTable ⟨ opBusConsumer ⟩
        (by simp [circuit_norm, opBusConsumer])
        (by simp [circuit_norm, opBusConsumer])
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
               component, circuit, opBusConsumer, binaryAddElaborated]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.BinaryAdd
