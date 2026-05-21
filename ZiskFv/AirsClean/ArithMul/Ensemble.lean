import ZiskFv.AirsClean.ArithMul.Circuit
import Clean.Air.Vm

/-!
# ArithMul minimal ensemble (Phase C3 — D-5)

Assembles ArithMul's Clean `Component` into a minimal `Air.Flat`
ensemble — the ArithMul provider Component plus a deliberately
trivial op-bus consumer, with `OpBusChannel` finished. Proves the
ensemble-assembly API (`SoundEnsemble` / `addTable` /
`addFinishedChannel` / `toFormal`) composes for the ArithMul AIR
Component.

The real op-bus consumer is the Main AIR (a much later phase); the
trivial consumer here stands in for it so C3 can exercise the
assembly end-to-end. Mirrors `AirsClean/BinaryAdd/Ensemble.lean`.
-/

namespace ZiskFv.AirsClean.ArithMul

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

/-- The minimal ArithMul ensemble: the ArithMul provider Component + the
    trivial op-bus consumer, `OpBusChannel` finished, taken all the way
    through `toFormal` to a `FormalEnsemble`.

    `toFormal`'s `AssumptionsConsistency` obligation discharges because both
    Components carry `Assumptions := True` (plan D-2 / F-4 — ArithMul's
    20-clause algebraic Spec follows from its definitional constraints
    alone, no caller assumption). The resulting ensemble soundness is
    genuine — *not* vacuous: its trust closure is the per-Component
    completeness axiom only, no `sorry`, no `False`-style assumption.
    This is the C3 D-5 deliverable. -/
def arithMulEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable component
        (by simp [circuit_norm, component, circuit, arithMulElaborated])
        (by simp [circuit_norm, component, circuit, arithMulElaborated])
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
               component, circuit, opBusConsumer, arithMulElaborated]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.ArithMul
