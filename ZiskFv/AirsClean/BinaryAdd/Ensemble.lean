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

/-- The minimal BinaryAdd ensemble, assembled up through `addFinishedChannel`:
    the BinaryAdd provider Component + the trivial op-bus consumer, op-bus
    finished. This much of the `Air.Flat` assembly API (`SoundEnsemble` /
    `addTable` / `addFinishedChannel`) provably composes for a real ZisK AIR
    `Component`, with the `addTable` obligations discharged.

    `toFormal` (→ a non-vacuous `FormalEnsemble`) is intentionally NOT taken
    here. It carries an `AssumptionsConsistency` obligation —
    `∀ witness, EnsembleAssumptions witness.publicInput → witness.Assumptions`
    — and `witness.Assumptions` requires *every* BinaryAdd row to satisfy the
    Component's `Assumptions`. BinaryAdd's Component `Assumptions` is
    currently `BinaryAdd.Assumptions` (the 8 column range bounds + 2 carry
    pins), which a `PublicIO := unit` ensemble assumption cannot establish
    non-vacuously. The non-vacuous fix (plan decision D-2): BinaryAdd's
    Component `Assumptions` must become `True`, with the range bounds
    supplied by range-bus *lookup* interactions (channel guarantees), not
    soundness-assumptions. That is range-bus integration — a per-AIR-phase
    step, not part of the op-bus pilot. See the C0c finding. -/
def binaryAddEnsemble : SoundEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable component
        (by simp [circuit_norm, component, circuit, binaryAddElaborated])
        (by simp [circuit_norm, component, circuit, binaryAddElaborated])
    |>.addFinishedChannel OpBusChannel.toRaw
    |>.addTable ⟨ opBusConsumer ⟩
        (by simp [circuit_norm, opBusConsumer])
        (by simp [circuit_norm, opBusConsumer])

end ZiskFv.AirsClean.BinaryAdd
