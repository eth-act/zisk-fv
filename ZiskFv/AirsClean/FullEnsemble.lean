import ZiskFv.AirsClean.Main.Circuit
import ZiskFv.AirsClean.BinaryAdd.Circuit
import ZiskFv.AirsClean.Binary.Circuit
import ZiskFv.AirsClean.BinaryExtension.Circuit
import ZiskFv.AirsClean.BinaryExtension.StaticCircuit
import ZiskFv.AirsClean.ArithMul.Circuit
import ZiskFv.AirsClean.ArithDiv.Circuit
import ZiskFv.AirsClean.Mem.Circuit
import ZiskFv.AirsClean.MemAlign.Circuit
import ZiskFv.AirsClean.MemAlignByte.Circuit
import ZiskFv.AirsClean.MemAlignReadByte.Circuit
import Clean.Air.Vm

/-!
# Full Clean ensemble skeleton

T7 starts from a single ensemble statement for the RV64IM-supported Clean
surface rather than family-local assembly artefacts.  This module assembles
the migrated components that currently exist:

* Main's unified ROM + memory-bus + operation-bus consumer component;
* BinaryAdd plus lookup-aware Binary and BinaryExtension providers;
* lookup-aware ArithMul and ArithDiv row components;
* Mem, MemAlign, MemAlignByte, and MemAlignReadByte memory providers.

This is still not the final T7 theorem.  The Main row is now coherent across
the operation and memory channels, but T7.2/T7.3 must still add the
constructibility statement and re-root canonical theorems before those
theorems may be claimed to be rooted on this ensemble.

## Trust note

No axioms.  This file only composes existing components into a
`FormalEnsemble`; component completeness fields are local constructibility
claims, not sources of cross-row honesty.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- The sound channel-balanced backbone of the full RV64IM Clean ensemble:
    every migrated component added as a table, with the operation and memory
    channels finished. This is the `SoundEnsemble` from which both the formal
    ensemble (`fullRv64imEnsemble`) and the table-soundness discharge
    (`witness_spec_of_constraints`) are derived. -/
def fullRv64imSoundEnsemble (length : ℕ) (program : Program length) :
    SoundEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
        (by simp [circuit_norm,
          ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus,
          ZiskFv.AirsClean.Main.circuitWithRomMemAndOpBus,
          ZiskFv.AirsClean.Main.mainWithRomMemAndOpBusElaborated])
        (by simp [circuit_norm,
          ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus,
          ZiskFv.AirsClean.Main.circuitWithRomMemAndOpBus,
          ZiskFv.AirsClean.Main.mainWithRomMemAndOpBusElaborated])
    |>.addTable ZiskFv.AirsClean.BinaryAdd.component
        (by simp [circuit_norm, ZiskFv.AirsClean.BinaryAdd.component,
          ZiskFv.AirsClean.BinaryAdd.circuit,
          ZiskFv.AirsClean.BinaryAdd.binaryAddElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.BinaryAdd.component,
          ZiskFv.AirsClean.BinaryAdd.circuit,
          ZiskFv.AirsClean.BinaryAdd.binaryAddElaborated])
    |>.addTable ZiskFv.AirsClean.Binary.staticLookupComponent
        (by
          change ([] : List (RawChannel FGL)) ⊆ _
          simp)
        (by
          intro channel h
          simp [circuit_norm] at h)
    |>.addTable ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
        (by
          change ([] : List (RawChannel FGL)) ⊆ _
          simp)
        (by
          intro channel h
          simp [circuit_norm] at h)
    |>.addTable ZiskFv.AirsClean.ArithMul.componentWithArithTable
        (by simp [ZiskFv.AirsClean.ArithMul.componentWithArithTable,
          ZiskFv.AirsClean.ArithMul.circuitWithArithTable,
          ZiskFv.AirsClean.ArithMul.arithMulWithArithTableElaborated])
        (by
          intro channel h
          simp [circuit_norm] at h)
    |>.addTable ZiskFv.AirsClean.ArithDiv.component
        (by simp [circuit_norm, ZiskFv.AirsClean.ArithDiv.component,
          ZiskFv.AirsClean.ArithDiv.circuit,
          ZiskFv.AirsClean.ArithDiv.arithDivElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.ArithDiv.component,
          ZiskFv.AirsClean.ArithDiv.circuit,
          ZiskFv.AirsClean.ArithDiv.arithDivElaborated])
    |>.addTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
        (by simp [circuit_norm, ZiskFv.AirsClean.Mem.componentWithDualMemBus,
          ZiskFv.AirsClean.Mem.circuitWithDualMemBus,
          ZiskFv.AirsClean.Mem.memWithDualMemBusElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.Mem.componentWithDualMemBus,
          ZiskFv.AirsClean.Mem.circuitWithDualMemBus,
          ZiskFv.AirsClean.Mem.memWithDualMemBusElaborated])
    |>.addTable ZiskFv.AirsClean.MemAlign.component
        (by
          change ([] : List (RawChannel FGL)) ⊆ _
          simp)
        (by simp [circuit_norm])
    |>.addTable ZiskFv.AirsClean.MemAlignByte.component
        (by simp [circuit_norm, ZiskFv.AirsClean.MemAlignByte.component,
          ZiskFv.AirsClean.MemAlignByte.circuit,
          ZiskFv.AirsClean.MemAlignByte.memAlignByteElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.MemAlignByte.component,
          ZiskFv.AirsClean.MemAlignByte.circuit,
          ZiskFv.AirsClean.MemAlignByte.memAlignByteElaborated])
    |>.addTable ZiskFv.AirsClean.MemAlignReadByte.component
        (by simp [circuit_norm, ZiskFv.AirsClean.MemAlignReadByte.component,
          ZiskFv.AirsClean.MemAlignReadByte.circuit,
          ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByteElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.MemAlignReadByte.component,
          ZiskFv.AirsClean.MemAlignReadByte.circuit,
          ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByteElaborated])
    |>.addFinishedChannel OpBusChannel.toRaw
    |>.addFinishedChannel MemBusChannel.toRaw

/-- Per-table assumptions discharge for the full ensemble: each migrated
    component's per-row `Assumptions` reduce to `True`, so the ensemble-level
    `AssumptionsConsistency` (and hence `EnsembleWitness.Assumptions`) holds
    against the trivial `fun _ => True` ensemble assumptions. -/
theorem fullRv64imSoundEnsemble_assumptionsConsistency (length : ℕ) (program : Program length) :
    (fullRv64imSoundEnsemble length program).AssumptionsConsistency (fun _ => True) := by
  intro _ _ table h_mem row _
  have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
  clear h_mem
  simp only [fullRv64imSoundEnsemble, circuit_norm, Ensemble.allTables] at h
  rcases h with
    h | h | h | h | h | h | h | h | h | h | h <;>
    (rw [h]
     trivial)

/-- The currently migrated full Clean ensemble for the supported RV64IM
    surface. It finishes the operation and memory channels and includes
    lookup-aware Binary/BinaryExtension providers. Main is represented by
    one row-coherent component exposing both operation-bus and memory-bus
    interactions. -/
def fullRv64imEnsemble (length : ℕ) (program : Program length) :
    FormalEnsemble FGL unit :=
  (fullRv64imSoundEnsemble length program).toFormal (fun _ => True) (fun _ => True)
    (fullRv64imSoundEnsemble_assumptionsConsistency length program)
    (by intro _ _; trivial)

/-- **Discharge of `EnsembleWitness.Spec` from constraints + channel balance.**

    The full ensemble's table-soundness — `witness.Assumptions →
    witness.Constraints → witness.BalancedChannels → witness.Spec` — follows
    from `SoundEnsemble`'s sound finished channels (`tableSoundness_of_soundChannels`).
    The per-table `Assumptions` obligation is the trivial `fun _ => True`
    discharge above. Hence the spec each AIR encodes is *derived* from the
    accepted constraints and balanced channels, not assumed. -/
theorem witness_spec_of_constraints {length : ℕ} {program : Program length}
    (w : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (hc : w.Constraints) (hb : w.BalancedChannels) : w.Spec := by
  have h_sound : (fullRv64imSoundEnsemble length program).ensemble.TableSoundness :=
    Ensemble.tableSoundness_of_soundChannels
      ⟨(fullRv64imSoundEnsemble length program).finished,
       (fullRv64imSoundEnsemble length program).finished_subset,
       (fullRv64imSoundEnsemble length program).soundChannels⟩
  exact h_sound w
    (fullRv64imSoundEnsemble_assumptionsConsistency length program w trivial) hc hb

end ZiskFv.AirsClean.FullEnsemble
