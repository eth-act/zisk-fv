import ZiskFv.AirsClean.Main.Circuit
import ZiskFv.AirsClean.BinaryAdd.Circuit
import ZiskFv.AirsClean.Binary.Circuit
import ZiskFv.AirsClean.BinaryExtension.Circuit
import ZiskFv.AirsClean.BinaryExtension.StaticCircuit
import ZiskFv.AirsClean.ArithMul.Circuit
import ZiskFv.AirsClean.ArithDiv.Circuit
import ZiskFv.AirsClean.Mem.Circuit
import ZiskFv.AirsClean.SpecifiedRangesSlice
import ZiskFv.AirsClean.MemAlign.Circuit
import ZiskFv.AirsClean.MemAlignRomSlice
import ZiskFv.AirsClean.MemAlignRangeSlice
import ZiskFv.AirsClean.MemAlignByte.Circuit
import ZiskFv.AirsClean.MemAlignReadByte.Circuit
import ZiskFv.AirsClean.RegisterBoundary
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
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

private theorem specifiedRangesSliceChannel_ne_memBus :
    SpecifiedRangesSliceChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "MemoryBus" at h_name
  simp at h_name

private theorem specifiedRangesSliceChannel_ne_memAlignRom :
    SpecifiedRangesSliceChannel.toRaw ≠ MemAlignRomChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "MemAlignRom133" at h_name
  simp at h_name

private theorem specifiedRangesSliceChannel_ne_memAlignRange :
    SpecifiedRangesSliceChannel.toRaw ≠ MemAlignRangeChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "SpecifiedRangesSlice103" = "MemAlignRange107" at h_name
  simp at h_name

private theorem memAlignRomChannel_ne_memBus :
    MemAlignRomChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun raw : RawChannel FGL => raw.name) h
  change "MemAlignRom133" = "MemoryBus" at h_name
  simp at h_name

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
    |>.addTable ZiskFv.AirsClean.ArithMul.componentComplete
        (by simp [ZiskFv.AirsClean.ArithMul.componentComplete,
          ZiskFv.AirsClean.ArithMul.circuitComplete,
          ZiskFv.AirsClean.ArithMul.arithMulCompleteElaborated])
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
    |>.addTable ZiskFv.AirsClean.SpecifiedRangesSlice.component
        (by
          change ([] : List (RawChannel FGL)) ⊆ _
          simp)
        (by
          intro channel h
          simp [circuit_norm] at h)
    |>.addTable ZiskFv.AirsClean.Mem.componentWithDualMemBus
        (by simp [circuit_norm, ZiskFv.AirsClean.Mem.componentWithDualMemBus,
          ZiskFv.AirsClean.Mem.circuitWithDualMemBus])
        (by simp [circuit_norm, ZiskFv.AirsClean.Mem.componentWithDualMemBus,
          ZiskFv.AirsClean.Mem.circuitWithDualMemBus])
    |>.addFinishedChannel SpecifiedRangesSliceChannel.toRaw
    |>.addTable ZiskFv.AirsClean.MemAlignRomSlice.component
        (by
          change ([] : List (RawChannel FGL)) ⊆ _
          simp)
        (by
          intro channel h
          change channel ∈ [SpecifiedRangesSliceChannel.toRaw] at h
          have h_range : channel = SpecifiedRangesSliceChannel.toRaw := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
          subst channel
          change SpecifiedRangesSliceChannel.toRaw ∉ [MemAlignRomChannel.toRaw]
          intro h_channel
          apply specifiedRangesSliceChannel_ne_memAlignRom
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using h_channel)
    |>.addTable ZiskFv.AirsClean.MemAlignRangeSlice.component
        (by
          change ([] : List (RawChannel FGL)) ⊆ _
          simp)
        (by
          intro channel h
          change channel ∈ [SpecifiedRangesSliceChannel.toRaw] at h
          have h_range : channel = SpecifiedRangesSliceChannel.toRaw := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
          subst channel
          change SpecifiedRangesSliceChannel.toRaw ∉ [MemAlignRangeChannel.toRaw]
          intro h_channel
          apply specifiedRangesSliceChannel_ne_memAlignRange
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using h_channel)
    |>.addTable ZiskFv.AirsClean.MemAlign.component
        (by
          change ([] : List (RawChannel FGL)) ⊆ _
          simp)
        (by
          intro channel h
          change channel ∈ [SpecifiedRangesSliceChannel.toRaw] at h
          have h_range : channel = SpecifiedRangesSliceChannel.toRaw := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
          subst channel
          change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw,
            MemAlignRomChannel.toRaw, MemAlignRangeChannel.toRaw]
          intro h_channel
          have h_channel' : SpecifiedRangesSliceChannel.toRaw = MemBusChannel.toRaw ∨
              SpecifiedRangesSliceChannel.toRaw = MemAlignRomChannel.toRaw ∨
              SpecifiedRangesSliceChannel.toRaw = MemAlignRangeChannel.toRaw := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using h_channel
          rcases h_channel' with h_channel | h_channel | h_channel
          · exact specifiedRangesSliceChannel_ne_memBus h_channel
          · exact specifiedRangesSliceChannel_ne_memAlignRom h_channel
          · exact specifiedRangesSliceChannel_ne_memAlignRange h_channel)
    |>.addFinishedChannel MemAlignRomChannel.toRaw
    |>.addTable ZiskFv.AirsClean.MemAlignByte.component
        (by simp [circuit_norm, ZiskFv.AirsClean.MemAlignByte.component,
          ZiskFv.AirsClean.MemAlignByte.circuit,
          ZiskFv.AirsClean.MemAlignByte.memAlignByteElaborated])
        (by
          intro channel h_finished h_memBus
          have h_finished_list : channel ∈ [MemAlignRomChannel.toRaw,
              SpecifiedRangesSliceChannel.toRaw] := by
            simpa [circuit_norm, ZiskFv.AirsClean.MemAlignByte.component,
              ZiskFv.AirsClean.MemAlignByte.circuit,
              ZiskFv.AirsClean.MemAlignByte.memAlignByteElaborated] using h_finished
          have h_memBus_list : channel ∈ [MemBusChannel.toRaw] := by
            simpa [circuit_norm, ZiskFv.AirsClean.MemAlignByte.component,
              ZiskFv.AirsClean.MemAlignByte.circuit,
              ZiskFv.AirsClean.MemAlignByte.memAlignByteElaborated] using h_memBus
          have h_finished' : channel = MemAlignRomChannel.toRaw ∨
              channel = SpecifiedRangesSliceChannel.toRaw := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using h_finished_list
          have h_memBus' : channel = MemBusChannel.toRaw := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using h_memBus_list
          subst channel
          rcases h_finished' with h_finished | h_finished
          · exact memAlignRomChannel_ne_memBus h_finished.symm
          · exact specifiedRangesSliceChannel_ne_memBus h_finished.symm)
    |>.addTable ZiskFv.AirsClean.MemAlignReadByte.component
        (by simp [circuit_norm, ZiskFv.AirsClean.MemAlignReadByte.component,
          ZiskFv.AirsClean.MemAlignReadByte.circuit,
          ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByteElaborated])
        (by
          intro channel h_finished h_memBus
          have h_finished_list : channel ∈ [MemAlignRomChannel.toRaw,
              SpecifiedRangesSliceChannel.toRaw] := by
            simpa [circuit_norm, ZiskFv.AirsClean.MemAlignReadByte.component,
              ZiskFv.AirsClean.MemAlignReadByte.circuit,
              ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByteElaborated] using h_finished
          have h_memBus_list : channel ∈ [MemBusChannel.toRaw] := by
            simpa [circuit_norm, ZiskFv.AirsClean.MemAlignReadByte.component,
              ZiskFv.AirsClean.MemAlignReadByte.circuit,
              ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByteElaborated] using h_memBus
          have h_finished' : channel = MemAlignRomChannel.toRaw ∨
              channel = SpecifiedRangesSliceChannel.toRaw := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using h_finished_list
          have h_memBus' : channel = MemBusChannel.toRaw := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using h_memBus_list
          subst channel
          rcases h_finished' with h_finished | h_finished
          · exact memAlignRomChannel_ne_memBus h_finished.symm
          · exact specifiedRangesSliceChannel_ne_memBus h_finished.symm)
    |>.addTable ZiskFv.AirsClean.RegisterBoundary.component
        (by simp [circuit_norm, ZiskFv.AirsClean.RegisterBoundary.component,
          ZiskFv.AirsClean.RegisterBoundary.circuit,
          ZiskFv.AirsClean.RegisterBoundary.registerBoundaryElaborated])
        (by
          intro channel h_finished h_memBus
          have h_finished_list : channel ∈ [MemAlignRomChannel.toRaw,
              SpecifiedRangesSliceChannel.toRaw] := by
            simpa [circuit_norm, ZiskFv.AirsClean.RegisterBoundary.component,
              ZiskFv.AirsClean.RegisterBoundary.circuit,
              ZiskFv.AirsClean.RegisterBoundary.registerBoundaryElaborated] using h_finished
          have h_memBus_list : channel ∈ [MemBusChannel.toRaw] := by
            simpa [circuit_norm, ZiskFv.AirsClean.RegisterBoundary.component,
              ZiskFv.AirsClean.RegisterBoundary.circuit,
              ZiskFv.AirsClean.RegisterBoundary.registerBoundaryElaborated] using h_memBus
          have h_finished' : channel = MemAlignRomChannel.toRaw ∨
              channel = SpecifiedRangesSliceChannel.toRaw := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using h_finished_list
          have h_memBus' : channel = MemBusChannel.toRaw := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using h_memBus_list
          subst channel
          rcases h_finished' with h_finished | h_finished
          · exact memAlignRomChannel_ne_memBus h_finished.symm
          · exact specifiedRangesSliceChannel_ne_memBus h_finished.symm)
    |>.addFinishedChannel OpBusChannel.toRaw
    |>.addFinishedChannel MemBusChannel.toRaw
    |>.addFinishedChannel MemAlignRangeChannel.toRaw

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
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
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
