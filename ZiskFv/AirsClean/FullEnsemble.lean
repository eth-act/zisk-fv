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
* ArithMul and ArithDiv row components;
* Mem, MemAlign, MemAlignByte, and MemAlignReadByte memory providers.

This is still not the final T7 theorem.  The Main row is now coherent across
the operation and memory channels, but T7.2/T7.3 must still add the
constructibility statement and re-root canonical theorems before those
theorems may be claimed to be rooted on this ensemble.

## Trust note

No axioms.  This file only composes existing components into a
`FormalEnsemble`; the demoted component completeness fields are visible
non-claims, not source trust.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- The currently migrated full Clean ensemble for the supported RV64IM
    surface. It finishes the operation and memory channels and includes
    lookup-aware Binary/BinaryExtension providers. Main is represented by
    one row-coherent component exposing both operation-bus and memory-bus
    interactions. -/
def fullRv64imEnsemble (length : ℕ) (program : Program length) :
    FormalEnsemble FGL unit :=
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
        (by simp [circuit_norm, ZiskFv.AirsClean.Binary.staticLookupComponent,
          ZiskFv.AirsClean.Binary.staticLookupCircuit,
          ZiskFv.AirsClean.Binary.binaryWithStaticBinaryTableElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.Binary.staticLookupComponent,
          ZiskFv.AirsClean.Binary.staticLookupCircuit,
          ZiskFv.AirsClean.Binary.binaryWithStaticBinaryTableElaborated])
    |>.addTable ZiskFv.AirsClean.BinaryExtension.staticLookupComponent
        (by simp [circuit_norm,
          ZiskFv.AirsClean.BinaryExtension.staticLookupComponent,
          ZiskFv.AirsClean.BinaryExtension.staticLookupCircuit,
          ZiskFv.AirsClean.BinaryExtension.binaryExtensionWithStaticTableElaborated])
        (by simp [circuit_norm,
          ZiskFv.AirsClean.BinaryExtension.staticLookupComponent,
          ZiskFv.AirsClean.BinaryExtension.staticLookupCircuit,
          ZiskFv.AirsClean.BinaryExtension.binaryExtensionWithStaticTableElaborated])
    |>.addTable ZiskFv.AirsClean.ArithMul.component
        (by simp [circuit_norm, ZiskFv.AirsClean.ArithMul.component,
          ZiskFv.AirsClean.ArithMul.circuit,
          ZiskFv.AirsClean.ArithMul.arithMulElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.ArithMul.component,
          ZiskFv.AirsClean.ArithMul.circuit,
          ZiskFv.AirsClean.ArithMul.arithMulElaborated])
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
    |>.toFormal (fun _ => True) (fun _ => True)
        (by
          intro _ _ table h_mem row _
          have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
          clear h_mem
          simp only [circuit_norm, Ensemble.allTables] at h
          rcases h with
            h | h | h | h | h | h | h | h | h | h | h <;>
            (rw [h]
             trivial))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.FullEnsemble
