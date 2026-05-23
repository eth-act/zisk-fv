import ZiskFv.AirsClean.Mem.Circuit
import Clean.Air.Vm

/-!
# Mem minimal ensemble (Phase C8)

Assembles Mem's Clean `Component` into a minimal `Air.Flat` ensemble. The
memory-bus provider/consumer composition is terminal C10 work.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open Air.Flat

def memEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable component
        (by simp [circuit_norm, component, circuit, memElaborated])
        (by simp [circuit_norm, component, circuit, memElaborated])
    |>.toFormal (fun _ => True) (fun _ => True)
        (by
          intro _ _ table h_mem row _
          have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
          simp only [circuit_norm, Ensemble.allTables] at h
          rcases h with h | h <;>
            (rw [h]
             simp [circuit_norm, Air.Flat.Component.Assumptions,
               component, circuit, memElaborated]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.Mem
