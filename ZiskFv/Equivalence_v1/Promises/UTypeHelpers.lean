import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Equivalence_v1.Promises.UType
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `UTypePromises` companion helpers

For each U-TYPE opcode (LUI, AUIPC), provides a single helper that
assembles `h_circuit` — the `<op>_archetype_circuit_holds` term that
`equiv_<OP>` accepts alongside the structural `UTypePromises`
bundle — from three trust-ledger-style ingredients: the Main-AIR
activation pin, the opcode pin, and the per-row constraint subset.

The helper internally fires `transpile_<OP>` (class #1) to derive
the `m32`, `set_pc`, `store_pc` routing pins, then packs them
together with the subset hypothesis. Extracted from the per-opcode
`Compliance/Wrappers/<Op>.lean` wrappers.
-/

namespace ZiskFv.Equivalence_v1.Promises

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- Assemble LUI's `h_circuit` from the Main-side activation/opcode
    pins and the per-row LUI subset constraint. -/
def lui_h_circuit_of_main_constraints
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_lui : m.op r_main = OP_COPYB)
    (h_lui_subset : lui_subset_holds m r_main next_pc) :
    lui_archetype_circuit_holds m r_main next_pc :=
  let h_tr := ZiskFv.Trusted.transpile_LUI m r_main (0 : Fin 32)
    (0 : FGL) (0 : FGL)
    { xreg := fun _ => 0#64, pc := 0#64 } h_main_active h_main_op_lui
  let ⟨h_m32, h_set_pc, h_store_pc, _, _, _, _, _, _⟩ := h_tr
  let h_lui_mode : main_row_in_lui_mode m r_main :=
    ⟨h_main_active, by rw [h_main_op_lui]; rfl, h_m32, h_set_pc, h_store_pc⟩
  ⟨h_lui_subset, h_lui_mode⟩

/-- Assemble AUIPC's `h_circuit` from the Main-side activation/opcode
    pins and the per-row AUIPC subset constraint. -/
def auipc_h_circuit_of_main_constraints
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_auipc : m.op r_main = OP_FLAG)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc) :
    auipc_archetype_circuit_holds m r_main next_pc :=
  let h_tr := ZiskFv.Trusted.transpile_AUIPC m r_main (0 : Fin 32)
    (0 : FGL) { xreg := fun _ => 0#64, pc := 0#64 }
    h_main_active h_main_op_auipc
  let ⟨h_m32, h_set_pc, h_store_pc, _, _, _, _, _, _⟩ := h_tr
  let h_auipc_mode : main_row_in_auipc_mode m r_main :=
    ⟨h_main_active, by rw [h_main_op_auipc]; rfl, h_m32, h_set_pc, h_store_pc⟩
  ⟨h_auipc_subset, h_auipc_mode⟩

end ZiskFv.Equivalence_v1.Promises
