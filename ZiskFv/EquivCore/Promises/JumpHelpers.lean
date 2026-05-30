import Mathlib

import ZiskFv.EquivCore.Promises.Jump
import ZiskFv.ZiskCircuit.Jal
import ZiskFv.ZiskCircuit.Jalr
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `JumpPromises` companion helpers

For each JUMP opcode (JAL, JALR), provides a single helper that
assembles `h_circuit` — the `<op>_circuit_holds` term that
`equiv_<OP>` accepts alongside the structural `JumpPromises`
bundle — from the Main-AIR activation pin, opcode pin, and per-row
subset constraint.

The helper internally fires `transpile_<OP>` (class #1) to derive the
routing pins, then packs them with the subset hypothesis. Extracted
from the per-opcode `Compliance/Wrappers/<Op>.lean` wrappers.
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted
open ZiskFv.Airs.Main


/-- Assemble JAL's `h_circuit` from the Main-side activation/opcode
    pins and the per-row JAL subset constraint. -/
def jal_h_circuit_of_main_constraints
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_jal : m.op r_main = OP_FLAG)
    (h_jal_subset : ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc) :
    ZiskFv.ZiskCircuit.Jal.jal_circuit_holds m r_main next_pc :=
  let h_tr := ZiskFv.Trusted.transpile_JAL m r_main (0 : Fin 32)
    (0 : FGL) { xreg := fun _ => 0#64, pc := 0#64 }
    h_main_active h_main_op_jal
  let ⟨h_m32, h_set_pc, h_store_pc, _, _, _, _, _, _⟩ := h_tr
  let h_jal_mode : ZiskFv.ZiskCircuit.Jal.main_row_in_jal_mode m r_main :=
    ⟨h_main_active, by rw [h_main_op_jal]; rfl, h_m32, h_set_pc, h_store_pc⟩
  ⟨h_jal_subset, h_jal_mode⟩

/-- Assemble JALR's `h_circuit` from the Main-side activation/opcode
    pins and the per-row JALR subset constraint. -/
def jalr_h_circuit_of_main_constraints
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_jalr : m.op r_main = OP_AND)
    (h_jalr_subset :
      ZiskFv.Airs.Main.flag_boolean m r_main
      ∧ ZiskFv.Airs.Main.is_external_op_boolean m r_main
      ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m r_main
      ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m r_main next_pc) :
    ZiskFv.ZiskCircuit.Jalr.jalr_circuit_holds m r_main next_pc := by
  have h_tr := ZiskFv.Trusted.transpile_JALR m r_main (0 : Fin 32) (0 : Fin 32)
    (0 : FGL) { xreg := fun _ => 0#64, pc := 0#64 }
    h_main_active h_main_op_jalr
  obtain ⟨h_flag, h_m32, h_set_pc, h_store_pc, _, _⟩ := h_tr
  obtain ⟨h_flag_bool, h_ext_bool, h_disjoint, h_pc⟩ := h_jalr_subset
  refine ⟨h_flag_bool, h_ext_bool, h_disjoint, h_pc, ?_⟩
  · refine ⟨h_main_active, ?_, h_flag, h_m32, h_set_pc, h_store_pc⟩
    exact h_main_op_jalr

end ZiskFv.EquivCore.Promises
