import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.ShiftArchetype

/-!
Compositional SRAI spec — `ShiftArchetype` m32=0 immediate sibling
of SRA. Structurally identical to `Circuit.Sra`; see `Circuit.Slli` for
why SRA and SRAI share their Zisk opcode.
-/

namespace ZiskFv.Circuit.Srai

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ShiftArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in SRAI-execution mode. Same as
    `Circuit.Sra.main_row_in_sra_mode` — SRA and SRAI map to the same
    Zisk opcode (`OP_SRA = 35`, `m32 = 0`). -/
@[simp]
def main_row_in_srai_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (35 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- Main-side hypotheses for the SRAI archetype. -/
@[simp]
def srai_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_srai_mode m r_main
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Compositional SRAI theorem.** Instantiation of the
    `ShiftArchetype` m32=0 archetype macro at `opcode_lit = OP_SRA`. -/
theorem srai_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : srai_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main := by
  obtain ⟨h1, h2, h3, h_mode, h_match⟩ := h
  obtain ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩ := h_mode
  exact shift_archetype_m32_zero_passthrough_bus m r_main bus_entry OP_SRA
    ⟨h1, h2, h3, ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩, h_match⟩

end ZiskFv.Circuit.Srai
