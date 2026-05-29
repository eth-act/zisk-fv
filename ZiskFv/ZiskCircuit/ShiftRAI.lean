import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.ShiftArchetype

/-!
Compositional SRAIW spec — `ShiftArchetype` sibling, W-variant
immediate.

SRAIW's Main-AIR row mirrors SRAW's exactly (same `op = OP_SRA_W = 38`,
same `m32 = 1` bus path); the only difference vs SRAW is the source of
`b_lo` (immediate vs register). The `ShiftArchetype` m32=1 macro is
`b_lo`-source-agnostic, so the same instantiation closes SRAIW.
-/

namespace ZiskFv.ZiskCircuit.ShiftRAI

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ShiftArchetype


/-- The Main row at `r_main` is in SRAIW-execution mode. Identical to
    SRAW mode. -/
@[simp]
def main_row_in_sraiw_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (38 : FGL)
  ∧ m.m32 r_main = 1
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

@[simp]
def sraiw_circuit_holds
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_sraiw_mode m r_main
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Compositional SRAIW theorem.** Instantiation of the
    `ShiftArchetype` m32=1 archetype macro at `opcode_lit = OP_SRA_W`. -/
lemma sraiw_compositional
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : sraiw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 := by
  obtain ⟨h1, h2, h3, h_mode, h_match⟩ := h
  obtain ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩ := h_mode
  exact shift_archetype_m32_one_zeros_bus m r_main bus_entry OP_SRA_W
    ⟨h1, h2, h3, ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩, h_match⟩

end ZiskFv.ZiskCircuit.ShiftRAI
