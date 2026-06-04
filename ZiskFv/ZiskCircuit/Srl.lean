import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.ShiftArchetype

/-!
Compositional SRL spec — `ShiftArchetype` m32=0 sibling of SLL.

SRL mirrors SLL's Main-AIR row exactly (same `m32 = 0` passthrough
bus path, same `is_external_op = 1` to the `BinaryExtension` SM) —
only the `op` literal differs (`OP_SRL = 34` vs `OP_SLL = 33`).
-/

namespace ZiskFv.ZiskCircuit.Srl

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ShiftArchetype


/-- The Main row at `r_main` is in SRL-execution mode: external op with
    opcode literal 34 (`OP_SRL`), full 64-bit width (`m32 = 0`),
    `set_pc = 0`, and `flag = 0`. -/
@[simp]
def main_row_in_srl_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (34 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- Main-side hypotheses for the SRL archetype. -/
@[simp]
def srl_circuit_holds
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_srl_mode m r_main
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Compositional SRL theorem.** Instantiation of the
    `ShiftArchetype` m32=0 archetype macro at `opcode_lit = OP_SRL`. -/
lemma srl_compositional
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : srl_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main := by
  obtain ⟨h1, h2, h3, h_mode, h_match⟩ := h
  obtain ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩ := h_mode
  exact shift_archetype_m32_zero_passthrough_bus m r_main bus_entry OP_SRL
    ⟨h1, h2, h3, ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩, h_match⟩

end ZiskFv.ZiskCircuit.Srl
