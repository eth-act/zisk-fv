import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.ShiftArchetype

/-!
Compositional SLLIW spec — `ShiftArchetype` sibling, W-variant
immediate.

SLLIW's Main-AIR row mirrors SLLW's exactly (same `op = OP_SLL_W = 36`,
same `m32 = 1` bus path, same `is_external_op = 1` to the
`BinaryExtension` SM). The only difference is **operand routing**:
`transpile_SLLIW` emits `b_lo = shamt_w_b_lo shamt` (immediate source)
where `transpile_SLLW` emits `b_lo = lane_lo (state.xreg rs2)` (register
source). Since the `ShiftArchetype` m32=1 macro theorem is
`b_lo`-source-agnostic (it reasons only about `bus_entry.b_hi` /
`opBus_row_Main` via the `(1 - m32) * b[1]` PIL collapse, not about
where the low lane came from), the same archetype instance closes
SLLIW with no macro changes.

This module instantiates `Tactics.ShiftArchetype` for SLLIW at
`opcode_lit = OP_SLL_W`, producing the analogue of
`Circuit.Shift.sllw_compositional`.
-/

namespace ZiskFv.ZiskCircuit.ShiftLI

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ShiftArchetype


/-- The Main row at `r_main` is in SLLIW-execution mode. Identical to
    SLLW mode (same opcode literal `OP_SLL_W = 36`, same `m32 = 1`,
    same selectors): the immediate-vs-register distinction lives on
    `b_lo`, not on the mode-predicate columns. -/
@[simp]
def main_row_in_slliw_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (36 : FGL)
  ∧ m.m32 r_main = 1
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- Main-side hypotheses for the SLLIW archetype. Shape identical to
    `Circuit.Shift.sllw_circuit_holds` modulo the mode-predicate name. -/
@[simp]
def slliw_circuit_holds
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_slliw_mode m r_main
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Compositional SLLIW theorem.** Instantiation of the
    `ShiftArchetype` m32=1 archetype macro at `opcode_lit = OP_SLL_W`
    (same opcode as SLLW; the bus shape doesn't distinguish
    immediate-vs-register source). -/
lemma slliw_compositional
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : slliw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 := by
  obtain ⟨h1, h2, h3, h_mode, h_match⟩ := h
  obtain ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩ := h_mode
  exact shift_archetype_m32_one_zeros_bus m r_main bus_entry OP_SLL_W
    ⟨h1, h2, h3, ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩, h_match⟩

end ZiskFv.ZiskCircuit.ShiftLI
