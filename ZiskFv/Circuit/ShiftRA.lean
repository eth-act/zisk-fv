import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.ShiftArchetype

/-!
Compositional SRAW spec — `ShiftArchetype` sibling of SLLW/SRLW.

SRAW mirrors SLLW/SRLW's Main-AIR row exactly (same `m32 = 1` bus path, same
`is_external_op = 1` to the `BinaryExtension` SM) — only the `op` literal
differs (`OP_SRA_W = 38` vs `OP_SLL_W = 36` / `OP_SRL_W = 37`). The direction
of the shift (arithmetic-right) lives on the downstream SM side, not in the
Main AIR.

This module instantiates `Tactics.ShiftArchetype` for the SRAW opcode,
producing the analogue of `Spec.Shift.sllw_compositional` via the
`shift_archetype_m32_one_zeros_bus` macro-theorem.
-/

namespace ZiskFv.Circuit.ShiftRA

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ShiftArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in SRAW-execution mode: external op with
    opcode literal 38 (`OP_SRA_W`), 32-bit width (`m32 = 1`),
    `set_pc = 0`, and `flag = 0`. Identical shape to
    `Spec.Shift.main_row_in_sllw_mode` modulo the op literal. -/
@[simp]
def main_row_in_sraw_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (38 : FGL)
  ∧ m.m32 r_main = 1
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- Main-side hypotheses for the SRAW archetype. Shape identical to
    `Spec.Shift.sllw_circuit_holds` modulo opcode literal. -/
@[simp]
def sraw_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_sraw_mode m r_main
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Compositional SRAW theorem.** Instantiation of the
    `ShiftArchetype` m32=1 archetype macro at `opcode_lit = OP_SRA_W`.
    Under the SRAW-mode Main constraints, the secondary SM's bus entry
    carries zero high lanes — the `(1 - m32) * a[1]` / `(1 - m32) * b[1]`
    PIL emission collapses under `m32 = 1`. -/
theorem sraw_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : sraw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 := by
  -- Repackage `sraw_circuit_holds` as `shift_archetype_circuit_holds`
  -- at `opcode_lit = OP_SRA_W`, `m32_val = 1`, then delegate.
  obtain ⟨h1, h2, h3, h_mode, h_match⟩ := h
  obtain ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩ := h_mode
  exact shift_archetype_m32_one_zeros_bus m r_main bus_entry OP_SRA_W
    ⟨h1, h2, h3, ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩, h_match⟩

end ZiskFv.Circuit.ShiftRA
