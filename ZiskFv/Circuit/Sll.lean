import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.ShiftArchetype

/-!
Compositional SLL spec (Phase 3A H1 — `ShiftArchetype` m32=0 instantiation).

SLL is the 64-bit sibling of SLLW. They differ only in:
* the Zisk opcode literal (`OP_SLL = 33` vs `OP_SLL_W = 36`);
* the width flag (`m32 = 0` vs `m32 = 1`).

Under `m32 = 0`, the Main-AIR's PIL `a = [a[0], (1 - m32) * a[1]]`
bus-emission formula collapses the high lanes to **pass-through**
rather than zero — the downstream `BinaryExtension` SM sees the full
64-bit `a_1`/`b_1` lanes. This is the `shift_archetype_m32_zero_
passthrough_bus` archetype theorem from `Tactics/ShiftArchetype.lean`.

The direction of the shift (left, right-logical, right-arithmetic)
lives entirely on the Sail side; the Main-AIR is direction-agnostic
and the downstream SM dispatches on the `op` field.
-/

namespace ZiskFv.Circuit.Sll

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ShiftArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in SLL-execution mode: external op with
    opcode literal 33 (`OP_SLL`), full 64-bit width (`m32 = 0`),
    `set_pc = 0`, and `flag = 0`. Identical shape to
    `Spec.Shift.main_row_in_sllw_mode` modulo `m32 = 0` and the op
    literal. -/
@[simp]
def main_row_in_sll_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (33 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- Main-side hypotheses for the SLL archetype. Same shape as
    `Spec.ShiftR.srlw_circuit_holds` modulo opcode literal and
    `m32 = 0`. -/
@[simp]
def sll_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_sll_mode m r_main
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Compositional SLL theorem.** Instantiation of the
    `ShiftArchetype` m32=0 archetype macro at `opcode_lit = OP_SLL`.
    Under the SLL-mode Main constraints, the secondary SM's bus entry
    carries `a_hi = m.a_1 r_main` and `b_hi = m.b_1 r_main` — the
    `(1 - m32)` factor passes through under `m32 = 0`, so the high
    lanes flow verbatim to the `BinaryExtension` SM. -/
theorem sll_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : sll_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main := by
  obtain ⟨h1, h2, h3, h_mode, h_match⟩ := h
  obtain ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩ := h_mode
  exact shift_archetype_m32_zero_passthrough_bus m r_main bus_entry OP_SLL
    ⟨h1, h2, h3, ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩, h_match⟩

end ZiskFv.Circuit.Sll
