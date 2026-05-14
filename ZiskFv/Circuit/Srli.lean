import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.ShiftArchetype

/-!
Compositional SRLI spec — `ShiftArchetype` m32=0 immediate sibling
of SRL. Structurally identical to `Circuit.Srl`; see `Circuit.Slli` for
why SLL and SLLI share their Zisk opcode.
-/

namespace ZiskFv.Circuit.Srli

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ShiftArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in SRLI-execution mode. Same as
    `Circuit.Srl.main_row_in_srl_mode` — SRL and SRLI map to the same
    Zisk opcode (`OP_SRL = 34`, `m32 = 0`). -/
@[simp]
def main_row_in_srli_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (34 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- Main-side hypotheses for the SRLI archetype. -/
@[simp]
def srli_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_srli_mode m r_main
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Compositional SRLI theorem.** Instantiation of the
    `ShiftArchetype` m32=0 archetype macro at `opcode_lit = OP_SRL`. -/
lemma srli_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : srli_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main := by
  obtain ⟨h1, h2, h3, h_mode, h_match⟩ := h
  obtain ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩ := h_mode
  exact shift_archetype_m32_zero_passthrough_bus m r_main bus_entry OP_SRL
    ⟨h1, h2, h3, ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩, h_match⟩

end ZiskFv.Circuit.Srli
