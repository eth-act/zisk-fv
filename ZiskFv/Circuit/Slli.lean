import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.ShiftArchetype

/-!
Compositional SLLI spec — `ShiftArchetype` m32=0 instantiation,
immediate-variant sibling of SLL.

SLLI shares SLL's Zisk opcode literal (`OP_SLL = 33`) and `m32 = 0`
Main-AIR mode — the only difference between SLL and SLLI at the
transpile layer is the `b` source (register read vs immediate-u64),
which the Main-AIR bus emission is agnostic to (it treats `b_lo`/`b_hi`
as data regardless of provenance). Consequently the compositional
Spec body is structurally identical to `Circuit.Sll`; we duplicate the
file only to keep the per-opcode namespace clean for downstream
consumers.
-/

namespace ZiskFv.Circuit.Slli

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ShiftArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in SLLI-execution mode. Same as
    `Circuit.Sll.main_row_in_sll_mode` — SLL and SLLI map to the same
    Zisk opcode (`OP_SLL = 33`, `m32 = 0`). -/
@[simp]
def main_row_in_slli_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (33 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- Main-side hypotheses for the SLLI archetype. -/
@[simp]
def slli_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_slli_mode m r_main
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Compositional SLLI theorem.** Instantiation of the
    `ShiftArchetype` m32=0 archetype macro at `opcode_lit = OP_SLL`
    (same literal as SLL). -/
lemma slli_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : slli_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main := by
  obtain ⟨h1, h2, h3, h_mode, h_match⟩ := h
  obtain ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩ := h_mode
  exact shift_archetype_m32_zero_passthrough_bus m r_main bus_entry OP_SLL
    ⟨h1, h2, h3, ⟨h_iext, h_op, h_m32, h_flag, h_spc⟩, h_match⟩

end ZiskFv.Circuit.Slli
