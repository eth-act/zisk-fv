import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus

/-!
Compositional shift archetype spec — SLLW.

SLLW exercises the `m32 = 1` bus path. The PIL
`assumes_operation(...)` at `main.pil:367-374` emits the
operation-bus entry with `a = [a[0], (1 - m32) * a[1]]` and
`b = [b[0], (1 - m32) * b[1]]`. Under `m32 = 1` the high lanes zero
out: the downstream `BinaryExtension` state machine sees a 32-bit
operand. The `one_sub_one_mul` simp lemma collapses the
`(1 - 1) * x` factor post-`rw [h_m32]`.

This module packages the **Main-side** compositional theorem for the
SLLW archetype:

* `main_row_in_sllw_mode` — the mode witnesses that `transpile_SLLW`
  asserts (external op with `op = OP_SLL_W = 36`, `m32 = 1`,
  `set_pc = 0`, `flag = 0`);
* `sllw_circuit_holds` — adds the boolean / disjointness subset of
  Main's ADD-like constraints plus the bus-match hypothesis; and
* `sllw_bus_high_lanes_zero` — the compositional lemma: under mode
  witnesses + PIL-faithful `opBus_row_Main`, the emitted bus entry's
  `a_hi` and `b_hi` fields are `0` (the `m32 = 1` zeroing).

Like `Circuit.BranchEqual` for BEQ, the bus-emission match to the
concrete `BinaryExtension` AIR is **parameterized** (deferred to
the audit). The caller supplies the match hypothesis; we provide
the Main-side shape reasoning.

The actual SLLW compute semantics — 32-bit shift then sign-extend to
64 — lives on the Sail side (`Fundamentals/Execution.lean::
execute_RTYPEW_pure` for `ropw.SLLW`), not on the Main AIR (which
just delegates to the `BinaryExtension` SM via the bus).
-/

namespace ZiskFv.Circuit.Shift

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in SLLW-execution mode: external op
    with opcode literal 36 (`OP_SLL_W`), 32-bit width (`m32 = 1`),
    `set_pc = 0`, and `flag = 0`. Shape mirrors
    `Circuit.Add.main_row_in_add_mode`, with the key difference that
    `m32 = 1` here (vs. 0 for ADD/BEQ/JAL/MUL/LD). -/
@[simp]
def main_row_in_sllw_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (36 : FGL)
  ∧ m.m32 r_main = 1
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- Main-side hypotheses for the SLLW archetype. The bus-match to the
    `BinaryExtension` SM is parameterized via `h_bus_match`: caller
    supplies an `OperationBusEntry` they claim the secondary SM
    emits, and asserts it matches the Main row's `opBus_row_Main`.
    The audit derives this from a PIL-level
    `Valid_BinaryExtension` AIR. -/
@[simp]
def sllw_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_sllw_mode m r_main
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Compositional SLLW bus-lane lemma.** Under SLLW mode witnesses
    (especially `m32 = 1`), the Main row's emitted bus entry has
    `a_hi = 0` and `b_hi = 0` — the PIL `(1 - m32) * a[1]` factor
    collapses: under `m32 = 1` the high lanes vanish on the bus.

    The `(1 - m32) * x ↦ 0` collapse fires via `one_sub_one_mul`
    (the @[simp] lemma added alongside this module). -/
lemma sllw_bus_high_lanes_zero
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (h_mode : main_row_in_sllw_mode m r_main) :
    (opBus_row_Main m r_main).a_hi = 0
    ∧ (opBus_row_Main m r_main).b_hi = 0 := by
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  refine ⟨?_, ?_⟩ <;>
    simp only [opBus_row_Main] <;>
    rw [h_m32] <;>
    simp

/-- **Compositional SLLW theorem.** Given the Main-side circuit
    constraints plus the bus-match to the (caller-supplied) secondary
    entry, the `a_hi` and `b_hi` fields carried on that secondary
    entry are also `0`. The audit instantiates this with the
    `BinaryExtension` AIR's own `opBus_row_BinaryExtension`; here
    it remains a parameterized statement that the `m32 = 1` path
    zeroes the high lanes end-to-end. -/
lemma sllw_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : sllw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 := by
  obtain ⟨_, _, _, h_mode, h_match⟩ := h
  obtain ⟨h_main_ahi_zero, h_main_bhi_zero⟩ :=
    sllw_bus_high_lanes_zero m r_main h_mode
  obtain ⟨_, _, _, h_ahi, _, h_bhi, _, _, _, _, _, _⟩ := h_match
  refine ⟨?_, ?_⟩
  · rw [← h_ahi, h_main_ahi_zero]
  · rw [← h_bhi, h_main_bhi_zero]

end ZiskFv.Circuit.Shift
