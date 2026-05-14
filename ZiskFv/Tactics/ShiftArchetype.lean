import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Circuit.Shift

/-!
**Shift archetype macros / generic lemmas.**

The six RV64IM shift opcodes (SLL / SRL / SRA — 64-bit —
and SLLW / SRLW / SRAW — 32-bit-then-sign-extend) share a single
ZisK microinstruction shape under `create_register_op`:

* `op` = one of `OP_SLL`/`OP_SRL`/`OP_SRA` (64-bit) or
  `OP_SLL_W`/`OP_SRL_W`/`OP_SRA_W` (32-bit);
* `is_external_op = 1`, type `BinaryE` — delegated to the
  `BinaryExtension` SM via the operation bus;
* `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`;
* `flag = 0` (shifts never produce a boolean flag on the
  `BinaryExtension` path);
* `m32 = 1` for the `_w` variants, `m32 = 0` for the 64-bit siblings.

The Main-AIR side of the compositional proof is identical across all
six — the only parameters are the Zisk opcode literal and the
`m32` bit. The **direction** of the shift (left / right / arithmetic
right) lives entirely on the Sail side (`execute_RTYPE` /
`execute_RTYPEW` dispatch on the `rop`/`ropw` enum).

This module packages the reusable pieces so SRLW, SRAW, SLL, SRL,
SRA can fan out from a single parametric proof skeleton.

## Parameterization

* `opcode_lit : FGL` — `OP_SLL_W = 36`, `OP_SRL_W = 37`, etc.
* `m32_val : FGL` — `1` for `_w` variants, `0` otherwise. The
  archetype lemmas fire for both values; callers pin one at the
  equivalence theorem layer.

## Usage pattern

```
-- SRLW case:
theorem equiv_SRLW (...) := by
  have h_high_zero :=
    shift_archetype_m32_one_zeros_bus m r_main bus_entry
      (opcode_lit := OP_SRL_W) h_circuit_srlw
  ...
```

See `Spec/Shift.lean::sllw_compositional` for the SLLW specialization
that the concrete `equiv_SLLW_circuit` theorem consumes; the
`shift_archetype_m32_one_zeros_bus` macro-theorem below is its
parametric twin. SLL/SRL/SRA (64-bit siblings) invoke
`shift_archetype_m32_zero_passthrough_bus` for the symmetric
passthrough.
-/

namespace ZiskFv.Tactics.ShiftArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Circuit.Shift

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Archetype mode predicate.** A Main row is in shift-execution
    mode for a given Zisk opcode literal and `m32` bit when
    `is_external_op = 1`, `op = opcode_lit`, `m32 = m32_val`,
    `flag = 0`, `set_pc = 0`. `m32_val = 1` covers SLLW/SRLW/SRAW;
    `m32_val = 0` covers SLL/SRL/SRA. -/
@[simp]
def main_row_in_shift_mode
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (opcode_lit m32_val : FGL) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = m32_val
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- **Archetype circuit-holds.** Parametric version of
    `Circuit.Shift.sllw_circuit_holds` over opcode literal and `m32`. -/
@[simp]
def shift_archetype_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit m32_val : FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_shift_mode m r_main opcode_lit m32_val
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Archetype m32 = 1 bus-zeroing theorem.** For any shift opcode
    emitted in `m32 = 1` mode (SLLW/SRLW/SRAW), the secondary SM's
    bus entry has `a_hi = b_hi = 0`. Mirrors
    `Circuit.Shift.sllw_compositional` but parametric over the opcode
    literal. -/
lemma shift_archetype_m32_one_zeros_bus
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit : FGL)
    (h : shift_archetype_circuit_holds m r_main bus_entry opcode_lit 1) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 := by
  obtain ⟨_, _, _, h_mode, h_match⟩ := h
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  obtain ⟨_, _, _, h_ahi, _, h_bhi, _, _, _, _, _, _⟩ := h_match
  refine ⟨?_, ?_⟩
  · rw [← h_ahi]
    simp only [opBus_row_Main]
    rw [h_m32]; simp
  · rw [← h_bhi]
    simp only [opBus_row_Main]
    rw [h_m32]; simp

/-- **Archetype m32 = 0 bus-passthrough theorem.** For any shift
    opcode emitted in `m32 = 0` mode (SLL/SRL/SRA), the secondary
    SM's bus entry carries the Main row's `a[1]`/`b[1]` lanes
    verbatim (the `(1 - m32) = 1` factor leaves them unchanged).
    SLL/SRL/SRA proofs chain this with a `Valid_BinaryExtension`
    bus-emission; this theorem states the Main-side half only. -/
lemma shift_archetype_m32_zero_passthrough_bus
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit : FGL)
    (h : shift_archetype_circuit_holds m r_main bus_entry opcode_lit 0) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main := by
  obtain ⟨_, _, _, h_mode, h_match⟩ := h
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  obtain ⟨_, _, _, h_ahi, _, h_bhi, _, _, _, _, _, _⟩ := h_match
  refine ⟨?_, ?_⟩
  · rw [← h_ahi]
    simp only [opBus_row_Main]
    rw [h_m32]
    ring
  · rw [← h_bhi]
    simp only [opBus_row_Main]
    rw [h_m32]
    ring

end ZiskFv.Tactics.ShiftArchetype
