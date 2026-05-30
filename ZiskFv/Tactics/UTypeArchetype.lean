import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus

/-!
**UTYPE archetype macros / generic lemmas.**

Both RV64 UTYPE opcodes — LUI and AUIPC — are realized by a single
Zisk microinstruction that is *internal* (`is_external_op = 0`), so
neither emits an operation-bus entry. They share the same Main-AIR
columns except for two routing bits:

| opcode | `op`          | `store_pc` | `jmp_offset2` | rd receives         |
|--------|---------------|------------|---------------|---------------------|
| LUI    | `OP_COPYB = 1`| `0`        | `4`           | `c[0] = b[0] = imm` |
| AUIPC  | `OP_FLAG = 0` | `1`        | `imm`         | `pc + imm`          |

The two sub-archetypes below (`LUI`, `AUIPC`) handle each routing
individually because their proof obligations differ:

* **LUI:** internal-op-1 forces `c = b` (constraints 9/16) and `flag = 0`
  (constraint 18). With `store_pc = 0`, `store_value[0] = c[0]`, so rd
  receives `b[0]` verbatim. The PC handshake with `set_pc = 0, flag = 0`
  yields `next_pc = pc + jmp_offset2 = pc + 4`.
* **AUIPC:** internal-op-0 forces `c = 0` (constraints 8/15) and
  `flag = 1` (constraint 17). With `store_pc = 1`,
  `store_value[0] = 1 * (pc + jmp_offset2 - 0) + 0 = pc + jmp_offset2`.
  The PC handshake with `set_pc = 0, flag = 1` yields
  `next_pc = pc + jmp_offset2 + (jmp_offset1 - jmp_offset2)
         = pc + jmp_offset1 = pc + 4`.

## Usage pattern

```
-- LUI:
theorem equiv_LUI (...) := by
  have h_rd_value :=
    UTypeArchetype.lui_archetype_store_value m r_main h_circuit
  -- ...
-- AUIPC:
theorem equiv_AUIPC (...) := by
  have h_rd_value :=
    UTypeArchetype.auipc_archetype_store_value m r_main h_circuit
  -- ...
```

No secondary-SM hypothesis is needed (no bus hop). The store-value
lemma is the load-bearing result: it gives the rd-write identity
(`store_value[0] = imm` for LUI; `= pc + imm` for AUIPC) that the
`Spec/LoadUpperImmediate.lean` / `Spec/AddUpperImmediatePC.lean`
compositional theorems consume.
-/

namespace ZiskFv.Tactics.UTypeArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Trusted


/-! ## LUI sub-archetype -/

/-- **LUI-mode predicate.** A Main row is in LUI execution mode when it
    is internal `copyb` (`is_external_op = 0 ∧ op = 1 = OP_COPYB`), has
    full 64-bit width (`m32 = 0`), does not drive PC from `c[0]`
    (`set_pc = 0`), and stores `c` (not `pc + jmp_offset2`) to rd
    (`store_pc = 0`). -/
@[simp]
def main_row_in_lui_mode
    (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 0
  ∧ m.op r_main = (1 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0
  ∧ m.store_pc r_main = 0

/-- **LUI constraint subset.** Internal-op-1 forces `c = b` (constraints
    9/16) and `flag = 0` (constraint 18); `flag` / `is_external_op`
    booleans + disjointness are included so the PC handshake reduces
    cleanly. The PC handshake (parameterized on `next_pc`) is threaded
    through for the downstream next-pc lemma. -/
@[simp]
def lui_subset_holds
    (v : Valid_Main FGL FGL) (row : ℕ) (next_pc : FGL) : Prop :=
  flag_boolean v row
  ∧ is_external_op_boolean v row
  ∧ flag_set_pc_disjoint v row
  ∧ internal_op1_copies_b0 v row
  ∧ internal_op1_copies_b1 v row
  ∧ internal_op1_clears_flag v row
  ∧ pc_handshake_with_next_pc v row next_pc

/-- **LUI archetype circuit-holds.** Packs the constraint subset plus
    the mode witnesses. -/
@[simp]
def lui_archetype_circuit_holds
    (m : Valid_Main FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  lui_subset_holds m r_main next_pc
  ∧ main_row_in_lui_mode m r_main

/-- Derived: `flag = 0` when the row is internal-op-1. -/
private lemma flag_eq_zero_of_internal_op_one
    (v : Valid_Main FGL FGL) (row : ℕ)
    (h_ext : v.is_external_op row = 0)
    (h_op : v.op row = 1)
    (h18 : internal_op1_clears_flag v row) :
    v.flag row = 0 := by
  simp only [internal_op1_clears_flag] at h18
  rw [h_ext, h_op] at h18
  linear_combination h18

/-- Derived: `c_0 = b_0` when the row is internal-op-1. -/
private lemma c_0_eq_b_0_of_internal_op_one
    (v : Valid_Main FGL FGL) (row : ℕ)
    (h_ext : v.is_external_op row = 0)
    (h_op : v.op row = 1)
    (h9 : internal_op1_copies_b0 v row) :
    v.c_0 row = v.b_0 row := by
  simp only [internal_op1_copies_b0] at h9
  rw [h_ext, h_op] at h9
  linear_combination -h9

/-- Derived: `c_1 = b_1` when the row is internal-op-1. -/
private lemma c_1_eq_b_1_of_internal_op_one
    (v : Valid_Main FGL FGL) (row : ℕ)
    (h_ext : v.is_external_op row = 0)
    (h_op : v.op row = 1)
    (h16 : internal_op1_copies_b1 v row) :
    v.c_1 row = v.b_1 row := by
  simp only [internal_op1_copies_b1] at h16
  rw [h_ext, h_op] at h16
  linear_combination -h16

/-- **LUI archetype PC-advance theorem.** The next-pc equals
    `pc + jmp_offset2`. Together with `transpile_LUI` pinning
    `jmp_offset2 = 4`, this gives `next_pc = pc + 4`. -/
lemma lui_archetype_pc_advance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : lui_archetype_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, _h_c0_copy, _h_c1_copy,
          h18, h_handshake⟩ := h_subset
  obtain ⟨h_ext, h_op, _h_m32, h_set_pc, _h_store_pc⟩ := h_mode
  have h_flag : m.flag r_main = 0 :=
    flag_eq_zero_of_internal_op_one m r_main h_ext h_op h18
  simp only [pc_handshake_with_next_pc] at h_handshake
  rw [h_set_pc, h_flag] at h_handshake
  linear_combination h_handshake

/-- **LUI archetype store-value (low lane).** With `store_pc = 0`,
    `store_value[0] = c_0`, and under internal-op-1 `c_0 = b_0`. So rd's
    low lane equals `b_0 = imm_lo` (pinned by `transpile_LUI`). -/
lemma lui_archetype_store_value_lo
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : lui_archetype_circuit_holds m r_main next_pc) :
    m.store_pc r_main *
        (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
      + m.c_0 r_main
      = m.b_0 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, h9, _h16, _h18, _h_handshake⟩ :=
    h_subset
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  have h_c0_b0 : m.c_0 r_main = m.b_0 r_main :=
    c_0_eq_b_0_of_internal_op_one m r_main h_ext h_op h9
  rw [h_store_pc, h_c0_b0]
  ring

/-- **LUI archetype store-value (high lane).** With `store_pc = 0`,
    the high lane is `(1 - store_pc) * c_1 = c_1`. Under internal-op-1,
    `c_1 = b_1 = imm_hi` (pinned by `transpile_LUI`). -/
lemma lui_archetype_store_value_hi
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : lui_archetype_circuit_holds m r_main next_pc) :
    (1 - m.store_pc r_main) * m.c_1 r_main = m.b_1 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, _h9, h16, _h18, _h_handshake⟩ :=
    h_subset
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  have h_c1_b1 : m.c_1 r_main = m.b_1 r_main :=
    c_1_eq_b_1_of_internal_op_one m r_main h_ext h_op h16
  rw [h_store_pc, h_c1_b1]
  ring

/-! ## AUIPC sub-archetype -/

/-- **AUIPC-mode predicate.** A Main row is in AUIPC execution mode when
    it is internal `flag` (`is_external_op = 0 ∧ op = 0 = OP_FLAG`), has
    full 64-bit width (`m32 = 0`), does not drive PC from `c[0]`
    (`set_pc = 0`), and stores `pc + jmp_offset2` to rd (`store_pc = 1`). -/
@[simp]
def main_row_in_auipc_mode
    (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 0
  ∧ m.op r_main = (0 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0
  ∧ m.store_pc r_main = 1

/-- **AUIPC constraint subset.** Internal-op-0 forces `c = 0`
    (constraints 8/15) and `flag = 1` (constraint 17). Structurally
    identical to `jump_subset_holds` (JAL) — AUIPC shares JAL's
    internal-op-0 discipline but with `store_pc = 1` and
    `jmp_offset2` now carrying the AUIPC immediate. -/
@[simp]
def auipc_subset_holds
    (v : Valid_Main FGL FGL) (row : ℕ) (next_pc : FGL) : Prop :=
  flag_boolean v row
  ∧ is_external_op_boolean v row
  ∧ flag_set_pc_disjoint v row
  ∧ internal_op0_zeroes_c0 v row
  ∧ internal_op0_zeroes_c1 v row
  ∧ internal_op0_sets_flag v row
  ∧ pc_handshake_with_next_pc v row next_pc

/-- **AUIPC archetype circuit-holds.** Packs the constraint subset plus
    the mode witnesses. -/
@[simp]
def auipc_archetype_circuit_holds
    (m : Valid_Main FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  auipc_subset_holds m r_main next_pc
  ∧ main_row_in_auipc_mode m r_main

/-- **AUIPC archetype PC-advance theorem.** The next-pc equals
    `pc + jmp_offset1`. Under AUIPC's routing this is `pc + 4`. The
    handshake reasoning is the same as JAL: `set_pc = 0, flag = 1`
    collapses the formula to `pc + jmp_offset1`. -/
lemma auipc_archetype_pc_advance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : auipc_archetype_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, _h_c0_zero, _h_c1_zero,
          h17, h_handshake⟩ := h_subset
  obtain ⟨h_ext, h_op, _h_m32, h_set_pc, _h_store_pc⟩ := h_mode
  have h_flag : m.flag r_main = 1 :=
    flag_eq_one_of_internal_op_zero m r_main h_ext h_op h17
  exact pc_handshake_jump m r_main next_pc h_set_pc h_flag h_handshake

/-- **AUIPC archetype store-value (low lane).** With `store_pc = 1`,
    `store_value[0] = 1 * (pc + jmp_offset2 - c_0) + c_0`. Under
    internal-op-0, `c_0 = 0`, so this reduces to `pc + jmp_offset2`,
    which is the `pc + imm` RV64 semantics expects (given
    `transpile_AUIPC` pins `jmp_offset2 = imm_offset`). -/
lemma auipc_archetype_store_value_lo
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : auipc_archetype_circuit_holds m r_main next_pc) :
    m.store_pc r_main *
        (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
      + m.c_0 r_main
      = m.pc r_main + m.jmp_offset2 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, h8, _h15, _h17, _h_handshake⟩ :=
    h_subset
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  have h_c0 : m.c_0 r_main = 0 :=
    c_0_eq_zero_of_internal_op_zero m r_main h_ext h_op h8
  rw [h_store_pc, h_c0]
  ring

/-- **AUIPC archetype store-value (high lane).** With `store_pc = 1`,
    the high lane is `(1 - store_pc) * c_1 = 0`. This matches the RV64
    AUIPC semantics where only the low lane receives `pc + imm` when the
    high lane of `imm` is zero (AUIPC's immediate is 20 bits, so the
    contribution to the high lane of the 64-bit word depends only on
    the pc's high lane — the imm-high-lane write is zero-valued before
    the add). The real circuit's rd high lane is `pc_hi + carry`; this
    is the downstream `Spec` file's job to bridge. Here we just prove
    `(1 - store_pc) * c_1 = 0`. -/
lemma auipc_archetype_store_value_hi
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : auipc_archetype_circuit_holds m r_main next_pc) :
    (1 - m.store_pc r_main) * m.c_1 r_main = 0 := by
  obtain ⟨_h_subset, h_mode⟩ := h
  obtain ⟨_, _, _, _, h_store_pc⟩ := h_mode
  rw [h_store_pc]
  ring

end ZiskFv.Tactics.UTypeArchetype
