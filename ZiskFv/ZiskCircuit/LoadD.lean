import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus

/-!
Compositional LD (load doubleword) spec.

Given the Main-AIR row in LD-mode (`is_external_op = 0`, `op = OP_COPYB = 1`,
`m32 = 0`, `set_pc = 0`, `store_pc = 0`), the named Main constraints 9/16
(internal-op=1 copies `b → c`), 18 (internal-op=1 clears `flag`), 19
(flag/set_pc disjoint), and the PC handshake, plus a memory-bus matching
hypothesis tying the Main `b` lanes to the 8 byte-lanes of the load entry,
yield:

* `c_packed = memory_entry_toField entry`  — the packed 64-bit `c` equals
  the 64-bit value from the memory-bus entry;
* `next_pc = pc + 4`                       — PC advances by 4.

This is the **A3 archetype** circuit-side spec. The Sail-level companion
and equivalence theorem live in `Equivalence/LoadD.lean`.

Unlike `Circuit.Add`, LD does *not* use the operation bus — copyb is
`OpType::Internal`, so Main constraint 9 discharges the `c = b` identity
directly. The novel infrastructure is the **memory-bus** matching predicate
`memory_load_lanes_match` imported from `Airs/MemoryBus.lean`.
-/

namespace ZiskFv.ZiskCircuit.LoadD

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in LD-execution mode: **internal** op
    (is_external_op = 0) with opcode literal 1 (OP_COPYB), 64-bit width
    (m32 = 0), and no PC override (`set_pc = 0`, `store_pc = 0`). -/
@[simp]
def main_row_in_ld_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 0
  ∧ m.op r_main = (1 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- The Main AIR constraints a LD-family row must satisfy, specialized
    to the internal-op=copyb case:
    * constraint 9  — `c_0 = b_0` (when `is_external_op = 0, op = 1`);
    * constraint 16 — `c_1 = b_1`;
    * constraint 18 — `flag = 0` (when `is_external_op = 0, op = 1`);
    * constraint 19 — `flag * set_pc = 0` (trivial given `set_pc = 0`);
    * plus the PC handshake parameterized on `next_pc`.

    No `flag_boolean` / `is_external_op_boolean` required here — the
    mode witnesses already pin both to `0`. -/
@[simp]
def load_subset_holds (m : Valid_Main C FGL FGL) (row : ℕ) (next_pc : FGL) : Prop :=
  internal_op1_copies_b0 m row
  ∧ internal_op1_copies_b1 m row
  ∧ internal_op1_clears_flag m row
  ∧ flag_set_pc_disjoint m row
  ∧ pc_handshake_with_next_pc m row next_pc

/-- Hypotheses needed by the LD compositional theorem. Combines:
    * the Main-subset constraints (load-specific);
    * the mode pinning (internal op=1);
    * the memory-bus matching lanes (the `b` lanes equal the low/high
      halves of the 8-byte load-value entry).

    The caller supplies `entry` — the memory-bus entry for the LD's
    memory read. Existence of this entry is parameterized; the audit
    derives it from the PIL memory-SM permutation. -/
@[simp]
def load_d_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL) : Prop :=
  load_subset_holds m r_main next_pc
  ∧ main_row_in_ld_mode m r_main
  ∧ memory_load_lanes_match m r_main entry

/-- The 64-bit value packed into the Main row's `(c_0, c_1)` lanes,
    as a single Goldilocks element. Same shape as `Circuit.Add.main_c_packed`. -/
@[simp]
def main_c_packed (m : Valid_Main C FGL FGL) (r : ℕ) : FGL :=
  m.c_0 r + m.c_1 r * 4294967296

/-- **Compositional LD theorem (c-packed).** If the load-subset Main
    constraints hold, the row is in LD-mode, and the memory-bus lanes
    match, then Main's packed `c` equals the packed 64-bit value from
    the memory-bus entry.

    Proof structure:
    1. Internal-op=1 (`is_external_op = 0`, `op = 1`) activates
       constraint 9/16: `b_0 - c_0 = 0` and `b_1 - c_1 = 0`;
    2. `memory_load_lanes_match` substitutes `b_0 = memory_entry_lo`,
       `b_1 = memory_entry_hi`;
    3. `memory_entry_toField_lo_hi` reassembles into the 64-bit value.

    The conclusion avoids mentioning the byte-lanes individually —
    `memory_entry_toField` packs them; `Equivalence/LoadD.lean` then
    bridges from `memory_entry_toField` to the `BitVec 64` produced
    by Sail's `vmem_read`. -/
lemma load_d_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_d_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_toField entry := by
  obtain ⟨h_subset, h_mode, h_mem⟩ := h
  obtain ⟨h_copy0, h_copy1, _h_flag0, _h_disj, _h_hand⟩ := h_subset
  obtain ⟨h_ext, h_op, _h_m32, _h_setpc⟩ := h_mode
  obtain ⟨h_b0_lo, h_b1_hi⟩ := h_mem
  -- Constraint 9/16 reduce to `c_0 = b_0` / `c_1 = b_1` after we
  -- substitute `is_external_op = 0, op = 1`. Close via linear_combination
  -- (ring-style) — linarith doesn't work over the finite field FGL.
  simp only [internal_op1_copies_b0, internal_op1_copies_b1] at h_copy0 h_copy1
  rw [h_ext, h_op] at h_copy0 h_copy1
  have h_c0 : m.c_0 r_main = m.b_0 r_main := by linear_combination -h_copy0
  have h_c1 : m.c_1 r_main = m.b_1 r_main := by linear_combination -h_copy1
  -- Unfold, substitute, and reassemble via memory_entry_toField_lo_hi.
  unfold main_c_packed
  rw [h_c0, h_c1, h_b0_lo, h_b1_hi, memory_entry_toField_lo_hi]

/-- **Next-PC for LD.** With `set_pc = 0` and `flag = 0` (both pinned
    by the mode + constraint 18), the PC handshake gives
    `next_pc = pc + jmp_offset2`. For LD, `jmp_offset2 = 4` (from
    `transpile_LD`), so this is `pc + 4`. -/
lemma load_d_next_pc
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_d_circuit_holds m r_main next_pc entry) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) := by
  obtain ⟨h_subset, h_mode, _h_mem⟩ := h
  obtain ⟨_, _, _, _, h_hand⟩ := h_subset
  obtain ⟨_, _, _, h_setpc⟩ := h_mode
  exact pc_handshake_branch m r_main next_pc h_setpc h_hand

/-- **Next-PC simplified for LD.** When `flag = 0` (forced by
    constraint 18) and `jmp_offset1 = jmp_offset2 = 4` (forced by
    `transpile_LD`), the handshake collapses to `next_pc = pc + 4`. -/
lemma load_d_next_pc_concrete
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_d_circuit_holds m r_main next_pc entry)
    (h_jmp1 : m.jmp_offset1 r_main = 4)
    (h_jmp2 : m.jmp_offset2 r_main = 4) :
    next_pc = m.pc r_main + 4 := by
  -- First derive `flag = 0` from constraint 18 + the mode witnesses.
  have h_pc := load_d_next_pc m r_main next_pc entry h
  obtain ⟨h_subset, h_mode, _⟩ := h
  obtain ⟨_, _, h_flag0, _, _⟩ := h_subset
  obtain ⟨h_ext, h_op, _, _⟩ := h_mode
  simp only [internal_op1_clears_flag] at h_flag0
  rw [h_ext, h_op] at h_flag0
  have h_flag : m.flag r_main = 0 := by linear_combination h_flag0
  -- Apply the PC handshake, substitute flag/jmp values.
  rw [h_jmp1, h_jmp2, h_flag] at h_pc
  linear_combination h_pc

end ZiskFv.ZiskCircuit.LoadD
