import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.ZiskCircuit.LoadD

/-!
Compositional SD (store doubleword) spec — the A4 write-side mirror
of `Circuit.LoadD`.

Given the Main-AIR row in SD-mode (`is_external_op = 0`, `op = OP_COPYB = 1`,
`m32 = 0`, `set_pc = 0`, `store_pc = 0` — identical to LD), the named Main
constraints 9/16 (internal-op=1 copies `b → c`), 18 (clears `flag`), 19
(flag/set_pc disjoint), and the PC handshake, plus a memory-bus matching
hypothesis tying the Main `b` lanes to the 8 byte-lanes of the **store
value** entry, yield:

* `c_packed = memory_entry_toField entry`  — the packed 64-bit `c`
  equals the store-value entry's packed 64-bit value (dual to LD:
  LD's `c_packed = memory_read_entry`, SD's `c_packed =
  memory_write_entry`);
* `next_pc = pc + 4`                       — PC advances by 4.

Unlike LD where `entry` is the memory-read entry (assume side,
`multiplicity = -1`), in SD `entry` is the memory-write entry
(prove side, `multiplicity = +1`). The lane-packing
(`memory_entry_toField`) is identical — the packing is
direction-agnostic.

## Subset shape reuse

SD reuses `load_subset_holds` verbatim — the Main constraint 9/16/18/19
+ PC handshake signature is identical for LD and SD because both sit in
the internal-op=1 mode. We re-export it as `store_subset_holds` for
readability at the SD spec-consumer level without introducing a
separately-defined predicate (trivial `rfl` bridge).
-/

namespace ZiskFv.ZiskCircuit.StoreD

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.LoadD
open ZiskFv.Trusted


/-- **Store-subset Main constraints.** Definitionally equal to
    `Circuit.LoadD.load_subset_holds` — both LD and SD sit in the
    internal-op=1 mode so the same Main constraints fire. We expose
    this alias for spec-consumer readability. -/
@[simp]
def store_subset_holds (m : Valid_Main FGL FGL) (row : ℕ) (next_pc : FGL) : Prop :=
  load_subset_holds m row next_pc

/-- The Main row at `r_main` is in SD-execution mode: **internal** op
    (is_external_op = 0) with opcode literal 1 (OP_COPYB), 64-bit width
    (m32 = 0), and no PC override (`set_pc = 0`). Identical to
    `main_row_in_ld_mode` — SD and LD share `OP_COPYB`. -/
@[simp]
def main_row_in_sd_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 0
  ∧ m.op r_main = (1 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- Hypotheses needed by the SD compositional theorem. Combines:
    * the Main-subset constraints (store-specific — same subset as LD);
    * the mode pinning (internal op=1);
    * the memory-bus **write** matching lanes (the `c` lanes equal the
      low/high halves of the 8-byte store-value entry).

    The caller supplies `entry` — the memory-bus *write* entry for the
    SD's memory write. Existence of this entry is parameterized; the
    audit derives it from the PIL memory-SM `permutation_proves`
    side. -/
@[simp]
def store_d_circuit_holds
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL) : Prop :=
  store_subset_holds m r_main next_pc
  ∧ main_row_in_sd_mode m r_main
  ∧ memory_store_lanes_match m r_main entry

/-- The 64-bit value packed into the Main row's `(c_0, c_1)` lanes,
    as a single Goldilocks element. Identical to
    `Circuit.LoadD.main_c_packed` — we re-export so the SD consumer
    doesn't need to import `Circuit.LoadD` alongside `Circuit.StoreD`. -/
@[simp]
def main_c_packed (m : Valid_Main FGL FGL) (r : ℕ) : FGL :=
  m.c_0 r + m.c_1 r * 4294967296

/-- **Compositional SD theorem (c-packed).** If the store-subset Main
    constraints hold, the row is in SD-mode, and the memory-bus write
    lanes match, then Main's packed `c` equals the packed 64-bit
    store-value from the memory-bus write entry.

    The proof composes through `load_d_compositional` — SD and LD share
    the same Main-constraint subset and mode, and the store-side
    matching predicate `memory_store_lanes_match` has the same `c = e`
    lane shape as LD's `register_write_lanes_match`. However we express
    the theorem directly (without routing through LoadD's
    `memory_load_lanes_match` on `b`) because the store hypothesis is
    on `c` — the existing LD route asserted on `b` and derived `c` via
    constraint 9; here we take `c` directly. -/
lemma store_d_compositional
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : store_d_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_toField entry := by
  obtain ⟨_h_subset, _h_mode, h_mem⟩ := h
  obtain ⟨h_c0_lo, h_c1_hi⟩ := h_mem
  -- The store-side lane match directly gives `c_0` and `c_1` in terms
  -- of `memory_entry_lo` / `memory_entry_hi`; reassemble via the
  -- `memory_entry_toField_lo_hi` bridge.
  unfold main_c_packed
  rw [h_c0_lo, h_c1_hi, memory_entry_toField_lo_hi]

/-- **Next-PC for SD.** With `set_pc = 0` and `flag = 0` (both pinned
    by the mode + constraint 18), the PC handshake gives
    `next_pc = pc + jmp_offset2`. For SD, `jmp_offset2 = 4` (from
    SD row-shape contract), so this is `pc + 4`. -/
lemma store_d_next_pc
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : store_d_circuit_holds m r_main next_pc entry) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) := by
  obtain ⟨h_subset, h_mode, _h_mem⟩ := h
  obtain ⟨_, _, _, _, h_hand⟩ := h_subset
  obtain ⟨_, _, _, h_setpc⟩ := h_mode
  exact pc_handshake_branch m r_main next_pc h_setpc h_hand

/-- **Next-PC simplified for SD.** When `flag = 0` (forced by
    constraint 18) and `jmp_offset1 = jmp_offset2 = 4` (forced by
    SD row-shape contract), the handshake collapses to `next_pc = pc + 4`. -/
lemma store_d_next_pc_concrete
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : store_d_circuit_holds m r_main next_pc entry)
    (h_jmp1 : m.jmp_offset1 r_main = 4)
    (h_jmp2 : m.jmp_offset2 r_main = 4) :
    next_pc = m.pc r_main + 4 := by
  -- First derive `flag = 0` from constraint 18 + the mode witnesses.
  have h_pc := store_d_next_pc m r_main next_pc entry h
  obtain ⟨h_subset, h_mode, _⟩ := h
  obtain ⟨_, _, h_flag0, _, _⟩ := h_subset
  obtain ⟨h_ext, h_op, _, _⟩ := h_mode
  simp only [internal_op1_clears_flag] at h_flag0
  rw [h_ext, h_op] at h_flag0
  have h_flag : m.flag r_main = 0 := by linear_combination h_flag0
  -- Apply the PC handshake, substitute flag/jmp values.
  rw [h_jmp1, h_jmp2, h_flag] at h_pc
  linear_combination h_pc

end ZiskFv.ZiskCircuit.StoreD
