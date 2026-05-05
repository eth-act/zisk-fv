import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Circuit.StoreD
import ZiskFv.Tactics.StoreArchetype

/-!
Compositional SW (store word) spec — Phase 2.5 D4d sibling of
`Spec.StoreD`. Narrow variant: SW writes the **low 4 bytes** of `rs2`
to memory while SD writes all 8.

At the Main-AIR level the SW row is indistinguishable from SD (both
use `OP_COPYB = 1`, `is_external_op = 0`, `m32 = 0`, `set_pc = 0`,
`store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`, `src_a = reg(rs1)`,
`src_b = reg(rs2)`). The only substantive PIL-level difference is
`ind_width`: SD emits width = 8, SW emits width = 4. `ind_width` is
not a Main-AIR column in our `Valid_Main` packaging — it surfaces only
on the memory-bus entry as the count of live byte lanes.

Accordingly, SW's circuit-holds is SD's circuit-holds plus a
**high-byte zeroing hypothesis** on the memory-bus write entry:
`entry.x4 = entry.x5 = entry.x6 = entry.x7 = 0`. With this zeroing,
`memory_entry_toField` reduces to `memory_entry_lo` — i.e. the packed
`c` cell equals just the low 32 bits of the store value.

This module is the **first sibling instantiation of the store
archetype macro** (`Tactics.StoreArchetype`). It validates that the
archetype theorems parameterize correctly on opcode width without
requiring any adjustment to the macro infrastructure.
-/

namespace ZiskFv.Circuit.StoreW

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Circuit.StoreD
open ZiskFv.Tactics.StoreArchetype
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **SW high-byte zeroing.** The memory-bus write entry populated by a
    4-byte store has its top 4 byte lanes (`x4..x7`) pinned to zero,
    because ZisK's Main AIR only routes `ind_width = 4` bytes from the
    `c` cell to the memory-bus entry; the remaining lanes are witnessed
    as zero by the PIL circuit.

    Supplied by the caller (Phase 4 audit derives it from the PIL
    memory-SM `permutation_proves` side + the `ind_width` selector). -/
@[simp]
def sw_high_bytes_zero (entry : MemoryBusEntry FGL) : Prop :=
  entry.x4 = 0 ∧ entry.x5 = 0 ∧ entry.x6 = 0 ∧ entry.x7 = 0

/-- When the high bytes are zero, the packed 64-bit memory-entry value
    reduces to just its low 32 bits (`memory_entry_lo`). -/
lemma memory_entry_toField_of_high_zero
    (entry : MemoryBusEntry FGL) (h : sw_high_bytes_zero entry) :
    memory_entry_toField entry = memory_entry_lo entry := by
  obtain ⟨h4, h5, h6, h7⟩ := h
  simp only [memory_entry_toField, memory_entry_lo, h4, h5, h6, h7]
  ring

/-- **Compositional SW theorem (c-packed, low-32-specialized).**
    Given the store-archetype circuit-holds (identical to SD's) plus
    the SW-specific high-byte-zeroing hypothesis, the Main row's packed
    `c` cell equals the low 32 bits of the memory-bus write entry.

    This is the SW analogue of `store_d_compositional` narrowed to the
    4-byte width. The proof routes through the store archetype theorem
    `store_archetype_copyb_c_packed` (validating the macro) and then
    applies `memory_entry_toField_of_high_zero`. -/
theorem store_w_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_zero : sw_high_bytes_zero entry) :
    main_c_packed m r_main = memory_entry_lo entry := by
  have h_packed := store_archetype_copyb_c_packed m r_main next_pc entry h_circuit
  rw [h_packed]
  exact memory_entry_toField_of_high_zero entry h_zero

/-- **Compositional SW theorem (c-packed, general form).** The same
    conclusion as `store_d_compositional`: `c_packed = memory_entry_toField
    entry`. With the high-byte zeroing witness the RHS equals
    `memory_entry_lo entry`, but we expose the general form too so SW
    composes uniformly with SD at the metaplan layer. -/
theorem store_w_compositional_general
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_toField entry :=
  store_archetype_copyb_c_packed m r_main next_pc entry h_circuit

/-- **Next-PC simplified for SW.** Identical in form to
    `store_d_next_pc_concrete` — the archetype's `j(4, 4)` yields
    `next_pc = pc + 4` for all stores regardless of width. -/
theorem store_w_next_pc_concrete
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_jmp1 : m.jmp_offset1 r_main = 4)
    (h_jmp2 : m.jmp_offset2 r_main = 4) :
    next_pc = m.pc r_main + 4 :=
  store_archetype_copyb_next_pc m r_main next_pc entry h_circuit h_jmp1 h_jmp2

end ZiskFv.Circuit.StoreW
