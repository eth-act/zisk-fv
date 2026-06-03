import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.ZiskCircuit.StoreD
import ZiskFv.Tactics.StoreArchetype

/-!
Compositional SH (store halfword) spec — narrow sibling of
`Circuit.StoreW` / `Circuit.StoreD`. SH writes the **low 2 bytes** of
`rs2` to memory while SW writes the low 4 and SD writes all 8.

At the Main-AIR level the SH row is indistinguishable from SW/SD (all
use `OP_COPYB = 1`, `is_external_op = 0`, `m32 = 0`, `set_pc = 0`,
`store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`, `src_a = reg(rs1)`,
`src_b = reg(rs2)`). The only substantive PIL-level difference is
`ind_width`: SH emits width = 2, while SW = 4 and SD = 8. `ind_width`
is not a Main-AIR column in our `Valid_Main` packaging — it surfaces
only on the memory-bus entry as the count of live byte lanes.

Accordingly, SH's circuit-holds is the store archetype's circuit-holds
plus a **high-byte zeroing hypothesis** on six lanes (`entry.x2..x7 = 0`)
of the memory-bus write entry. Under zeroing, `memory_entry_toField`
reduces to `memory_entry_lo_16` — the packed `c` cell equals just the
low 16 bits of the store value.

Instantiates the `StoreArchetype` macro with a narrower zeroing
witness than SW (six lanes vs four).
-/

namespace ZiskFv.ZiskCircuit.StoreH

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD
open ZiskFv.Tactics.StoreArchetype
open ZiskFv.Trusted


/-- **Low 16 bits of a memory-bus entry**, packed as an `FGL` element.
    Under the SH zeroing hypothesis the entire chunk-pack collapses to
    `value_0`, which holds the half-word as an FGL. Used by SH's spec
    to expose the `c`-packed value as the 2-byte halfword the store
    writes. -/
@[simp]
def memory_entry_lo_16 (e : MemoryBusEntry FGL) : FGL :=
  e.value_0

/-- **SH high-byte zeroing.** The memory-bus write entry populated by a
    2-byte store has its high chunk pinned to zero and its low chunk
    holding only a 16-bit halfword (`value_0.val < 65536`), because
    ZisK's Main AIR only routes `ind_width = 2` bytes from the `c`
    cell to the memory-bus entry; the remaining bytes are witnessed
    as zero by the PIL circuit.

    Supplied by the caller; the audit derives it from the PIL
    memory-SM `permutation_proves` side + the `ind_width` selector. -/
@[simp]
def sh_high_bytes_zero (entry : MemoryBusEntry FGL) : Prop :=
  entry.value_1 = 0 ∧ entry.value_0.val < 65536

/-- When the high bytes are zero, the packed 64-bit memory-entry value
    reduces to just its low 16 bits (`memory_entry_lo_16`). -/
lemma memory_entry_toField_of_high_zero_16
    (entry : MemoryBusEntry FGL) (h : sh_high_bytes_zero entry) :
    memory_entry_toField entry = memory_entry_lo_16 entry := by
  obtain ⟨h_v1, _⟩ := h
  show entry.value_0 + entry.value_1 * 4294967296 = entry.value_0
  rw [h_v1]; ring

/-- **Compositional SH theorem (c-packed, low-16-specialized).**
    Given the store-archetype circuit-holds (identical to SD/SW's) plus
    the SH-specific high-byte-zeroing hypothesis, the Main row's packed
    `c` cell equals the low 16 bits of the memory-bus write entry.

    Analogue of `store_w_compositional` narrowed to the 2-byte width.
    The proof routes through the store archetype theorem
    `store_archetype_copyb_c_packed` (validating the macro) and then
    applies `memory_entry_toField_of_high_zero_16`. -/
lemma store_h_compositional
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_zero : sh_high_bytes_zero entry) :
    main_c_packed m r_main = memory_entry_lo_16 entry := by
  have h_packed := store_archetype_copyb_c_packed m r_main next_pc entry h_circuit
  rw [h_packed]
  exact memory_entry_toField_of_high_zero_16 entry h_zero

/-- **Compositional SH theorem (c-packed, general form).** Same
    conclusion as `store_d_compositional` — `c_packed = memory_entry_toField
    entry`. With the high-byte zeroing witness the RHS equals
    `memory_entry_lo_16 entry`, but we expose the general form too so SH
    composes uniformly with SD/SW at the equivalence layer. -/
lemma store_h_compositional_general
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_toField entry :=
  store_archetype_copyb_c_packed m r_main next_pc entry h_circuit

/-- **Next-PC simplified for SH.** Identical in form to
    `store_w_next_pc_concrete` — the archetype's `j(4, 4)` yields
    `next_pc = pc + 4` for all stores regardless of width. -/
lemma store_h_next_pc_concrete
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_jmp1 : m.jmp_offset1 r_main = 4)
    (h_jmp2 : m.jmp_offset2 r_main = 4) :
    next_pc = m.pc r_main + 4 :=
  store_archetype_copyb_next_pc m r_main next_pc entry h_circuit h_jmp1 h_jmp2

end ZiskFv.ZiskCircuit.StoreH
