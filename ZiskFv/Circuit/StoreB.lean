import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Circuit.StoreD
import ZiskFv.Tactics.StoreArchetype

/-!
Compositional SB (store byte) spec — narrowest sibling of
`Circuit.StoreH` / `Circuit.StoreW` / `Circuit.StoreD`. SB writes the **low
1 byte** of `rs2` to memory while SH writes the low 2,
SW the low 4, and SD all 8.

At the Main-AIR level the SB row is indistinguishable from SH/SW/SD
(all use `OP_COPYB = 1`, `is_external_op = 0`, `m32 = 0`, `set_pc = 0`,
`store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`, `src_a = reg(rs1)`,
`src_b = reg(rs2)`). The only substantive PIL-level difference is
`ind_width`: SB emits width = 1, while SH = 2, SW = 4, SD = 8.
`ind_width` is not a Main-AIR column in our `Valid_Main` packaging — it
surfaces only on the memory-bus entry as the count of live byte lanes.

Accordingly, SB's circuit-holds is the store archetype's circuit-holds
plus a **high-byte zeroing hypothesis** on seven lanes (`entry.x1..x7 = 0`)
of the memory-bus write entry. Under zeroing,
`memory_entry_toField` reduces to `memory_entry_lo_8` — the packed
`c` cell equals just the low 8 bits of the store value.

Instantiates the `StoreArchetype` macro with the widest zeroing witness
of the family (seven lanes vs SH's six and SW's four).
-/

namespace ZiskFv.Circuit.StoreB

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Circuit.StoreD
open ZiskFv.Tactics.StoreArchetype
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Low 8 bits of a memory-bus entry**, packed as an `FGL` element.
    Just `x0`. Used by SB's spec to expose the `c`-packed value as the
    1-byte the store writes. -/
@[simp]
def memory_entry_lo_8 (e : MemoryBusEntry FGL) : FGL :=
  e.x0

/-- **SB high-byte zeroing.** The memory-bus write entry populated by a
    1-byte store has its top 7 byte lanes (`x1..x7`) pinned to zero,
    because ZisK's Main AIR only routes `ind_width = 1` byte from the
    `c` cell to the memory-bus entry; the remaining lanes are witnessed
    as zero by the PIL circuit.

    Supplied by the caller; the audit derives it from the PIL
    memory-SM `permutation_proves` side + the `ind_width` selector. -/
@[simp]
def sb_high_bytes_zero (entry : MemoryBusEntry FGL) : Prop :=
  entry.x1 = 0 ∧ entry.x2 = 0 ∧ entry.x3 = 0 ∧ entry.x4 = 0
    ∧ entry.x5 = 0 ∧ entry.x6 = 0 ∧ entry.x7 = 0

/-- When the high bytes are zero, the packed 64-bit memory-entry value
    reduces to just its low 8 bits (`memory_entry_lo_8`). -/
lemma memory_entry_toField_of_high_zero_8
    (entry : MemoryBusEntry FGL) (h : sb_high_bytes_zero entry) :
    memory_entry_toField entry = memory_entry_lo_8 entry := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [memory_entry_toField, memory_entry_lo_8, h1, h2, h3, h4, h5, h6, h7]
  ring

/-- **Compositional SB theorem (c-packed, low-8-specialized).**
    Given the store-archetype circuit-holds (identical to SD/SW/SH's)
    plus the SB-specific high-byte-zeroing hypothesis, the Main row's
    packed `c` cell equals the low 8 bits (x0) of the memory-bus write
    entry.

    Analogue of `store_h_compositional` / `store_w_compositional`
    narrowed to the 1-byte width. The proof routes through the store
    archetype theorem `store_archetype_copyb_c_packed` (validating the
    macro) and then applies `memory_entry_toField_of_high_zero_8`. -/
lemma store_b_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_zero : sb_high_bytes_zero entry) :
    main_c_packed m r_main = memory_entry_lo_8 entry := by
  have h_packed := store_archetype_copyb_c_packed m r_main next_pc entry h_circuit
  rw [h_packed]
  exact memory_entry_toField_of_high_zero_8 entry h_zero

/-- **Compositional SB theorem (c-packed, general form).** Same
    conclusion as `store_d_compositional` — `c_packed = memory_entry_toField
    entry`. With the high-byte zeroing witness the RHS equals
    `memory_entry_lo_8 entry`, but we expose the general form too so SB
    composes uniformly with SD/SW/SH at the equivalence layer. -/
lemma store_b_compositional_general
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_toField entry :=
  store_archetype_copyb_c_packed m r_main next_pc entry h_circuit

/-- **Next-PC simplified for SB.** Identical in form to
    `store_h_next_pc_concrete` / `store_w_next_pc_concrete` — the
    archetype's `j(4, 4)` yields `next_pc = pc + 4` for all stores
    regardless of width. -/
lemma store_b_next_pc_concrete
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : store_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_jmp1 : m.jmp_offset1 r_main = 4)
    (h_jmp2 : m.jmp_offset2 r_main = 4) :
    next_pc = m.pc r_main + 4 :=
  store_archetype_copyb_next_pc m r_main next_pc entry h_circuit h_jmp1 h_jmp2

end ZiskFv.Circuit.StoreB
