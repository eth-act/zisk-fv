import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Airs.MemoryBus
import ZiskFv.Channels.RangeBusSoundness

/-!
# Memory-bus entry byte-range soundness

The memory-bus protocol carries entries whose 8 byte cells
(`x0..x7`) participate in a row-level `bits(8)` lookup against the
standard byte-range bus. The `pil2-compiler` translates each
`bits(8)` annotation into a lookup-argument interaction on
`RANGE_BUS_ID`; lookup-argument soundness on that bus IS the trust
assumption (same trust class as the existing per-AIR range axioms
`binary_columns_in_range`, `binary_extension_columns_in_range`,
`binary_add_columns_in_range`, `main_columns_in_range`).

PIL citations:
* `zisk/state-machines/mem/pil/mem.pil:64`: `col witness bits(8) value[BYTES]`
  for the 8 per-byte memory-data columns on the Mem AIR provider side.
* `zisk/state-machines/mem_align/pil/mem_align.pil:103`: `col witness
  bits(8) value[BYTES]` on the MemAlign* providers.
* `zisk/state-machines/main/pil/main.pil:78`: `col witness bits(8)
  x[BYTES]` on Main when participating as a memory-bus consumer.

The lookup-argument chain across these participants means every
memory-bus entry that ever appears on the bus (load-side or
store-side) has its 8 byte cells constrained to `[0, 256)`. This is
the same closure pattern already accepted for register-write entries
via `memory_bus_register_write_perm_sound`.

Trust class: lookup-argument soundness on the standard byte-range
bus, restricted to memory-bus participants.
-/

namespace ZiskFv.Airs.MemoryBus

open Goldilocks
open ZiskFv.Channels.RangeBusSoundness

/-- **Memory-bus entry byte-range soundness (derived).** Every
    memory-bus entry's 8 byte cells (`x0..x7`) lie in `[0, 256)`.
    Soundness derives from the bus protocol's `bits(8)` annotation
    on the per-byte columns of every memory-bus participant (Mem,
    MemAlign*, Main's memory-bus emission path).

    Previously an axiom; now derived from `range_bus_sound` via 8
    applications (one per byte lane). The row argument is dummied to
    `0` since `MemoryBusEntry` is not a row-indexed record. -/
theorem memory_bus_entry_byte_range_perm_sound (e : Interaction.MemoryBusEntry FGL) :
    memory_entry_bytes_in_range e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact range_bus_sound e (fun e _ => e.x0) 8 trivial 0
  · exact range_bus_sound e (fun e _ => e.x1) 8 trivial 0
  · exact range_bus_sound e (fun e _ => e.x2) 8 trivial 0
  · exact range_bus_sound e (fun e _ => e.x3) 8 trivial 0
  · exact range_bus_sound e (fun e _ => e.x4) 8 trivial 0
  · exact range_bus_sound e (fun e _ => e.x5) 8 trivial 0
  · exact range_bus_sound e (fun e _ => e.x6) 8 trivial 0
  · exact range_bus_sound e (fun e _ => e.x7) 8 trivial 0

/-- The lo-half byte pack `e.x0 + e.x1*256 + e.x2*65536 + e.x3*16777216`
    fits in `[0, 2^32)` once the four involved byte cells are byte-ranged.
    Derived from `memory_bus_entry_byte_range_perm_sound`; lets JAL / JALR /
    AUIPC discharge the `h_lo_bound` parameter their canonicals previously
    asked the caller to supply. -/
theorem memory_entry_lo_val_lt_2_32 (e : Interaction.MemoryBusEntry FGL) :
    (memory_entry_lo e).val < 4294967296 := by
  have hr := memory_bus_entry_byte_range_perm_sound e
  obtain ⟨h0, h1, h2, h3, _, _, _, _⟩ := hr
  simp only [memory_entry_lo, Fin.val_add, Fin.val_mul]
  have h256_lt : (256 : ℕ) < GL_prime := by decide
  have h65536_lt : (65536 : ℕ) < GL_prime := by decide
  have h16777216_lt : (16777216 : ℕ) < GL_prime := by decide
  have hm1 : e.x1.val * (256 : FGL).val < GL_prime := by
    have h256_val : ((256 : FGL) : Fin GL_prime).val = 256 :=
      Nat.mod_eq_of_lt h256_lt
    rw [h256_val]
    have : e.x1.val * 256 < 256 * 256 :=
      Nat.mul_lt_mul_of_pos_right h1 (by decide)
    omega
  have hm2 : e.x2.val * (65536 : FGL).val < GL_prime := by
    have h65536_val : ((65536 : FGL) : Fin GL_prime).val = 65536 :=
      Nat.mod_eq_of_lt h65536_lt
    rw [h65536_val]
    have : e.x2.val * 65536 < 256 * 65536 :=
      Nat.mul_lt_mul_of_pos_right h2 (by decide)
    omega
  have hm3 : e.x3.val * (16777216 : FGL).val < GL_prime := by
    have h16777216_val : ((16777216 : FGL) : Fin GL_prime).val = 16777216 :=
      Nat.mod_eq_of_lt h16777216_lt
    rw [h16777216_val]
    have : e.x3.val * 16777216 < 256 * 16777216 :=
      Nat.mul_lt_mul_of_pos_right h3 (by decide)
    omega
  have h256_val : ((256 : FGL) : Fin GL_prime).val = 256 :=
    Nat.mod_eq_of_lt h256_lt
  have h65536_val : ((65536 : FGL) : Fin GL_prime).val = 65536 :=
    Nat.mod_eq_of_lt h65536_lt
  have h16777216_val : ((16777216 : FGL) : Fin GL_prime).val = 16777216 :=
    Nat.mod_eq_of_lt h16777216_lt
  rw [h256_val] at hm1 ⊢
  rw [h65536_val] at hm2 ⊢
  rw [h16777216_val] at hm3 ⊢
  rw [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2, Nat.mod_eq_of_lt hm3]
  have hs1 : e.x0.val + e.x1.val * 256 < GL_prime := by omega
  rw [Nat.mod_eq_of_lt hs1]
  have hs2 : e.x0.val + e.x1.val * 256 + e.x2.val * 65536 < GL_prime := by omega
  rw [Nat.mod_eq_of_lt hs2]
  have hs3 : e.x0.val + e.x1.val * 256 + e.x2.val * 65536
              + e.x3.val * 16777216 < GL_prime := by omega
  rw [Nat.mod_eq_of_lt hs3]
  omega

end ZiskFv.Airs.MemoryBus
