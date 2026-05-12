import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.MemoryBus.MemAlignBridge
import ZiskFv.Airs.MemoryBus.LaneMatch

/-!
# Mem discharge bridge

Implements *promise discharge* for the Mem-AIR-shape opcodes —
loads (`LD` / `LBU` / `LHU` / `LWU` / `LB` / `LH` / `LW`) and
stores (`SD` / `SB` / `SH` / `SW`).

Unlike the BinaryAdd / Binary / BinaryExtension / Arith bridges,
the Mem-side derivation infrastructure was authored *before* the
Step 2 bridge convention was established. The bulk of the work
lives in:

* `ZiskFv/Airs/MemoryBus/MemBridge.lean` — `lookup_consumer_matches_provider_load`
  and `lookup_consumer_matches_provider_store` axioms plus the
  `memory_{load,store}_lanes_match_of_mem_row` packaging theorems
  that produce the existential Mem row witness from the Main-side
  emission.
* `ZiskFv/Airs/MemoryBus/LaneMatch.lean` — the
  `memory_bus_register_write_perm_sound` axiom plus
  `register_{write,read_rs1,read_rs2}_lanes_match_of_bus_emission`
  theorems for the register-side lane match (`as = 1`).
* `ZiskFv/Airs/MemoryBus/MemAlignBridge.lean` — the
  `memalign_load_perm_sound` and
  `mem_align_rom_subdoubleword_load_value_1_zero` axioms plus the
  derived sub-doubleword zero-pad theorems
  (`memalign_subdoubleword_load_high_bytes_zero` etc.) that
  ground LBU / LHU / LWU's high-byte-zero claims.

This module is a thin façade re-exporting those theorems under a
single `Bridge.Mem` namespace alias so that downstream
`equiv_<OP>` proofs (Step 3) can consume Mem-side discharges
through the same import path the other bridges use.

No new axioms; no new derivation. All Mem-side trust was already
encoded prior to the Step 2 bridge convention; this file simply
groups it for uniform downstream access.
-/

namespace ZiskFv.Equivalence.Bridge.Mem

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Load-side discharge.** Re-export of
    `MemoryBus.memory_load_lanes_match_of_mem_row`: given a Main
    emission whose `b` lanes pack the entry's lo/hi halves
    (`as = 2`, `multiplicity = -1`), deliver the lane-match
    conclusion plus an existential Mem-AIR row witness grounded by
    `lookup_consumer_matches_provider_load`. Consumed by
    `equiv_LD` / `equiv_LBU` / `equiv_LHU` / `equiv_LWU` (and
    indirectly by `equiv_LB` / `equiv_LH` / `equiv_LW` after the
    sign-extension chain in `Circuit/SextLoadBridge.lean`). -/
theorem load_discharge
    (main : Valid_Main C FGL FGL) (mem : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_main_emit : main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e
                   ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = -1) :
    ZiskFv.Airs.MemoryBus.memory_load_lanes_match main r_main e
    ∧ ∃ r_mem, ZiskFv.Airs.MemoryBus.MemBridge.mem_row_matches_entry mem r_mem e ∧ mem.wr r_mem = 0 :=
  ZiskFv.Airs.MemoryBus.MemBridge.memory_load_lanes_match_of_mem_row main mem r_main e h_main_emit

/-- **Store-side discharge.** Symmetric to `load_discharge` for
    stores (`multiplicity = 1`, Main's `c` lanes carry the value).
    Consumed by `equiv_SD` / `equiv_SB` / `equiv_SH` / `equiv_SW`. -/
theorem store_discharge
    (main : Valid_Main C FGL FGL) (mem : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_main_emit : main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e
                   ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = 1) :
    ZiskFv.Airs.MemoryBus.memory_store_lanes_match main r_main e
    ∧ ∃ r_mem, ZiskFv.Airs.MemoryBus.MemBridge.mem_row_matches_entry mem r_mem e ∧ mem.wr r_mem = 1 :=
  ZiskFv.Airs.MemoryBus.MemBridge.memory_store_lanes_match_of_mem_row main mem r_main e h_main_emit

end ZiskFv.Equivalence.Bridge.Mem
