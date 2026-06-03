import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.ZiskCircuit.LoadD
import ZiskFv.Tactics.LoadArchetype

/-!
Compositional LHU (load halfword, unsigned / zero-extended) spec.

Sibling of LD / LWU under the **`LoadArchetype`** macro for LHU
(the 2-byte zero-extension load). Shares nearly all infrastructure
with LD (`Spec/LoadD.lean`) and LWU (`Spec/LoadWU.lean`):

* Same Main-row mode (`is_external_op = 0, op = OP_COPYB = 1, m32 = 0,
  set_pc = 0, store_pc = 0`) — LHU uses the same ZisK `copyb` internal
  op, differing only in the memory-bus `bytes` (= 2 vs 4 vs 8) and the
  semantic zero-extension. Both are handled off the Main row.
* Same constraints 9/16/18/19 + PC handshake — `load_subset_holds`
  transfers verbatim.
* Same `memory_load_lanes_match` predicate.

The LHU-specific addition is **`memory_entry_high_bytes_zero_hu`**: a
hypothesis that the memory-bus entry's high 6 byte lanes (x2..x7) are
zero. ZisK's Memory SM pads the unused high bytes with zero when
`ind_width < 8`; we take this as a compositional hypothesis here (the
audit derives it from the memory-SM permutation-proves).

With the zeroing hypothesis, `memory_entry_toField entry` collapses to
the 16-bit value at x0/x1, matching Sail's zero-extension semantics for
LHU.

The Sail-level companion and equivalence theorem live in
`Equivalence/Lhu.lean`; the `LoadArchetype` macro is consumed to
discharge the c-packed equation.
-/

namespace ZiskFv.ZiskCircuit.LoadHU

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.LoadD
open ZiskFv.Tactics.LoadArchetype
open ZiskFv.Trusted


/-- The memory-bus entry's high chunk is zero and the low chunk
    holds a 16-bit half (`value_0.val < 65536`). Holds for any
    `ind_width = 2` load (LHU) because ZisK's Memory SM zero-pads
    the unused high bytes of the 8-byte memory-bus entry.

    The audit derives this from the memory-SM `permutation_proves`;
    here it is a compositional hypothesis. -/
@[simp]
def memory_entry_high_bytes_zero_hu (e : MemoryBusEntry FGL) : Prop :=
  e.value_1 = 0 ∧ e.value_0.val < 65536

/-- The 16-bit low half of a memory-bus entry — under the LHU
    zeroing hypothesis the entire chunk-pack collapses to
    `value_0`, which holds the half-word as an FGL. -/
@[simp]
def memory_entry_half (e : MemoryBusEntry FGL) : FGL :=
  e.value_0

/-- With the LHU zeroing hypothesis, the packed 64-bit value
    `memory_entry_toField` reduces to the 16-bit half alone. -/
lemma memory_entry_toField_eq_half {e : MemoryBusEntry FGL}
    (h : memory_entry_high_bytes_zero_hu e) :
    memory_entry_toField e = memory_entry_half e := by
  obtain ⟨h_v1, _⟩ := h
  show e.value_0 + e.value_1 * 4294967296 = e.value_0
  rw [h_v1]; ring

/-- The Main row at `r_main` is in LHU-execution mode: identical to
    LD-mode (`is_external_op = 0, op = OP_COPYB = 1, m32 = 0,
    set_pc = 0`). LHU shares `main_row_in_ld_mode` verbatim — aliased
    here for documentation. -/
@[simp]
def main_row_in_lhu_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_ld_mode m r_main

/-- LHU circuit hypotheses. Extends `load_d_circuit_holds` with the
    high-bytes-zero hypothesis (6 high bytes) on the memory-bus entry. -/
@[simp]
def load_hu_circuit_holds
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL) : Prop :=
  load_d_circuit_holds m r_main next_pc entry
  ∧ memory_entry_high_bytes_zero_hu entry

/-- **Compositional LHU theorem (c-packed).** With the LD-style load
    hypotheses plus the high-bytes-zero bus-entry hypothesis, the Main
    row's packed `c` cell equals the memory-bus entry's 16-bit half —
    i.e. the 16-bit loaded value zero-extended to 64 bits.

    Proof: apply the `LoadArchetype` macro to get
    `c_packed = memory_entry_toField entry`, then collapse the high
    54 bits to zero using `memory_entry_toField_eq_half`. -/
lemma load_hu_compositional
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_hu_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_half entry := by
  obtain ⟨h_ld, h_zero⟩ := h
  have h_packed := load_d_compositional m r_main next_pc entry h_ld
  rw [h_packed, memory_entry_toField_eq_half h_zero]

/-- **Archetype-macro invocation.** Shows the `LoadArchetype` parametric
    lemma (`load_archetype_copyb_c_packed`) closes the LD-shape goal
    that underlies LHU; LHU then adds the high-bytes-zero step on top. -/
lemma load_hu_compositional_via_archetype
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_hu_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_half entry := by
  obtain ⟨h_ld, h_zero⟩ := h
  obtain ⟨h_subset, h_mode, h_mem⟩ := h_ld
  obtain ⟨h_ext, h_op, h_m32, h_setpc⟩ := h_mode
  -- Package into the archetype's parametric form.
  have h_arch :
      load_archetype_copyb_circuit_holds m r_main next_pc entry := by
    refine ⟨h_subset, ?_, h_mem⟩
    exact ⟨h_ext, h_op, h_m32, h_setpc⟩
  have h_packed :=
    load_archetype_copyb_c_packed m r_main next_pc entry h_arch
  rw [h_packed, memory_entry_toField_eq_half h_zero]

/-- **Next-PC for LHU.** Identical derivation to LD / LWU — `jmp_offset1
    = jmp_offset2 = 4` (from `transpile_LHU`) + `flag = 0` (constraint
    18) collapses the PC handshake to `pc + 4`. -/
lemma load_hu_next_pc_concrete
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_hu_circuit_holds m r_main next_pc entry)
    (h_jmp1 : m.jmp_offset1 r_main = 4)
    (h_jmp2 : m.jmp_offset2 r_main = 4) :
    next_pc = m.pc r_main + 4 := by
  exact load_d_next_pc_concrete m r_main next_pc entry h.1 h_jmp1 h_jmp2

end ZiskFv.ZiskCircuit.LoadHU
