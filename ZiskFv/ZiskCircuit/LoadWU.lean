import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.ZiskCircuit.LoadD
import ZiskFv.Tactics.LoadArchetype

/-!
Compositional LWU (load word, unsigned / zero-extended) spec.

Sibling of LD under the **`LoadArchetype`** macro for LWU (the
4-byte zero-extension load). Shares nearly all infrastructure with
LD (`Spec/LoadD.lean`):

* Same Main-row mode (`is_external_op = 0, op = OP_COPYB = 1, m32 = 0,
  set_pc = 0, store_pc = 0`) — LWU uses the same ZisK `copyb` internal
  op as LD, differing only in the memory-bus `bytes` (= 4 vs 8) and the
  semantic zero-extension. Both are handled off the Main row.
* Same constraints 9/16/18/19 + PC handshake — `load_subset_holds`
  transfers verbatim.
* Same `memory_load_lanes_match` predicate.

The only LWU-specific addition is **`memory_entry_high_bytes_zero`**:
a hypothesis that the memory-bus entry's high 4 byte lanes (x4..x7) are
zero. ZisK's Memory SM pads the unused high bytes with zero when
`ind_width < 8`; we take this as a compositional hypothesis here (the
audit derives it from the memory-SM permutation-proves).

With the zeroing hypothesis, `memory_entry_toField entry = memory_entry_lo entry`
(bits 32..63 vanish), so the Main row's `c_packed` equals the 32-bit
loaded value directly — matching Sail's `zero_extend 64` semantics for
LWU.

The Sail-level companion and equivalence theorem live in
`Equivalence/LoadWU.lean`; the `LoadArchetype` macro is consumed to
discharge the c-packed equation.
-/

namespace ZiskFv.ZiskCircuit.LoadWU

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.LoadD
open ZiskFv.Tactics.LoadArchetype
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The memory-bus entry's high 4 byte lanes are zero. Holds for any
    `ind_width = 4` load (LWU) because ZisK's Memory SM zero-pads the
    unused high bytes of the 8-byte memory-bus entry.

    The audit derives this from the memory-SM `permutation_proves`;
    here it is a compositional hypothesis. -/
@[simp]
def memory_entry_high_bytes_zero (e : MemoryBusEntry FGL) : Prop :=
  e.x4 = 0 ∧ e.x5 = 0 ∧ e.x6 = 0 ∧ e.x7 = 0

/-- With the high 4 byte lanes zeroed, `memory_entry_hi` collapses to 0. -/
lemma memory_entry_hi_eq_zero {e : MemoryBusEntry FGL}
    (h : memory_entry_high_bytes_zero e) :
    memory_entry_hi e = 0 := by
  obtain ⟨h4, h5, h6, h7⟩ := h
  simp only [memory_entry_hi, h4, h5, h6, h7]
  ring

/-- With the high 4 byte lanes zeroed, the packed 64-bit value reduces
    to the low 32-bit half alone. -/
lemma memory_entry_toField_eq_lo {e : MemoryBusEntry FGL}
    (h : memory_entry_high_bytes_zero e) :
    memory_entry_toField e = memory_entry_lo e := by
  rw [memory_entry_toField_lo_hi, memory_entry_hi_eq_zero h]
  ring

/-- The Main row at `r_main` is in LWU-execution mode: identical to
    LD-mode (`is_external_op = 0, op = OP_COPYB = 1, m32 = 0, set_pc = 0`).
    LWU shares `main_row_in_ld_mode` verbatim — aliased here for
    documentation. -/
@[simp]
def main_row_in_lwu_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_ld_mode m r_main

/-- LWU circuit hypotheses. Extends `load_d_circuit_holds` with the
    high-bytes-zero hypothesis on the memory-bus entry (captures the
    `ind_width = 4` bus-side zero-pad). -/
@[simp]
def load_wu_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL) : Prop :=
  load_d_circuit_holds m r_main next_pc entry
  ∧ memory_entry_high_bytes_zero entry

/-- **Compositional LWU theorem (c-packed).** With the LD-style load
    hypotheses plus the high-bytes-zero bus-entry hypothesis, the Main
    row's packed `c` cell equals the memory-bus entry's low 32-bit
    half — i.e. the 32-bit loaded value zero-extended to 64 bits.

    Proof: apply the `LoadArchetype` macro to get
    `c_packed = memory_entry_toField entry`, then collapse the high
    half to zero using `memory_entry_toField_eq_lo`. -/
lemma load_wu_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_wu_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_lo entry := by
  obtain ⟨h_ld, h_zero⟩ := h
  have h_packed := load_d_compositional m r_main next_pc entry h_ld
  rw [h_packed, memory_entry_toField_eq_lo h_zero]

/-- **Archetype-macro invocation.** Shows the `LoadArchetype` parametric
    lemma (`load_archetype_copyb_c_packed`) closes the LD-shape goal
    that underlies LWU; LWU then adds the high-bytes-zero step on top. -/
lemma load_wu_compositional_via_archetype
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_wu_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_lo entry := by
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
  rw [h_packed, memory_entry_toField_eq_lo h_zero]

/-- **Next-PC for LWU.** Identical derivation to LD — `jmp_offset1 =
    jmp_offset2 = 4` (from `transpile_LWU`) + `flag = 0` (constraint
    18) collapses the PC handshake to `pc + 4`. -/
lemma load_wu_next_pc_concrete
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_wu_circuit_holds m r_main next_pc entry)
    (h_jmp1 : m.jmp_offset1 r_main = 4)
    (h_jmp2 : m.jmp_offset2 r_main = 4) :
    next_pc = m.pc r_main + 4 := by
  exact load_d_next_pc_concrete m r_main next_pc entry h.1 h_jmp1 h_jmp2

end ZiskFv.ZiskCircuit.LoadWU
