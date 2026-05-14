import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.ZiskCircuit.LoadD
import ZiskFv.Tactics.LoadArchetype

/-!
Compositional LBU (load byte, unsigned / zero-extended) spec.

Sibling of LD/LWU/LHU under the **`LoadArchetype`** macro for LBU
(the 1-byte zero-extension load, narrowest width). Shares nearly all
infrastructure with the wider variants:

* Same Main-row mode (`is_external_op = 0, op = OP_COPYB = 1, m32 = 0,
  set_pc = 0, store_pc = 0`) — LBU uses the same ZisK `copyb` internal
  op, differing only in the memory-bus `bytes` (= 1 vs 2 vs 4 vs 8).
* Same constraints 9/16/18/19 + PC handshake — `load_subset_holds`
  transfers verbatim.
* Same `memory_load_lanes_match` predicate.

The LBU-specific addition is **`memory_entry_high_bytes_zero_bu`**:
a hypothesis that the memory-bus entry's 7 high byte lanes (x1..x7)
are zero. ZisK's Memory SM pads the unused high bytes with zero when
`ind_width < 8`; this is carried as a compositional hypothesis here
(the audit derives it from the memory-SM permutation).

With the zeroing hypothesis, `memory_entry_toField entry` collapses to
`entry.x0` — the single loaded byte — matching Sail's zero-extension
semantics for LBU.

The Sail-level companion and equivalence theorem live in
`Equivalence/LoadBU.lean`; the `LoadArchetype` macro is consumed to
discharge the c-packed equation.
-/

namespace ZiskFv.ZiskCircuit.LoadBU

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.LoadD
open ZiskFv.Tactics.LoadArchetype
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The memory-bus entry's 7 high byte lanes (x1..x7) are zero. Holds
    for any `ind_width = 1` load (LBU) because ZisK's Memory SM
    zero-pads the unused high bytes of the 8-byte memory-bus entry.

    The audit derives this from the memory-SM `permutation_proves`;
    here it is a compositional hypothesis. -/
@[simp]
def memory_entry_high_bytes_zero_bu (e : MemoryBusEntry FGL) : Prop :=
  e.x1 = 0 ∧ e.x2 = 0 ∧ e.x3 = 0 ∧ e.x4 = 0
    ∧ e.x5 = 0 ∧ e.x6 = 0 ∧ e.x7 = 0

/-- The 8-bit value (single byte) of a memory-bus entry: `x0`. -/
@[simp]
def memory_entry_byte (e : MemoryBusEntry FGL) : FGL :=
  e.x0

/-- With the 7 high byte lanes zeroed, the packed 64-bit value
    `memory_entry_toField` reduces to `x0` alone. -/
lemma memory_entry_toField_eq_byte {e : MemoryBusEntry FGL}
    (h : memory_entry_high_bytes_zero_bu e) :
    memory_entry_toField e = memory_entry_byte e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [memory_entry_toField, memory_entry_byte, h1, h2, h3, h4, h5, h6, h7]
  ring

/-- The Main row at `r_main` is in LBU-execution mode: identical to
    LD-mode. LBU shares `main_row_in_ld_mode` verbatim — aliased here
    for documentation. -/
@[simp]
def main_row_in_lbu_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_ld_mode m r_main

/-- LBU circuit hypotheses. Extends `load_d_circuit_holds` with the
    7-byte high-bytes-zero hypothesis on the memory-bus entry. -/
@[simp]
def load_bu_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL) : Prop :=
  load_d_circuit_holds m r_main next_pc entry
  ∧ memory_entry_high_bytes_zero_bu entry

/-- **Compositional LBU theorem (c-packed).** With the LD-style load
    hypotheses plus the 7-high-bytes-zero bus-entry hypothesis, the
    Main row's packed `c` cell equals the memory-bus entry's single
    byte — i.e. the 8-bit loaded value zero-extended to 64 bits.

    Proof: apply the `LoadArchetype` macro to get
    `c_packed = memory_entry_toField entry`, then collapse to `x0`
    using `memory_entry_toField_eq_byte`. -/
lemma load_bu_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_bu_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_byte entry := by
  obtain ⟨h_ld, h_zero⟩ := h
  have h_packed := load_d_compositional m r_main next_pc entry h_ld
  rw [h_packed, memory_entry_toField_eq_byte h_zero]

/-- **Archetype-macro invocation.** Shows the `LoadArchetype` parametric
    lemma (`load_archetype_copyb_c_packed`) closes the LD-shape goal
    that underlies LBU; LBU then adds the high-bytes-zero step on top. -/
lemma load_bu_compositional_via_archetype
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_bu_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_byte entry := by
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
  rw [h_packed, memory_entry_toField_eq_byte h_zero]

/-- **Next-PC for LBU.** Identical derivation to LD / LWU / LHU —
    `jmp_offset1 = jmp_offset2 = 4` (from `transpile_LBU`) + `flag = 0`
    (constraint 18) collapses the PC handshake to `pc + 4`. -/
lemma load_bu_next_pc_concrete
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_bu_circuit_holds m r_main next_pc entry)
    (h_jmp1 : m.jmp_offset1 r_main = 4)
    (h_jmp2 : m.jmp_offset2 r_main = 4) :
    next_pc = m.pc r_main + 4 := by
  exact load_d_next_pc_concrete m r_main next_pc entry h.1 h_jmp1 h_jmp2

end ZiskFv.ZiskCircuit.LoadBU
