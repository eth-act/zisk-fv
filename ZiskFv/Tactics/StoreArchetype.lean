import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.ZiskCircuit.StoreD

/-!
**Store archetype macros / generic lemmas.**

Write-side mirror of `Tactics/LoadArchetype.lean`. The four RV64IM
integer stores (SD/SW/SH/SB) share a single ZisK transpilation shape:
one microinstruction with `src_a = reg(rs1)`, `src_b = reg(rs2)`
(the store *value*), `store = ind(imm, ...)` (memory write),
`j(4, 4)`, `op = "copyb"` (`OP_COPYB = 1`, `OpType::Internal`),
`is_external_op = 0`. **All four stores share `op = "copyb"`** —
there's no signed/unsigned split for stores (the value bytes are
just written verbatim), so unlike loads there is no sign-extension
sub-family.

The archetype closes SD (width = 8). SW/SH/SB fall out by
instantiation with a width-specific "high-byte zeroing" assumption on
the memory-bus
write entry (SW zeros x4..x7, SH zeros x2..x7, SB zeros x1..x7) —
i.e. the unused bytes of the 8-lane `MemoryBusEntry` are zeroed
from the Main row's byte-emission side, and the spec-side packing
folds them harmlessly into `memory_entry_toField`.

## Usage pattern

```lean
-- SW case (width = 4, op = OP_COPYB = 1):
theorem equiv_SW (...) := by
  have := store_archetype_c_packed m r next_pc entry h_circuit
  -- apply `memory_entry_toField` lemmas specialized to width = 4
  ...
```

## Why a separate module (vs extending LoadArchetype)

`Tactics/LoadArchetype.lean` deliberately uses `memory_load_lanes_match`
(on `b`), which reflects the *assume-side* matching for loads. The
store archetype uses `memory_store_lanes_match` (on `c`, the *prove-side*
matching for stores). While constraint 9/16 makes them interconvertible,
keeping the two archetype modules separate lets each carry its own
mode predicate (`main_row_in_load_mode` vs `main_row_in_store_mode`)
and circuit-holds packaging — matching the semantic direction of each
archetype consumer. Shared infrastructure lives in `Airs/MemoryBus.lean`.
-/

namespace ZiskFv.Tactics.StoreArchetype

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Archetype mode predicate.** A Main row is in store-execution mode
    for a given Zisk opcode literal when `is_external_op`, `op`, `m32`,
    and `set_pc` match the transpile-axiom witnesses. All four RV64
    stores (SD/SW/SH/SB) use `OP_COPYB = 1` and `is_external_op = 0` —
    the only sub-family split is by the operand width on the bus, not
    by the Main-level mode. -/
@[simp]
def main_row_in_store_mode
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (opcode_lit : FGL) (is_ext : FGL) : Prop :=
  m.is_external_op r_main = is_ext
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- **Archetype circuit-holds (copyb stores).** Parametric version of
    `Circuit.StoreD.store_d_circuit_holds`. Covers the entire integer
    store family (SD/SW/SH/SB) since all share `OP_COPYB`. -/
@[simp]
def store_archetype_copyb_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL) : Prop :=
  store_subset_holds m r_main next_pc
  ∧ main_row_in_store_mode m r_main (1 : FGL) (0 : FGL)
  ∧ memory_store_lanes_match m r_main entry

/-- **Archetype theorem (copyb stores, c-packed).** Same shape as
    `Circuit.StoreD.store_d_compositional` but expressed in the
    parametric `store_archetype_copyb_circuit_holds` form. SW/SH/SB
    close via instantiation + a width-specific zeroing-of-high-bytes
    assumption on the memory-bus write entry. -/
lemma store_archetype_copyb_c_packed
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : store_archetype_copyb_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_toField entry := by
  obtain ⟨h_subset, h_mode, h_mem⟩ := h
  obtain ⟨h_ext, h_op, h_m32, h_setpc⟩ := h_mode
  apply store_d_compositional m r_main next_pc entry
  refine ⟨h_subset, ?_, h_mem⟩
  exact ⟨h_ext, h_op, h_m32, h_setpc⟩

/-- **Archetype next-PC (copyb stores).** Same shape as
    `Circuit.StoreD.store_d_next_pc_concrete`: when `jmp_offset1 =
    jmp_offset2 = 4`, the next-pc is `pc + 4`. Holds uniformly for
    SD/SW/SH/SB since they all use `j(4, 4)` in the Zisk
    transpiler. -/
lemma store_archetype_copyb_next_pc
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : store_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_jmp1 : m.jmp_offset1 r_main = 4)
    (h_jmp2 : m.jmp_offset2 r_main = 4) :
    next_pc = m.pc r_main + 4 := by
  obtain ⟨h_subset, h_mode, h_mem⟩ := h
  obtain ⟨h_ext, h_op, h_m32, h_setpc⟩ := h_mode
  apply store_d_next_pc_concrete m r_main next_pc entry _ h_jmp1 h_jmp2
  exact ⟨h_subset, ⟨h_ext, h_op, h_m32, h_setpc⟩, h_mem⟩

end ZiskFv.Tactics.StoreArchetype
