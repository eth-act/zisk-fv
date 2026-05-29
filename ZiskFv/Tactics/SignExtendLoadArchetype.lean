import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus

/-!
**Sign-extend load archetype macros / generic lemmas.**

The three RV64 signed loads (LW / LH / LB) share a single ZisK
microinstruction shape under `fn load_op` with an external-op opcode:

* `op ∈ {OP_SIGNEXTEND_B, OP_SIGNEXTEND_H, OP_SIGNEXTEND_W}`
  (`zisk_ops.rs:419-421`, type `BinaryE`);
* `is_external_op = 1` — bus hop to the `BinaryExtension` SM;
* `flag = 0` (the `op_signextend_*` helpers all return `(_, false)`);
* `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`;
* `m32 = 1` for LW (the `"_w"` variant) and `m32 = 0` for LH / LB.

Unlike the zero-extension loads (LD / LWU / LHU / LBU — `OP_COPYB`
internal op, Main constraint 9 gives `c = b` directly), signed loads
materialize the extended value on the operation-bus reply; the Main
AIR's `c` lanes are populated by the BinaryExtension SM's bus push.
As a consequence the compositional spec exposes a `matches_entry`
hypothesis tying a Main-emitted `OperationBusEntry` to a secondary
entry supplied by the caller — the BinaryExtension-side emission is
a separate audit obligation (same decision as SLLW / MULW).

Structurally this archetype is the load-family analogue of
`Tactics/ShiftArchetype.lean`: it parameterizes over the opcode
literal (`OP_SIGNEXTEND_B/H/W`) and the `m32` bit, asserts the
standard load mode pins on the Main row, and derives the two
bus-emission corollaries (`a_hi = b_hi = 0` when `m32 = 1`;
pass-through when `m32 = 0`). The `a` lanes are not pinned by the
transpile contract to a specific register-read here because the
archetype focuses on the bus match rather than the full address
chain; concrete opcodes pin `a` lanes at the equivalence layer.

## Parameterization

* `opcode_lit : FGL` — `OP_SIGNEXTEND_W = 41` (LW),
  `OP_SIGNEXTEND_H = 40` (LH), `OP_SIGNEXTEND_B = 39` (LB).
* `m32_val : FGL` — `1` for LW, `0` for LH / LB. The archetype lemmas
  fire for either value; callers pin one at the equivalence theorem
  layer via the `transpile_L{W,H,B}` axiom witnesses.

## Usage pattern

```lean
-- LW case:
lemma equiv_LW_circuit (...) := by
  have := sign_extend_load_archetype_m32_one_zeros_bus m r_main bus_entry
    (opcode_lit := OP_SIGNEXTEND_W) h_circuit_lw
  ...
```

See `Spec/LoadWord.lean` / `Spec/LoadHalf.lean` / `Spec/LoadByte.lean`
for the concrete specializations.

## Why a new archetype (vs. extending `LoadArchetype`)

`Tactics/LoadArchetype.lean` is explicitly scoped to
`OP_COPYB = 1` + `is_external_op = 0` — its
`load_archetype_copyb_circuit_holds` predicate hard-codes
`main_row_in_load_mode m r_main (1 : FGL) (0 : FGL)`. Generalizing it
over `is_ext ∈ {0, 1}` / `opcode_lit` would need a split on the two
paths (internal vs. external) in the `c_packed` conclusion, which
does not generalize cleanly: for internal ops the conclusion is
`c_packed = memory_entry_toField entry`; for external ops the `c`
lanes are populated by the BinaryExtension SM's bus push, not the
memory-bus entry. Duplication into a sibling archetype is the
preferred path; the two archetypes share the Main-row mode /
PC-handshake structure but diverge in the `c`-populating mechanism.
-/

namespace ZiskFv.Tactics.SignExtendLoadArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted


/-- **Archetype mode predicate.** A Main row is in sign-extend-load
    execution mode for a given Zisk opcode literal and `m32` bit when
    `is_external_op = 1`, `op = opcode_lit`, `m32 = m32_val`,
    `flag = 0`, `set_pc = 0`. `m32_val = 1` covers LW; `m32_val = 0`
    covers LH / LB. -/
@[simp]
def main_row_in_sign_extend_load_mode
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (opcode_lit m32_val : FGL) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = m32_val
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- **Archetype circuit-holds.** Parametric over opcode literal and
    `m32`. Mirrors `Tactics/ShiftArchetype.lean` and its sibling
    `shift_archetype_circuit_holds`. Conclusion is a Main-side
    `matches_entry` to a secondary bus entry the caller supplies
    from the BinaryExtension SM row. -/
@[simp]
def sign_extend_load_archetype_circuit_holds
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit m32_val : FGL) : Prop :=
  main_row_in_sign_extend_load_mode m r_main opcode_lit m32_val
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- **Archetype m32 = 1 bus-zeroing theorem.** For the LW case
    (`m32 = 1`), the bus entry has `a_hi = b_hi = 0`. This mirrors
    `Circuit.Shift.sllw_compositional` and the
    `shift_archetype_m32_one_zeros_bus` theorem. -/
lemma sign_extend_load_archetype_m32_one_zeros_bus
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit : FGL)
    (h : sign_extend_load_archetype_circuit_holds m r_main bus_entry
           opcode_lit 1) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 := by
  obtain ⟨h_mode, h_match⟩ := h
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  obtain ⟨_, _, _, h_ahi, _, h_bhi, _, _, _, _, _, _⟩ := h_match
  refine ⟨?_, ?_⟩
  · rw [← h_ahi]
    simp only [opBus_row_Main]
    rw [h_m32]; simp
  · rw [← h_bhi]
    simp only [opBus_row_Main]
    rw [h_m32]; simp

/-- **Archetype m32 = 0 bus-passthrough theorem.** For LH / LB
    (`m32 = 0`), the bus carries `a[1]` / `b[1]` verbatim; the
    `(1 - m32) = 1` factor leaves them unchanged. Mirror of
    `shift_archetype_m32_zero_passthrough_bus`. -/
lemma sign_extend_load_archetype_m32_zero_passthrough_bus
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit : FGL)
    (h : sign_extend_load_archetype_circuit_holds m r_main bus_entry
           opcode_lit 0) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main := by
  obtain ⟨h_mode, h_match⟩ := h
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  obtain ⟨_, _, _, h_ahi, _, h_bhi, _, _, _, _, _, _⟩ := h_match
  refine ⟨?_, ?_⟩
  · rw [← h_ahi]
    simp only [opBus_row_Main]
    rw [h_m32]
    ring
  · rw [← h_bhi]
    simp only [opBus_row_Main]
    rw [h_m32]
    ring

/-- **Archetype multiplicity passthrough.** The bus entry's
    multiplicity matches the Main row's `is_external_op` — = 1 for
    signed loads. Useful at the equivalence layer for tying the Main
    bus emission to the BinaryExtension SM's bus pop. -/
lemma sign_extend_load_archetype_multiplicity_one
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit m32_val : FGL)
    (h : sign_extend_load_archetype_circuit_holds m r_main bus_entry
           opcode_lit m32_val) :
    bus_entry.multiplicity = 1 := by
  obtain ⟨h_mode, h_match⟩ := h
  obtain ⟨h_ext, _, _, _, _⟩ := h_mode
  obtain ⟨h_mult, _, _, _, _, _, _, _, _, _, _, _⟩ := h_match
  rw [← h_mult]
  simp only [opBus_row_Main]
  exact h_ext

/-- **Archetype op passthrough.** The bus entry's `op` field matches
    the Main row's `op` — = `opcode_lit` for signed loads. -/
lemma sign_extend_load_archetype_op_passthrough
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit m32_val : FGL)
    (h : sign_extend_load_archetype_circuit_holds m r_main bus_entry
           opcode_lit m32_val) :
    bus_entry.op = opcode_lit := by
  obtain ⟨h_mode, h_match⟩ := h
  obtain ⟨_, h_op, _, _, _⟩ := h_mode
  obtain ⟨_, h_bus_op, _, _, _, _, _, _, _, _, _, _⟩ := h_match
  rw [← h_bus_op]
  simp only [opBus_row_Main]
  exact h_op

end ZiskFv.Tactics.SignExtendLoadArchetype
