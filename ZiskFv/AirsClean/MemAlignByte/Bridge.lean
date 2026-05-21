import ZiskFv.AirsClean.MemAlignByte.Circuit
import ZiskFv.Airs.MemAlignByte

/-!
# `Valid_MemAlignByte` ↔ `MemAlignByteRow` compatibility + Component re-root

Connects the existing `Valid_MemAlignByte` interface (a record with
named column accessors `ℕ → FGL`) to the Clean Component's
`MemAlignByteRow`, and exposes the **C1 re-root entry point**
`bus_byte_in_range_via_component` — the narrow-load consumers
(LBU / LHU / LWU) source MemAlignByte's `bus_byte < 256` range fact
from the Clean Component's proven `Spec` rather than from a
caller-supplied promise.

## Trust note

No axioms. The Component-routed bridge inherits `circuit`'s closure
(`memAlignByte_circuit_completeness` + `range_bus_sound`); both are
already in every load opcode's closure.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks


@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ)
    : MemAlignByteRow FGL where
  sel_high_4b := v.sel_high_4b r
  sel_high_2b := v.sel_high_2b r
  sel_high_b := v.sel_high_b r
  direct_value := v.direct_value r
  composed_value := v.composed_value r
  written_composed_value := v.written_composed_value r
  written_byte_value := v.written_byte_value r
  value_16b := v.value_16b r
  value_8b := v.value_8b r
  byte_value := v.byte_value r
  addr_w := v.addr_w r
  step := v.step r
  is_write := v.is_write r
  mem_write_values_0 := v.mem_write_values_0 r
  mem_write_values_1 := v.mem_write_values_1 r
  bus_byte := v.bus_byte r

/-- The 9 F-typed MemAlignByte row constraints at row `r`, expressed
    against a `Valid_MemAlignByte`. The 5 definitional identities (4,
    6, 7, 8, 9) are what `soundness` consumes; the 4 booleans (1, 2,
    3, 5) live in `Assumptions`. -/
def constraints_at
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) : Prop :=
  v.composed_value r - (v.byte_value r
      * byte_value_factor (v.sel_high_2b r) (v.sel_high_b r)
    + v.value_8b r * value_8b_factor (v.sel_high_2b r) (v.sel_high_b r)
    + v.value_16b r * value_16b_factor (v.sel_high_2b r)) = 0
  ∧ v.written_composed_value r - (v.written_byte_value r
      * byte_value_factor (v.sel_high_2b r) (v.sel_high_b r)
    + v.value_8b r * value_8b_factor (v.sel_high_2b r) (v.sel_high_b r)
    + v.value_16b r * value_16b_factor (v.sel_high_2b r)) = 0
  ∧ v.mem_write_values_0 r
      - (v.sel_high_4b r * (v.direct_value r - v.written_composed_value r)
         + v.written_composed_value r) = 0
  ∧ v.mem_write_values_1 r
      - (v.sel_high_4b r * (v.written_composed_value r - v.direct_value r)
         + v.direct_value r) = 0
  ∧ v.bus_byte r
      - (v.is_write r * (v.written_byte_value r - v.byte_value r)
         + v.byte_value r) = 0

/-- **Bridge theorem.** -/
theorem spec_of_valid
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r)
    (h_bus_byte_range : (v.bus_byte r).val < 2 ^ 8)
    (h_byte_value_range : (v.byte_value r).val < 2 ^ 8)
    (h_is_write_range : (v.is_write r).val < 2 ^ 1) :
    Spec (rowAt v r) := by
  obtain ⟨h_c, h_wc, h_m0, h_m1, h_bb⟩ := h_constraints
  exact soundness (rowAt v r) h_assumptions h_c h_wc h_m0 h_m1 h_bb
    h_bus_byte_range h_byte_value_range h_is_write_range

/-! ## C1 re-root — Component-routed `bus_byte` range

The narrow-load consumers (LBU / LHU / LWU) need MemAlignByte's
`bus_byte` column range-bounded to `< 256`. They source it here —
**through the Clean Component's proven `Spec`** — from the AIR's
own `core_every_row` PIL constraints, rather than as a
caller-supplied promise hypothesis.

`Spec` carries the `bits(8)` `bus_byte` bound as its 6th conjunct;
that conjunct is discharged inside `circuit.soundness` from
`range_bus_sound`. Routing through `MemAlignByte.spec_via_component`
makes the Clean Component genuinely load-bearing for the load
opcodes: their `#print axioms` reaches `memAlignByte_circuit_completeness`.
-/

/-- **C1 re-root entry point.** From the MemAlignByte AIR's
    `core_every_row` PIL constraints at row `r`, derive `bus_byte`'s
    `< 256` range bound **through the Clean Component** (its proven
    `Spec`, via `spec_via_component`). This is what the LBU / LHU /
    LWU narrow loads consume — making `memAlignByteComponent`
    load-bearing for those opcodes. -/
theorem bus_byte_in_range_via_component
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ)
    (h_core : ZiskFv.Airs.MemAlignByte.core_every_row v r) :
    (v.bus_byte r).val < 2 ^ 8 := by
  obtain ⟨h_b0, h_b1, h_b2, h_composed, h_b4, h_written, h_m0, h_m1, h_bus⟩ := h_core
  -- `rowAt v r` projects the AIR row into the Clean Component row;
  -- each `rowAt` field is `@[reducible]`-defeq to `v.<col> r`.
  have h_spec :
      Spec (rowAt v r) :=
    spec_via_component (rowAt v r) h_composed h_written h_m0 h_m1 h_bus
      h_b0 h_b1 h_b2 h_b4
  exact h_spec.2.2.2.2.2.1

end ZiskFv.AirsClean.MemAlignByte
