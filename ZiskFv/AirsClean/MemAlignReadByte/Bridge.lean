import ZiskFv.AirsClean.MemAlignReadByte.Circuit
import ZiskFv.Airs.MemAlignReadByte
import ZiskFv.Channels.RangeBusSoundness

/-!
# `Valid_MemAlignReadByte` ↔ `MemAlignReadByteRow` compatibility + Component re-root

Connects the existing `Valid_MemAlignReadByte` interface (a record with
named column accessors `ℕ → FGL`) to the Clean Component's
`MemAlignReadByteRow`, and exposes the **C2 re-root entry point**
`byte_value_in_range_via_component` — the narrow-load consumers
(LBU / LHU / LWU) source MemAlignReadByte's `byte_value < 256` range
fact from the Clean Component's proven `Spec` rather than from a
caller-supplied promise.

## Trust note

No axioms. The Component-routed bridge inherits `circuit`'s closure
(`memAlignReadByte_circuit_completeness` + `range_bus_sound`); both are
already in every load opcode's closure.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks
open ZiskFv.Channels.RangeBusSoundness (range_bus_sound)


/-- Project a `Valid_MemAlignReadByte` at row `r` into a Clean
    `MemAlignReadByteRow FGL`. -/
@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ)
    : MemAlignReadByteRow FGL where
  sel_high_4b := v.sel_high_4b r
  sel_high_2b := v.sel_high_2b r
  sel_high_b := v.sel_high_b r
  direct_value := v.direct_value r
  composed_value := v.composed_value r
  value_16b := v.value_16b r
  value_8b := v.value_8b r
  byte_value := v.byte_value r
  addr_w := v.addr_w r
  step := v.step r

/-- The 4 F-typed MemAlignReadByte row constraints at row `r`,
    expressed against a `Valid_MemAlignReadByte`. -/
def constraints_at
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ) : Prop :=
  v.sel_high_4b r * (1 - v.sel_high_4b r) = 0
  ∧ v.sel_high_2b r * (1 - v.sel_high_2b r) = 0
  ∧ v.sel_high_b r * (1 - v.sel_high_b r) = 0
  ∧ v.composed_value r - (v.byte_value r
        * byte_value_factor (v.sel_high_2b r) (v.sel_high_b r)
      + v.value_8b r * value_8b_factor (v.sel_high_2b r) (v.sel_high_b r)
      + v.value_16b r * value_16b_factor (v.sel_high_2b r)) = 0

/-- **Bridge theorem.** Given a row of a `Valid_MemAlignReadByte`
    satisfying the 4 Clean Component constraints + the boolean
    assumptions + the `bits(8)` range bound, the MemAlignReadByte Spec
    holds. -/
theorem spec_of_valid
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r)
    (h_byte_value_range : (v.byte_value r).val < 2 ^ 8) :
    Spec (rowAt v r) := by
  obtain ⟨h_4b, h_2b, h_b, h_composed⟩ := h_constraints
  exact soundness (rowAt v r) h_assumptions h_4b h_2b h_b h_composed
    h_byte_value_range

/-! ## C2 re-root — Component-routed `byte_value` range

The narrow-load consumers (LBU / LHU / LWU) need MemAlignReadByte's
`byte_value` column range-bounded to `< 256`. They source it here —
**through the Clean Component's proven `Spec`** — from the AIR's
own `core_every_row` PIL constraints, rather than as a
caller-supplied promise hypothesis.

`Spec` carries the `bits(8)` `byte_value` bound as its 2nd conjunct;
that conjunct is discharged inside `circuit.soundness` from
`range_bus_sound`. Routing through `MemAlignReadByte.spec_via_component`
makes the Clean Component genuinely load-bearing for the load
opcodes: their `#print axioms` reaches `memAlignReadByte_circuit_completeness`.
-/

/-- **C2 re-root entry point.** From the MemAlignReadByte AIR's
    `core_every_row` PIL constraints at row `r`, derive `byte_value`'s
    `< 256` range bound **through the Clean Component** (its proven
    `Spec`, via `spec_via_component`). This is what the LBU / LHU /
    LWU narrow loads consume — making `memAlignReadByteComponent`
    load-bearing for those opcodes. -/
theorem byte_value_in_range_via_component
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ)
    (h_core : ZiskFv.Airs.MemAlignReadByte.core_every_row v r) :
    (v.byte_value r).val < 2 ^ 8 := by
  obtain ⟨h_b0, h_b1, h_b2, h_composed⟩ := h_core
  -- `rowAt v r` projects the AIR row into the Clean Component row;
  -- each `rowAt` field is `@[reducible]`-defeq to `v.<col> r`.
  have h_spec : Spec (rowAt v r) :=
    spec_via_component (rowAt v r) h_composed h_b0 h_b1 h_b2
      (range_bus_sound (rowAt v r) (fun row _ => row.byte_value) 8 trivial 0)
  exact h_spec.2

end ZiskFv.AirsClean.MemAlignReadByte
