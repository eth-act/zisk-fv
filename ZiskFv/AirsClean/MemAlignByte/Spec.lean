import ZiskFv.AirsClean.MemAlignByte.Row

/-!
# MemAlignByte Spec + Assumptions

The Spec for MemAlignByte is the conjunction of the 5 genuine
algebraic relations the AIR's definitional PIL constraints pin. It
is **non-vacuous** — each clause restates a specific
`mem_align_byte.pil` constraint line (D-2 / V-3, no `Spec := True`):

* `composed_value` — `mem_align_byte.pil:59` (the read-side byte
  recombination): `composed_value = byte_value·BVF + value_8b·V8F
  + value_16b·V16F`.
* `written_composed_value` — `mem_align_byte.pil:83` (write-side
  byte recombination, identical shape with `written_byte_value` as
  the byte source).
* `mem_write_values_0` — `mem_align_byte.pil:87`: the `sel_high_4b`
  multiplexer selecting `direct_value` vs `written_composed_value`.
* `mem_write_values_1` — `mem_align_byte.pil:88`: the dual
  multiplexer lane.
* `bus_byte` — `mem_align_byte.pil:95`: the `is_write` multiplexer
  picking `byte_value` (read) vs `written_byte_value` (write).

The three byte-position factor expressions (`byte_value_factor`,
`value_8b_factor`, `value_16b_factor`) are the `byte_value_factor`
/ `value_8b_factor` / `value_16b_factor` PIL macros
(`mem_align_byte.pil:41-57`).

The Spec additionally pins the `bits(N)` range bounds of the
byte/selector columns the AIR declares:

* `bus_byte.val < 256`        — `mem_align_byte.pil:94` (`bits(8)`).
* `byte_value.val < 256`      — `mem_align_byte.pil:30` (`bits(8)`).
* `is_write.val < 2`          — `mem_align_byte.pil:70` (`bits(1)`).

These are the standard range-checker-bus lookup bounds — the Clean
Component's `soundness` discharges them from `range_bus_sound` (the
range-checker bus, plan F-4: column bounds come from inside
`soundness`, not from `Assumptions`). The `bus_byte` bound is the
fact the LBU / LHU / LWU narrow-load consumers need
(`SubdoublewordLoadLowBytePinning`).

## Trust note

No axioms (the `Spec` is a pure definition; `range_bus_sound` is
consumed only inside the Component's `soundness` proof).
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks

@[reducible]
def byte_value_factor (sel_high_2b sel_high_b : FGL) : FGL :=
  16777216 * sel_high_2b * sel_high_b
  + 65536 * sel_high_2b * (1 - sel_high_b)
  + 256 * (1 - sel_high_2b) * sel_high_b
  + (1 - sel_high_2b) * (1 - sel_high_b)

@[reducible]
def value_8b_factor (sel_high_2b sel_high_b : FGL) : FGL :=
  16777216 * sel_high_2b * (1 - sel_high_b)
  + 65536 * sel_high_2b * sel_high_b
  + 256 * (1 - sel_high_2b) * (1 - sel_high_b)
  + (1 - sel_high_2b) * sel_high_b

@[reducible]
def value_16b_factor (sel_high_2b : FGL) : FGL :=
  65536 * (1 - sel_high_2b) + sel_high_2b

def Assumptions (row : MemAlignByteRow FGL) : Prop :=
  row.sel_high_4b.val < 2 ∧ row.sel_high_2b.val < 2
  ∧ row.sel_high_b.val < 2 ∧ row.is_write.val < 2

/-- MemAlignByte Spec: the 5 derived algebraic relations (composed
    value, written composed value, two mem_write lanes, bus byte) and
    the 3 byte/selector `bits(N)` range bounds. -/
def Spec (row : MemAlignByteRow FGL) : Prop :=
  row.composed_value
    = row.byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
    + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
    + row.value_16b * value_16b_factor row.sel_high_2b
  ∧ row.written_composed_value
    = row.written_byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
    + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
    + row.value_16b * value_16b_factor row.sel_high_2b
  ∧ row.mem_write_values_0
    = row.sel_high_4b * (row.direct_value - row.written_composed_value)
        + row.written_composed_value
  ∧ row.mem_write_values_1
    = row.sel_high_4b * (row.written_composed_value - row.direct_value)
        + row.direct_value
  ∧ row.bus_byte
    = row.is_write * (row.written_byte_value - row.byte_value) + row.byte_value
  -- `bits(N)` range bounds (from `range_bus_sound`, discharged inside
  -- the Component's `soundness`):
  ∧ row.bus_byte.val < 2 ^ 8
  ∧ row.byte_value.val < 2 ^ 8
  ∧ row.is_write.val < 2 ^ 1

end ZiskFv.AirsClean.MemAlignByte
