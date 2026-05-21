import ZiskFv.AirsClean.MemAlignReadByte.Row

/-!
# MemAlignReadByte Spec + Assumptions

The Clean-side spec for the MemAlignReadByte AIR. It is **non-vacuous**
— each clause restates a specific `mem_align_byte.pil` constraint line
(D-2 / V-3, no `Spec := True`):

* `composed_value` — `mem_align_byte.pil:57` (the read-side byte
  recombination): `composed_value = byte_value·BVF + value_8b·V8F
  + value_16b·V16F`.

The three byte-position factor expressions (`byte_value_factor`,
`value_8b_factor`, `value_16b_factor`) are the `byte_value_factor`
/ `value_8b_factor` / `value_16b_factor` PIL macros
(`mem_align_byte.pil:44-56`).

The Spec additionally pins the `bits(N)` range bound of the byte
column the AIR declares:

* `byte_value.val < 256`      — `mem_align_byte.pil:30` (`bits(8)`).

This is the standard range-checker-bus lookup bound — the Clean
Component's `soundness` discharges it from `range_bus_sound` (the
range-checker bus, plan F-4: column bounds come from inside
`soundness`, not from `Assumptions`). The `byte_value` bound is the
fact the LBU / LHU / LWU narrow-load consumers need
(`SubdoublewordLoadLowBytePinning.read_byte_value_lt`).

## Trust note

No axioms (the `Spec` is a pure definition; `range_bus_sound` is
consumed only inside the Component's `soundness` proof).
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks

/-- The byte-position factor for `byte_value`, parameterized by the
    selector bits. PIL `mem_align_byte.pil:44`. -/
@[reducible]
def byte_value_factor (sel_high_2b sel_high_b : FGL) : FGL :=
  16777216 * sel_high_2b * sel_high_b
  + 65536 * sel_high_2b * (1 - sel_high_b)
  + 256 * (1 - sel_high_2b) * sel_high_b
  + (1 - sel_high_2b) * (1 - sel_high_b)

/-- The byte-position factor for `value_8b`. -/
@[reducible]
def value_8b_factor (sel_high_2b sel_high_b : FGL) : FGL :=
  16777216 * sel_high_2b * (1 - sel_high_b)
  + 65536 * sel_high_2b * sel_high_b
  + 256 * (1 - sel_high_2b) * (1 - sel_high_b)
  + (1 - sel_high_2b) * sel_high_b

/-- The byte-position factor for `value_16b`. -/
@[reducible]
def value_16b_factor (sel_high_2b : FGL) : FGL :=
  65536 * (1 - sel_high_2b) + sel_high_2b

/-- Assumptions on a MemAlignReadByte row: range bounds on the
    selector bits. -/
def Assumptions (row : MemAlignReadByteRow FGL) : Prop :=
  row.sel_high_4b.val < 2 ∧ row.sel_high_2b.val < 2 ∧ row.sel_high_b.val < 2

/-- MemAlignReadByte Spec: the `composed_value` byte-recombination
    relation and the `byte_value` `bits(8)` range bound. The
    `composed_value` clause restates `mem_align_byte.pil:57`; the
    `byte_value` bound restates the `bits(8)` declaration at
    `mem_align_byte.pil:30` and is discharged inside the Component's
    `soundness` from `range_bus_sound`. -/
def Spec (row : MemAlignReadByteRow FGL) : Prop :=
  row.composed_value
    = row.byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
    + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
    + row.value_16b * value_16b_factor row.sel_high_2b
  -- `bits(8)` range bound (from `range_bus_sound`, discharged inside
  -- the Component's `soundness`):
  ∧ row.byte_value.val < 2 ^ 8

end ZiskFv.AirsClean.MemAlignReadByte
