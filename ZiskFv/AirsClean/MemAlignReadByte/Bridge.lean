import ZiskFv.AirsClean.MemAlignReadByte.Circuit
import ZiskFv.Airs.MemAlignReadByte

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

No axioms. The Component-routed bridge gets its byte range fact from a
lookup-aware witness for the Clean `lookup rangeTable8` operation.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks
open ZiskFv.Channels.MemoryBus

/-- Constant-expression view of a `MemAlignReadByteRow`, used when
    specializing lookup-aware Clean soundness to one concrete row. -/
@[reducible]
def constVar (row : MemAlignReadByteRow FGL) : Var MemAlignReadByteRow FGL where
  sel_high_4b := .const row.sel_high_4b
  sel_high_2b := .const row.sel_high_2b
  sel_high_b := .const row.sel_high_b
  direct_value := .const row.direct_value
  composed_value := .const row.composed_value
  value_16b := .const row.value_16b
  value_8b := .const row.value_8b
  byte_value := .const row.byte_value
  addr_w := .const row.addr_w
  step := .const row.step

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

@[reducible]
def validOfRow (row : MemAlignReadByteRow FGL) :
    ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL where
  sel_high_4b := fun _ => row.sel_high_4b
  sel_high_2b := fun _ => row.sel_high_2b
  sel_high_b := fun _ => row.sel_high_b
  direct_value := fun _ => row.direct_value
  composed_value := fun _ => row.composed_value
  value_16b := fun _ => row.value_16b
  value_8b := fun _ => row.value_8b
  byte_value := fun _ => row.byte_value
  addr_w := fun _ => row.addr_w
  step := fun _ => row.step

/-- Concrete MemAlignReadByte memory-bus message:
`[1, addr_w * 8 + byte_offset, step, 1, byte_value, 0]`.

This is the PIL-shaped message emitted by `memBusMessageExpr`. -/
@[reducible]
def memBusMessage (row : MemAlignReadByteRow FGL) : MemBusMessage FGL :=
  { mem_op := 1
    ptr := row.addr_w * 8
      + (row.sel_high_4b * 4 + row.sel_high_2b * 2 + row.sel_high_b)
    timestamp := row.step
    width := 1
    value_0 := row.byte_value
    value_1 := 0 }

theorem eval_memBusMessageExpr
    (env : Environment FGL) (row : Var MemAlignReadByteRow FGL) :
    eval env (memBusMessageExpr row) = memBusMessage (eval env row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [memBusMessageExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor

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

/-- Lookup-aware Clean witness for the byte-value range lookup in a
    selected MemAlignReadByte row. This exposes the real
    `lookup (rangeTable8) byte_value` operation from `main`; it is
    structural evidence, not a replacement range axiom. -/
structure RangeLookupWitness
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ) where
  offset : ℕ
  env : Environment FGL
  holds :
    ConstraintsHold.Soundness env
      ((main (constVar (rowAt v r))).operations offset)

/-- Project the byte-value range fact supplied by the Clean lookup
    operation in `MemAlignReadByte.main`. -/
theorem byte_value_range_of_lookup_aware_const_soundness
    {v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL} {r : ℕ}
    (w : RangeLookupWitness v r) :
    (v.byte_value r).val < 2 ^ 8 := by
  have h_holds := w.holds
  simp only [main, circuit_norm] at h_holds
  rcases h_holds with ⟨h_byte_range, _h0, _h1, _h2, _h_composed⟩
  simpa [rowAt, constVar] using h_byte_range

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
that conjunct is supplied from the Clean `lookup rangeTable8` operation
exposed by `RangeLookupWitness`. Routing through
`MemAlignReadByte.spec_via_component` makes the Clean Component genuinely
load-bearing for the load opcodes without adding a completeness declaration.
-/

/-- **C2 re-root entry point.** From the MemAlignReadByte AIR's
    `core_every_row` PIL constraints plus lookup-aware Clean range
    evidence at row `r`, derive `byte_value`'s `< 256` range bound
    **through the Clean Component** (its proven `Spec`, via
    `spec_via_component`). This is what the LBU / LHU / LWU narrow
    loads consume — making `memAlignReadByteComponent` load-bearing
    for those opcodes. -/
theorem byte_value_in_range_via_component
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ)
    (h_core : ZiskFv.Airs.MemAlignReadByte.core_every_row v r)
    (h_lookup : RangeLookupWitness v r) :
    (v.byte_value r).val < 2 ^ 8 := by
  obtain ⟨h_b0, h_b1, h_b2, h_composed⟩ := h_core
  have h_byte_value_range :=
    byte_value_range_of_lookup_aware_const_soundness h_lookup
  -- `rowAt v r` projects the AIR row into the Clean Component row;
  -- each `rowAt` field is `@[reducible]`-defeq to `v.<col> r`.
  have h_spec : Spec (rowAt v r) :=
    spec_via_component (rowAt v r) h_composed h_b0 h_b1 h_b2
      h_byte_value_range
  exact h_spec.2

end ZiskFv.AirsClean.MemAlignReadByte
