import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Extraction.Buses
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus

/-!
# BusShape — derivation lemmas linking extracted bus specs to hand-written `OperationBusEntry`s

`ZiskFv.Extraction.Buses` is auto-generated from the pilout's
`gsum_debug_data` hints (Track O POC). It mirrors the PIL2 macros'
runtime view of bus emissions: a `BusEmissionSpec` carries the bus id,
the multiplicity expression, and a tuple of named slots whose values are
`C F ExtF → ℕ → F` thunks rendered straight from the pilout.

`ZiskFv.Airs.OperationBus.opBus_row_Main` is the hand-written named-column
version that downstream proofs (`Spec.Add`, etc.) consume. It exposes the
same eight tuple slots through `Valid_Main`'s named accessors.

This file proves the two are pointwise equal. Concretely:
* `bus_emission_main_slots_match_opBus_row_Main` shows that for every row,
  applying each extracted slot's `value` thunk to `m.circuit` produces
  the same field element as the corresponding `opBus_row_Main` field;
* `bus_shape_for_ADD` specialises the slot-equalities to a row where
  `op = OP_ADD ∧ is_external_op = 1 ∧ m32 = 0`, deriving a fully
  resolved 8-tuple shape (the form needed by the operation-bus matcher
  in `Spec.Add`).

`#print axioms bus_shape_for_ADD` after this file builds confirms the
lemma uses no axioms beyond Mathlib's. The extracted spec adds no axioms
itself — it's a pure `def`.
-/

namespace ZiskFv.Airs.BusShape

open Goldilocks
open ZiskFv.Extraction.Buses
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- Helper: extracted slot lookup by zero-based index, projecting just
    the `value` thunk. Returns `0` past the end (which never happens for
    well-formed specs — the operation-bus tuple has exactly 8 slots). -/
def slotValue (spec : @BusEmissionSpec C F ExtF _ _ _) (i : ℕ)
    : C F ExtF → ℕ → F :=
  match spec.slots[i]? with
  | some s => s.value
  | none => fun _ _ => 0

/-- The Main AIR's operation-bus emission (extracted from
    `gsum_debug_data` hint #46) is *pointwise equal* to `opBus_row_Main`
    on the same row, slot by slot. The hint only carries 8 slots
    (`op, a_lo, a_hi, b_lo, b_hi, c_lo, c_hi, flag`); the four trailing
    `OperationBusEntry` fields (`main_step`, `extended_arg`,
    `extra_args_0`, plus the `multiplicity` accumulator) are
    handled separately because they're injected by the PIL2 lookup
    macro at compile time as zeros / the gating selector and don't
    appear as tuple slots in the hint. We prove all eight slot
    equalities and the multiplicity equality here. -/
theorem bus_emission_main_slots_match_opBus_row_Main
    (m : Valid_Main C F ExtF) (row : ℕ) :
    let spec := @bus_emission_Main_0 C F ExtF _ _ _
    let entry := opBus_row_Main m row
    spec.multiplicity m.circuit row = entry.multiplicity ∧
    slotValue spec 0 m.circuit row = entry.op ∧
    slotValue spec 1 m.circuit row = entry.a_lo ∧
    slotValue spec 2 m.circuit row = entry.a_hi ∧
    slotValue spec 3 m.circuit row = entry.b_lo ∧
    slotValue spec 4 m.circuit row = entry.b_hi ∧
    slotValue spec 5 m.circuit row = entry.c_lo ∧
    slotValue spec 6 m.circuit row = entry.c_hi ∧
    slotValue spec 7 m.circuit row = entry.flag := by
  -- Each slot's value thunk was rendered by the same `Circuit.main`
  -- accessor pattern as the named-column `_def` lemmas in `Valid_Main`.
  -- After unfolding, the goals reduce to either `(x + 0) = x`
  -- (constant trailing zero from PIL's `Add` representation of unary
  -- expressions) or the literal `(1 - m32 row) * a_1 row` form, all of
  -- which `simp` plus the named-column `_def` rewrites close.
  -- The extracted spec emits each tuple slot as `Circuit.main c id col
  -- row 0` (raw column access), while `opBus_row_Main` uses the named
  -- accessors `m.is_external_op row` etc. The `_def` lemmas in
  -- `Valid_Main` give one direction (`m.X row = Circuit.main ...`).
  -- Unfold the spec/entry first, then push the named accessors *into*
  -- the `Circuit.main` form on the RHS (using `← _def`) so both sides
  -- are syntactically identical Circuit.main lookups, closed by `ring`
  -- (which also handles `... + 0 = ...` from the extractor's `Add(x, 0)`
  -- representation of unary expressions).
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [bus_emission_Main_0, slotValue, opBus_row_Main,
                 List.getElem?_cons_zero, List.getElem?_cons_succ]
      try simp only [m.is_external_op_def, m.op_def, m.a_0_def, m.a_1_def,
                     m.b_0_def, m.b_1_def, m.c_0_def, m.c_1_def, m.flag_def,
                     m.m32_def]
      try ring

/-- **Bus-shape derivation for ADD** — the POC payoff. Given a row of
    `Valid_Main` constrained to be in ADD mode (`op = OP_ADD`,
    `is_external_op = 1`, `m32 = 0` — all three are constraint
    consequences for the ADD opcode, see `Spec.Add.main_row_in_add_mode`),
    the operation-bus tuple emitted by Main on that row reduces to the
    fully-resolved shape:
    `[10, a_lo, a_hi, b_lo, b_hi, c_lo, c_hi, flag]` with multiplicity 1.

    This packages the extracted spec's pointwise slot equalities into a
    form a downstream caller can rewrite the bus-matcher predicate
    against. Composed with `Spec.Add.main_row_in_add_mode`'s field
    equalities, it yields exactly `opBus_row_Main`'s ADD-mode shape. -/
theorem bus_shape_for_ADD
    (m : Valid_Main C F ExtF) (row : ℕ)
    (h_op : m.op row = 10)
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    let spec := @bus_emission_Main_0 C F ExtF _ _ _
    let entry := opBus_row_Main m row
    spec.multiplicity m.circuit row = 1
    ∧ slotValue spec 0 m.circuit row = 10
    ∧ slotValue spec 1 m.circuit row = entry.a_lo
    ∧ slotValue spec 2 m.circuit row = m.a_1 row
    ∧ slotValue spec 3 m.circuit row = entry.b_lo
    ∧ slotValue spec 4 m.circuit row = m.b_1 row
    ∧ slotValue spec 5 m.circuit row = entry.c_lo
    ∧ slotValue spec 6 m.circuit row = entry.c_hi
    ∧ slotValue spec 7 m.circuit row = entry.flag := by
  obtain ⟨h_mul, h_op_eq, h_a_lo, h_a_hi, h_b_lo, h_b_hi,
           h_c_lo, h_c_hi, h_flag⟩ :=
    bus_emission_main_slots_match_opBus_row_Main m row
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- multiplicity = is_external_op = 1
    rw [h_mul]; simp [opBus_row_Main, h_ext]
  · -- slot 0 = op = OP_ADD = 10
    rw [h_op_eq]; simp [opBus_row_Main, h_op]
  · -- slot 1 = a_lo (definitional)
    exact h_a_lo
  · -- slot 2 = a_hi = (1 - m32) * a_1 = a_1 when m32 = 0
    rw [h_a_hi]; simp [opBus_row_Main, h_m32]
  · exact h_b_lo
  · -- slot 4 = b_hi = (1 - m32) * b_1 = b_1 when m32 = 0
    rw [h_b_hi]; simp [opBus_row_Main, h_m32]
  · exact h_c_lo
  · exact h_c_hi
  · exact h_flag

-- Dependency / axiom audit. The output messages confirm both lemmas
-- depend only on the standard built-in axioms `propext`,
-- `Classical.choice`, `Quot.sound` (Mathlib base) — no ZisK trust-base
-- axioms. The extracted `bus_emission_Main_0` is a pure `def`, and
-- `bus_shape_for_ADD` is closed by `ring` over field laws and the
-- named-column `_def` equalities (also `def`-defined by the
-- `Valid_Main` structure).
#print axioms bus_shape_for_ADD
#print axioms bus_emission_main_slots_match_opBus_row_Main

end ZiskFv.Airs.BusShape
