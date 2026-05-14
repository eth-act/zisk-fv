import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Field.Goldilocks
import Extraction.Buses

import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus

/-!
# BusShape — derivation lemmas linking extracted bus specs to hand-written `OperationBusEntry`s

`Extraction.Buses` is auto-generated from the pilout's
`gsum_debug_data` hints. It mirrors the PIL2 macros' runtime view of
bus emissions: a `BusEmissionSpec` carries the bus id, the multiplicity
expression, and a tuple of named slots whose values are
`C F ExtF → ℕ → F` thunks rendered straight from the pilout.

`ZiskFv.Airs.OperationBus.opBus_row_Main` is the hand-written
named-column version that downstream proofs (`Circuit.Add`, etc.) consume.
It exposes the same eight tuple slots through `Valid_Main`'s named
accessors.

This file proves the two are pointwise equal:
* `bus_emission_main_slots_match_opBus_row_Main` shows that for every row,
  applying each extracted slot's `value` thunk to `m.circuit` produces
  the same field element as the corresponding `opBus_row_Main` field;
* `bus_shape_for_ADD` specialises the slot-equalities to a row where
  `op = OP_ADD ∧ is_external_op = 1 ∧ m32 = 0`, deriving the fully
  resolved 8-tuple shape needed by the operation-bus matcher in
  `Circuit.Add`.
-/

namespace ZiskFv.Airs.BusShape

open Goldilocks
open Extraction.Buses
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
lemma bus_emission_main_slots_match_opBus_row_Main
    (m : Valid_Main C F ExtF) (row : ℕ) :
    let spec := @Extraction.Buses.bus_emission_Main_0 C F ExtF _ _ _
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
    · simp only [Extraction.Buses.bus_emission_Main_0, slotValue, opBus_row_Main,
                 List.getElem?_cons_zero, List.getElem?_cons_succ]
      try simp only [m.is_external_op_def, m.op_def, m.a_0_def, m.a_1_def,
                     m.b_0_def, m.b_1_def, m.c_0_def, m.c_1_def, m.flag_def,
                     m.m32_def]
      try ring

/-- **Bus-shape derivation for ADD.** Given a row of `Valid_Main`
    constrained to be in ADD mode (`op = OP_ADD`, `is_external_op = 1`,
    `m32 = 0` — see `Circuit.Add.main_row_in_add_mode`), the operation-bus
    tuple emitted by Main on that row reduces to the fully-resolved shape
    `[10, a_lo, a_hi, b_lo, b_hi, c_lo, c_hi, flag]` with multiplicity 1.

    Composed with `Circuit.Add.main_row_in_add_mode`'s field equalities, this
    yields `opBus_row_Main`'s ADD-mode shape — the form a downstream
    caller can rewrite the bus-matcher predicate against. -/
lemma bus_shape_for_ADD
    (m : Valid_Main C F ExtF) (row : ℕ)
    (h_op : m.op row = 10)
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    let spec := @Extraction.Buses.bus_emission_Main_0 C F ExtF _ _ _
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

/-! ## Per-archetype parametric bus-shape lemmas

The body of `bus_shape_for_ADD` makes no use of the ADD-specific opcode
literal beyond rewriting `m.op row = op_lit`. We extract two parametric
lemmas — one for `m32 = 0` (full 64-bit operands) and one for `m32 = 1`
(32-bit word variants where the high lanes zero out on the bus). Every
RV64IM opcode that emits via the operation bus falls into one of these
two shapes; the per-opcode `bus_shape_for_<OP>` lemmas below are thin
specialisations.
-/

/-- **Parametric bus-shape, `m32 = 0` (64-bit) variant.** Specialises
    `bus_emission_main_slots_match_opBus_row_Main` to a row in
    `op = op_lit` mode with `is_external_op = 1, m32 = 0`. Slots 2/4
    collapse to `a_1`/`b_1` via `(1 - 0) * x = x`; slot 0 collapses to
    the opcode literal. Slots 1/3/5/6/7 are definitionally the
    corresponding `opBus_row_Main` field. -/
lemma bus_shape_for_main_at_m32_zero
    (m : Valid_Main C F ExtF) (row : ℕ) (op_lit : F)
    (h_op : m.op row = op_lit)
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    let spec := @Extraction.Buses.bus_emission_Main_0 C F ExtF _ _ _
    let entry := opBus_row_Main m row
    spec.multiplicity m.circuit row = 1
    ∧ slotValue spec 0 m.circuit row = op_lit
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
  · rw [h_mul]; simp [opBus_row_Main, h_ext]
  · rw [h_op_eq]; simp [opBus_row_Main, h_op]
  · exact h_a_lo
  · rw [h_a_hi]; simp [opBus_row_Main, h_m32]
  · exact h_b_lo
  · rw [h_b_hi]; simp [opBus_row_Main, h_m32]
  · exact h_c_lo
  · exact h_c_hi
  · exact h_flag

/-- **Parametric bus-shape, `m32 = 1` (32-bit word) variant.** Mirrors
    `bus_shape_for_main_at_m32_zero` for the 32-bit ADDW/SUBW/SLLW/...
    archetype. Slots 2/4 collapse to `0` via `(1 - 1) * x = 0`, mirroring
    PIL's zero-out of the high lanes for word opcodes. -/
lemma bus_shape_for_main_at_m32_one
    (m : Valid_Main C F ExtF) (row : ℕ) (op_lit : F)
    (h_op : m.op row = op_lit)
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    let spec := @Extraction.Buses.bus_emission_Main_0 C F ExtF _ _ _
    let entry := opBus_row_Main m row
    spec.multiplicity m.circuit row = 1
    ∧ slotValue spec 0 m.circuit row = op_lit
    ∧ slotValue spec 1 m.circuit row = entry.a_lo
    ∧ slotValue spec 2 m.circuit row = 0
    ∧ slotValue spec 3 m.circuit row = entry.b_lo
    ∧ slotValue spec 4 m.circuit row = 0
    ∧ slotValue spec 5 m.circuit row = entry.c_lo
    ∧ slotValue spec 6 m.circuit row = entry.c_hi
    ∧ slotValue spec 7 m.circuit row = entry.flag := by
  obtain ⟨h_mul, h_op_eq, h_a_lo, h_a_hi, h_b_lo, h_b_hi,
           h_c_lo, h_c_hi, h_flag⟩ :=
    bus_emission_main_slots_match_opBus_row_Main m row
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_mul]; simp [opBus_row_Main, h_ext]
  · rw [h_op_eq]; simp [opBus_row_Main, h_op]
  · exact h_a_lo
  · rw [h_a_hi]; simp [opBus_row_Main, h_m32]
  · exact h_b_lo
  · rw [h_b_hi]; simp [opBus_row_Main, h_m32]
  · exact h_c_lo
  · exact h_c_hi
  · exact h_flag

/-- The conclusion of every per-opcode `bus_shape_for_<OP>` lemma at
    `m32 = 0`: a 9-tuple of equalities tying the extracted bus-emission
    spec's slots to the `opBus_row_Main` projection. Factored out so the
    per-opcode aliases can share one return type. -/
@[simp]
def bus_shape_main_at_m32_zero_conclusion
    (m : Valid_Main C F ExtF) (row : ℕ) (op_lit : F) : Prop :=
  let spec := @Extraction.Buses.bus_emission_Main_0 C F ExtF _ _ _
  let entry := opBus_row_Main m row
  spec.multiplicity m.circuit row = 1
  ∧ slotValue spec 0 m.circuit row = op_lit
  ∧ slotValue spec 1 m.circuit row = entry.a_lo
  ∧ slotValue spec 2 m.circuit row = m.a_1 row
  ∧ slotValue spec 3 m.circuit row = entry.b_lo
  ∧ slotValue spec 4 m.circuit row = m.b_1 row
  ∧ slotValue spec 5 m.circuit row = entry.c_lo
  ∧ slotValue spec 6 m.circuit row = entry.c_hi
  ∧ slotValue spec 7 m.circuit row = entry.flag

/-- 32-bit-word variant conclusion (m32 = 1): high lanes (slots 2/4)
    zero out on the bus. -/
@[simp]
def bus_shape_main_at_m32_one_conclusion
    (m : Valid_Main C F ExtF) (row : ℕ) (op_lit : F) : Prop :=
  let spec := @Extraction.Buses.bus_emission_Main_0 C F ExtF _ _ _
  let entry := opBus_row_Main m row
  spec.multiplicity m.circuit row = 1
  ∧ slotValue spec 0 m.circuit row = op_lit
  ∧ slotValue spec 1 m.circuit row = entry.a_lo
  ∧ slotValue spec 2 m.circuit row = (0 : F)
  ∧ slotValue spec 3 m.circuit row = entry.b_lo
  ∧ slotValue spec 4 m.circuit row = (0 : F)
  ∧ slotValue spec 5 m.circuit row = entry.c_lo
  ∧ slotValue spec 6 m.circuit row = entry.c_hi
  ∧ slotValue spec 7 m.circuit row = entry.flag

/-! ## Per-opcode specialisations

Each lemma below takes the same three mode hypotheses as
`bus_shape_for_ADD` (op-literal equality, `is_external_op = 1`, the
opcode's `m32` value) and yields the fully-resolved bus-tuple shape.
Names follow the `OP_*` constants in `Fundamentals.Transpiler`.

The three groups correspond to the two parametric shapes above:
* **64-bit ALU / branch / load / store / jump / mul / div** — `m32 = 0`,
  the dominant case. Eligibility is "Main emits the operation-bus tuple
  with high-lane factor `(1 - 0) = 1`".
* **32-bit word variants** (`*W` opcodes) — `m32 = 1`, high lanes zero
  out on the bus.

Per-opcode aliases drop the `op_lit` parameter by pinning it to the
matching `OP_*` constant.
-/

section PerOpcode

variable (m : Valid_Main C F ExtF) (row : ℕ)

/-- ADD (RV32IM) — opcode literal 10, m32 = 0. -/
lemma bus_shape_for_ADD'
    (h_op : m.op row = (10 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 10 := by
  exact bus_shape_for_main_at_m32_zero m row 10 h_op h_ext h_m32

/-- SUB — opcode literal 11, m32 = 0. -/
lemma bus_shape_for_SUB
    (h_op : m.op row = (11 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 11 := by
  exact bus_shape_for_main_at_m32_zero m row 11 h_op h_ext h_m32

/-- AND — opcode literal 14, m32 = 0. -/
lemma bus_shape_for_AND
    (h_op : m.op row = (14 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 14 := by
  exact bus_shape_for_main_at_m32_zero m row 14 h_op h_ext h_m32

/-- OR — opcode literal 15, m32 = 0. -/
lemma bus_shape_for_OR
    (h_op : m.op row = (15 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 15 := by
  exact bus_shape_for_main_at_m32_zero m row 15 h_op h_ext h_m32

/-- XOR — opcode literal 16, m32 = 0. -/
lemma bus_shape_for_XOR
    (h_op : m.op row = (16 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 16 := by
  exact bus_shape_for_main_at_m32_zero m row 16 h_op h_ext h_m32

/-- SLT (signed less-than) — opcode literal 7 (OP_LT), m32 = 0. -/
lemma bus_shape_for_SLT
    (h_op : m.op row = (7 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 7 := by
  exact bus_shape_for_main_at_m32_zero m row 7 h_op h_ext h_m32

/-- SLTU (unsigned less-than) — opcode literal 6 (OP_LTU), m32 = 0. -/
lemma bus_shape_for_SLTU
    (h_op : m.op row = (6 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 6 := by
  exact bus_shape_for_main_at_m32_zero m row 6 h_op h_ext h_m32

/-- ADDI — same as ADD; the I-type immediate is folded into `b` by the
    transpiler before the row reaches Main. -/
lemma bus_shape_for_ADDI
    (h_op : m.op row = (10 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 10 := by
  exact bus_shape_for_main_at_m32_zero m row 10 h_op h_ext h_m32

/-- ANDI — opcode 14, m32 = 0. -/
lemma bus_shape_for_ANDI
    (h_op : m.op row = (14 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 14 := by
  exact bus_shape_for_main_at_m32_zero m row 14 h_op h_ext h_m32

/-- ORI — opcode 15, m32 = 0. -/
lemma bus_shape_for_ORI
    (h_op : m.op row = (15 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 15 := by
  exact bus_shape_for_main_at_m32_zero m row 15 h_op h_ext h_m32

/-- XORI — opcode 16, m32 = 0. -/
lemma bus_shape_for_XORI
    (h_op : m.op row = (16 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 16 := by
  exact bus_shape_for_main_at_m32_zero m row 16 h_op h_ext h_m32

/-- SLTI — opcode 7, m32 = 0. -/
lemma bus_shape_for_SLTI
    (h_op : m.op row = (7 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 7 := by
  exact bus_shape_for_main_at_m32_zero m row 7 h_op h_ext h_m32

/-- SLTIU — opcode 6, m32 = 0. -/
lemma bus_shape_for_SLTIU
    (h_op : m.op row = (6 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 6 := by
  exact bus_shape_for_main_at_m32_zero m row 6 h_op h_ext h_m32

/-- BEQ (branch equal) — opcode 9 (OP_EQ), m32 = 0. -/
lemma bus_shape_for_BEQ
    (h_op : m.op row = (9 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 9 := by
  exact bus_shape_for_main_at_m32_zero m row 9 h_op h_ext h_m32

/-- BNE (branch not equal) — opcode 9 (OP_EQ; ZisK encodes via `flag`
    inversion in the per-opcode mode predicate). -/
lemma bus_shape_for_BNE
    (h_op : m.op row = (9 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 9 := by
  exact bus_shape_for_main_at_m32_zero m row 9 h_op h_ext h_m32

/-- BLT (branch less-than signed) — opcode 7. -/
lemma bus_shape_for_BLT
    (h_op : m.op row = (7 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 7 := by
  exact bus_shape_for_main_at_m32_zero m row 7 h_op h_ext h_m32

/-- BLTU (branch less-than unsigned) — opcode 6. -/
lemma bus_shape_for_BLTU
    (h_op : m.op row = (6 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 6 := by
  exact bus_shape_for_main_at_m32_zero m row 6 h_op h_ext h_m32

/-- BGE — opcode 7 (OP_LT, ZisK negates via flag). -/
lemma bus_shape_for_BGE
    (h_op : m.op row = (7 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 7 := by
  exact bus_shape_for_main_at_m32_zero m row 7 h_op h_ext h_m32

/-- BGEU — opcode 6 (OP_LTU, ZisK negates via flag). -/
lemma bus_shape_for_BGEU
    (h_op : m.op row = (6 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 6 := by
  exact bus_shape_for_main_at_m32_zero m row 6 h_op h_ext h_m32

/-- MUL — opcode 180 (OP_MUL), m32 = 0. -/
lemma bus_shape_for_MUL
    (h_op : m.op row = (180 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 180 := by
  exact bus_shape_for_main_at_m32_zero m row 180 h_op h_ext h_m32

/-- MULH — opcode 181 (OP_MULH), m32 = 0. -/
lemma bus_shape_for_MULH
    (h_op : m.op row = (181 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 181 := by
  exact bus_shape_for_main_at_m32_zero m row 181 h_op h_ext h_m32

/-- MULHU — opcode 177 (OP_MULUH), m32 = 0. -/
lemma bus_shape_for_MULHU
    (h_op : m.op row = (177 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 177 := by
  exact bus_shape_for_main_at_m32_zero m row 177 h_op h_ext h_m32

/-- MULHSU — opcode 179 (OP_MULSUH), m32 = 0. -/
lemma bus_shape_for_MULHSU
    (h_op : m.op row = (179 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 179 := by
  exact bus_shape_for_main_at_m32_zero m row 179 h_op h_ext h_m32

/-- DIV — opcode 186 (OP_DIV), m32 = 0. -/
lemma bus_shape_for_DIV
    (h_op : m.op row = (186 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 186 := by
  exact bus_shape_for_main_at_m32_zero m row 186 h_op h_ext h_m32

/-- DIVU — opcode 184 (OP_DIVU), m32 = 0. -/
lemma bus_shape_for_DIVU
    (h_op : m.op row = (184 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 184 := by
  exact bus_shape_for_main_at_m32_zero m row 184 h_op h_ext h_m32

/-- REM — opcode 187 (OP_REM), m32 = 0. -/
lemma bus_shape_for_REM
    (h_op : m.op row = (187 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 187 := by
  exact bus_shape_for_main_at_m32_zero m row 187 h_op h_ext h_m32

/-- REMU — opcode 185 (OP_REMU), m32 = 0. -/
lemma bus_shape_for_REMU
    (h_op : m.op row = (185 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 185 := by
  exact bus_shape_for_main_at_m32_zero m row 185 h_op h_ext h_m32

/-- SLL — opcode 33, m32 = 0. -/
lemma bus_shape_for_SLL
    (h_op : m.op row = (33 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 33 := by
  exact bus_shape_for_main_at_m32_zero m row 33 h_op h_ext h_m32

/-- SRL — opcode 34, m32 = 0. -/
lemma bus_shape_for_SRL
    (h_op : m.op row = (34 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 34 := by
  exact bus_shape_for_main_at_m32_zero m row 34 h_op h_ext h_m32

/-- SRA — opcode 35, m32 = 0. -/
lemma bus_shape_for_SRA
    (h_op : m.op row = (35 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 35 := by
  exact bus_shape_for_main_at_m32_zero m row 35 h_op h_ext h_m32

/-- SLLI — opcode 33 (shares SLL's bus shape; immediate folded into `b`). -/
lemma bus_shape_for_SLLI
    (h_op : m.op row = (33 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 33 := by
  exact bus_shape_for_main_at_m32_zero m row 33 h_op h_ext h_m32

/-- SRLI — opcode 34. -/
lemma bus_shape_for_SRLI
    (h_op : m.op row = (34 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 34 := by
  exact bus_shape_for_main_at_m32_zero m row 34 h_op h_ext h_m32

/-- SRAI — opcode 35. -/
lemma bus_shape_for_SRAI
    (h_op : m.op row = (35 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 35 := by
  exact bus_shape_for_main_at_m32_zero m row 35 h_op h_ext h_m32

/-- LD (load doubleword) — opcode 1 (OP_COPYB) per the load archetype. -/
lemma bus_shape_for_LD
    (h_op : m.op row = (1 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 1 := by
  exact bus_shape_for_main_at_m32_zero m row 1 h_op h_ext h_m32

/-- LBU / LHU / LWU — share LD's bus shape (load archetype). -/
lemma bus_shape_for_LBU
    (h_op : m.op row = (1 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 1 := by
  exact bus_shape_for_main_at_m32_zero m row 1 h_op h_ext h_m32

lemma bus_shape_for_LHU
    (h_op : m.op row = (1 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 1 := by
  exact bus_shape_for_main_at_m32_zero m row 1 h_op h_ext h_m32

lemma bus_shape_for_LWU
    (h_op : m.op row = (1 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 1 := by
  exact bus_shape_for_main_at_m32_zero m row 1 h_op h_ext h_m32

/-- LB / LH / LW — sign-extending loads share the byte-extend
    archetype's bus shape (m32 = 0; sign extension is downstream of
    the bus). -/
lemma bus_shape_for_LB
    (h_op : m.op row = (39 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 39 := by
  exact bus_shape_for_main_at_m32_zero m row 39 h_op h_ext h_m32

lemma bus_shape_for_LH
    (h_op : m.op row = (40 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 40 := by
  exact bus_shape_for_main_at_m32_zero m row 40 h_op h_ext h_m32

lemma bus_shape_for_LW
    (h_op : m.op row = (41 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 41 := by
  exact bus_shape_for_main_at_m32_zero m row 41 h_op h_ext h_m32

/-- SD/SB/SH/SW — store archetype, opcode 1 (OP_COPYB), m32 = 0. -/
lemma bus_shape_for_SD
    (h_op : m.op row = (1 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 1 := by
  exact bus_shape_for_main_at_m32_zero m row 1 h_op h_ext h_m32

lemma bus_shape_for_SB
    (h_op : m.op row = (1 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 1 := by
  exact bus_shape_for_main_at_m32_zero m row 1 h_op h_ext h_m32

lemma bus_shape_for_SH
    (h_op : m.op row = (1 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 1 := by
  exact bus_shape_for_main_at_m32_zero m row 1 h_op h_ext h_m32

lemma bus_shape_for_SW
    (h_op : m.op row = (1 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 1 := by
  exact bus_shape_for_main_at_m32_zero m row 1 h_op h_ext h_m32

/-- JAL/JALR — jump archetype, opcode 1 (OP_COPYB), m32 = 0. -/
lemma bus_shape_for_JAL
    (h_op : m.op row = (1 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 1 := by
  exact bus_shape_for_main_at_m32_zero m row 1 h_op h_ext h_m32

lemma bus_shape_for_JALR
    (h_op : m.op row = (1 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 1 := by
  exact bus_shape_for_main_at_m32_zero m row 1 h_op h_ext h_m32

/-- LUI/AUIPC — U-type, opcode 0 (OP_FLAG) per the U-type archetype. -/
lemma bus_shape_for_LUI
    (h_op : m.op row = (0 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 0 := by
  exact bus_shape_for_main_at_m32_zero m row 0 h_op h_ext h_m32

lemma bus_shape_for_AUIPC
    (h_op : m.op row = (0 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 0 := by
  exact bus_shape_for_main_at_m32_zero m row 0 h_op h_ext h_m32

/-- FENCE — same shape as a NOP-equivalent bus emission, opcode 0. -/
lemma bus_shape_for_FENCE
    (h_op : m.op row = (0 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    bus_shape_main_at_m32_zero_conclusion m row 0 := by
  exact bus_shape_for_main_at_m32_zero m row 0 h_op h_ext h_m32

/-! ### 32-bit word variants (m32 = 1) -/

/-- ADDW — opcode 26 (OP_ADD_W), m32 = 1. -/
lemma bus_shape_for_ADDW
    (h_op : m.op row = (26 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 26 := by
  exact bus_shape_for_main_at_m32_one m row 26 h_op h_ext h_m32

/-- SUBW — opcode 27 (OP_SUB_W), m32 = 1. -/
lemma bus_shape_for_SUBW
    (h_op : m.op row = (27 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 27 := by
  exact bus_shape_for_main_at_m32_one m row 27 h_op h_ext h_m32

/-- ADDIW — opcode 26, m32 = 1. -/
lemma bus_shape_for_ADDIW
    (h_op : m.op row = (26 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 26 := by
  exact bus_shape_for_main_at_m32_one m row 26 h_op h_ext h_m32

/-- SLLW — opcode 36 (OP_SLL_W), m32 = 1. -/
lemma bus_shape_for_SLLW
    (h_op : m.op row = (36 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 36 := by
  exact bus_shape_for_main_at_m32_one m row 36 h_op h_ext h_m32

/-- SRLW — opcode 37 (OP_SRL_W), m32 = 1. -/
lemma bus_shape_for_SRLW
    (h_op : m.op row = (37 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 37 := by
  exact bus_shape_for_main_at_m32_one m row 37 h_op h_ext h_m32

/-- SRAW — opcode 38 (OP_SRA_W), m32 = 1. -/
lemma bus_shape_for_SRAW
    (h_op : m.op row = (38 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 38 := by
  exact bus_shape_for_main_at_m32_one m row 38 h_op h_ext h_m32

/-- SLLIW — same shape as SLLW. -/
lemma bus_shape_for_SLLIW
    (h_op : m.op row = (36 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 36 := by
  exact bus_shape_for_main_at_m32_one m row 36 h_op h_ext h_m32

/-- SRLIW. -/
lemma bus_shape_for_SRLIW
    (h_op : m.op row = (37 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 37 := by
  exact bus_shape_for_main_at_m32_one m row 37 h_op h_ext h_m32

/-- SRAIW. -/
lemma bus_shape_for_SRAIW
    (h_op : m.op row = (38 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 38 := by
  exact bus_shape_for_main_at_m32_one m row 38 h_op h_ext h_m32

/-- MULW — opcode 182 (OP_MUL_W), m32 = 1. -/
lemma bus_shape_for_MULW
    (h_op : m.op row = (182 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 182 := by
  exact bus_shape_for_main_at_m32_one m row 182 h_op h_ext h_m32

/-- DIVW — opcode 190. -/
lemma bus_shape_for_DIVW
    (h_op : m.op row = (190 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 190 := by
  exact bus_shape_for_main_at_m32_one m row 190 h_op h_ext h_m32

/-- DIVUW — opcode 188. -/
lemma bus_shape_for_DIVUW
    (h_op : m.op row = (188 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 188 := by
  exact bus_shape_for_main_at_m32_one m row 188 h_op h_ext h_m32

/-- REMW — opcode 191. -/
lemma bus_shape_for_REMW
    (h_op : m.op row = (191 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 191 := by
  exact bus_shape_for_main_at_m32_one m row 191 h_op h_ext h_m32

/-- REMUW — opcode 189. -/
lemma bus_shape_for_REMUW
    (h_op : m.op row = (189 : F))
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    bus_shape_main_at_m32_one_conclusion m row 189 := by
  exact bus_shape_for_main_at_m32_one m row 189 h_op h_ext h_m32

end PerOpcode

-- Axiom audit: confirm these lemmas depend only on Lean/Mathlib base
-- axioms (`propext`, `Classical.choice`, `Quot.sound`) — no ZisK
-- trust-base axioms.
#print axioms bus_shape_for_ADD
#print axioms bus_emission_main_slots_match_opBus_row_Main
#print axioms bus_shape_for_main_at_m32_zero
#print axioms bus_shape_for_main_at_m32_one

end ZiskFv.Airs.BusShape
