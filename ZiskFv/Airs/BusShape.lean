import Mathlib

import ZiskFv.Field.Goldilocks

import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus

/-!
# BusShape — named-form shape lemmas for `OperationBusEntry`s

`ZiskFv.Airs.OperationBus.opBus_row_Main` is the hand-written
named-column projection that downstream proofs (`Circuit.Add`, etc.)
consume. It exposes the operation-bus 8-tuple through `Valid_Main`'s
named accessors.

This file proves the *named-form* shape of `opBus_row_Main m row`
under various mode hypotheses:
* `bus_emission_main_slots_match_opBus_row_Main` is the tautological
  unfolding — each field equals the corresponding named accessor;
* `bus_shape_for_main_at_m32_zero` / `bus_shape_for_main_at_m32_one`
  specialise to a row pinning `is_external_op = 1` and a chosen
  `m32` value, collapsing the `(1 - m32) * a_hi/b_hi` factors;
* `bus_shape_for_ADD` and the per-opcode aliases pin the opcode
  literal as well, yielding the fully resolved bus-tuple shape
  needed by the operation-bus matcher in `Circuit.Add`.

The previous formulation here equated each tuple slot of the
auto-extracted `Extraction.Buses.bus_emission_Main_0` spec to the
named projection's corresponding field. After Phase F (typeclass
retirement), that bridge migrates to the permutation-soundness axiom;
the load-bearing artifact is the named-form shape proved below. -/

namespace ZiskFv.Airs.BusShape

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus

variable {F ExtF : Type} [Field F] [Field ExtF]

/-- The Main AIR's operation-bus emission, expressed in named-accessor
    form: every field of `opBus_row_Main m row` equals the corresponding
    named-column accessor evaluated at `row`. After Phase F (typeclass
    retirement), the bridge to the extracted spec lives in the
    permutation-soundness axiom; the slot-match content here is the
    *named-form* shape of the bus entry, which is what downstream proofs
    actually consume.

    Proof is a tautological unfolding of `opBus_row_Main`. -/
lemma bus_emission_main_slots_match_opBus_row_Main
    (m : Valid_Main F ExtF) (row : ℕ) :
    let entry := opBus_row_Main m row
    entry.multiplicity = m.is_external_op row ∧
    entry.op = m.op row ∧
    entry.a_lo = m.a_0 row ∧
    entry.a_hi = (1 - m.m32 row) * m.a_1 row ∧
    entry.b_lo = m.b_0 row ∧
    entry.b_hi = (1 - m.m32 row) * m.b_1 row ∧
    entry.c_lo = m.c_0 row ∧
    entry.c_hi = m.c_1 row ∧
    entry.flag = m.flag row := by
  simp [opBus_row_Main]

/-- **Bus-shape derivation for ADD.** Given a row of `Valid_Main`
    constrained to be in ADD mode (`op = OP_ADD`, `is_external_op = 1`,
    `m32 = 0` — see `Circuit.Add.main_row_in_add_mode`), the operation-bus
    tuple emitted by Main on that row reduces to the fully-resolved
    named-form shape: every field of `opBus_row_Main m row` collapses
    to the corresponding row-resolved value.

    Composed with `Circuit.Add.main_row_in_add_mode`'s field equalities, this
    yields `opBus_row_Main`'s ADD-mode shape — the form a downstream
    caller can rewrite the bus-matcher predicate against. -/
lemma bus_shape_for_ADD
    (m : Valid_Main F ExtF) (row : ℕ)
    (h_op : m.op row = 10)
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    let entry := opBus_row_Main m row
    entry.multiplicity = 1
    ∧ entry.op = 10
    ∧ entry.a_lo = m.a_0 row
    ∧ entry.a_hi = m.a_1 row
    ∧ entry.b_lo = m.b_0 row
    ∧ entry.b_hi = m.b_1 row
    ∧ entry.c_lo = m.c_0 row
    ∧ entry.c_hi = m.c_1 row
    ∧ entry.flag = m.flag row := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [opBus_row_Main, h_op, h_ext, h_m32]

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
    `op = op_lit` mode with `is_external_op = 1, m32 = 0`. The `a_hi`/`b_hi`
    fields collapse to `a_1`/`b_1` via `(1 - 0) * x = x`; `op` collapses to
    the opcode literal. Other fields are definitionally the corresponding
    named-column accessor. -/
lemma bus_shape_for_main_at_m32_zero
    (m : Valid_Main F ExtF) (row : ℕ) (op_lit : F)
    (h_op : m.op row = op_lit)
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 0) :
    let entry := opBus_row_Main m row
    entry.multiplicity = 1
    ∧ entry.op = op_lit
    ∧ entry.a_lo = m.a_0 row
    ∧ entry.a_hi = m.a_1 row
    ∧ entry.b_lo = m.b_0 row
    ∧ entry.b_hi = m.b_1 row
    ∧ entry.c_lo = m.c_0 row
    ∧ entry.c_hi = m.c_1 row
    ∧ entry.flag = m.flag row := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [opBus_row_Main, h_op, h_ext, h_m32]

/-- **Parametric bus-shape, `m32 = 1` (32-bit word) variant.** Mirrors
    `bus_shape_for_main_at_m32_zero` for the 32-bit ADDW/SUBW/SLLW/...
    archetype. The `a_hi`/`b_hi` fields collapse to `0` via `(1 - 1) * x = 0`,
    mirroring PIL's zero-out of the high lanes for word opcodes. -/
lemma bus_shape_for_main_at_m32_one
    (m : Valid_Main F ExtF) (row : ℕ) (op_lit : F)
    (h_op : m.op row = op_lit)
    (h_ext : m.is_external_op row = 1)
    (h_m32 : m.m32 row = 1) :
    let entry := opBus_row_Main m row
    entry.multiplicity = 1
    ∧ entry.op = op_lit
    ∧ entry.a_lo = m.a_0 row
    ∧ entry.a_hi = 0
    ∧ entry.b_lo = m.b_0 row
    ∧ entry.b_hi = 0
    ∧ entry.c_lo = m.c_0 row
    ∧ entry.c_hi = m.c_1 row
    ∧ entry.flag = m.flag row := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [opBus_row_Main, h_op, h_ext, h_m32]

/-- The conclusion of every per-opcode `bus_shape_for_<OP>` lemma at
    `m32 = 0`: a 9-tuple of equalities pinning each field of
    `opBus_row_Main m row` to its row-resolved named-column value. Factored
    out so the per-opcode aliases can share one return type. -/
@[simp]
def bus_shape_main_at_m32_zero_conclusion
    (m : Valid_Main F ExtF) (row : ℕ) (op_lit : F) : Prop :=
  let entry := opBus_row_Main m row
  entry.multiplicity = 1
  ∧ entry.op = op_lit
  ∧ entry.a_lo = m.a_0 row
  ∧ entry.a_hi = m.a_1 row
  ∧ entry.b_lo = m.b_0 row
  ∧ entry.b_hi = m.b_1 row
  ∧ entry.c_lo = m.c_0 row
  ∧ entry.c_hi = m.c_1 row
  ∧ entry.flag = m.flag row

/-- 32-bit-word variant conclusion (m32 = 1): high lanes (`a_hi`/`b_hi`)
    zero out on the bus. -/
@[simp]
def bus_shape_main_at_m32_one_conclusion
    (m : Valid_Main F ExtF) (row : ℕ) (op_lit : F) : Prop :=
  let entry := opBus_row_Main m row
  entry.multiplicity = 1
  ∧ entry.op = op_lit
  ∧ entry.a_lo = m.a_0 row
  ∧ entry.a_hi = (0 : F)
  ∧ entry.b_lo = m.b_0 row
  ∧ entry.b_hi = (0 : F)
  ∧ entry.c_lo = m.c_0 row
  ∧ entry.c_hi = m.c_1 row
  ∧ entry.flag = m.flag row

/-! ## Per-opcode specialisations

Each lemma below takes the same three mode hypotheses as
`bus_shape_for_ADD` (op-literal equality, `is_external_op = 1`, the
opcode's `m32` value) and yields the fully-resolved bus-tuple shape.
Names follow the `OP_*` constants in `ZiskFv.RowShape.Contract`.

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

variable (m : Valid_Main F ExtF) (row : ℕ)

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

/-- Legacy internal-copyb jump archetype, opcode 1 (OP_COPYB), m32 = 0. -/
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
