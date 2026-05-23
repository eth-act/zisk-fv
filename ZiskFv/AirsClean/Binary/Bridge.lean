import ZiskFv.AirsClean.Binary.Circuit
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Channels.OperationBus

/-!
# `Valid_Binary` ↔ `BinaryRow` compatibility

Post-F1 Bridge: all 20 columns reached via named accessors on
`Valid_Binary FGL FGL`. No `Circuit.main`/`v.circuit` left.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open ZiskFv.Channels.OperationBus

@[reducible]
def rowAt (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r : ℕ) :
    BinaryRow FGL where
  aBytes := {
    free_in_a_0 := v.free_in_a_0 r
    free_in_a_1 := v.free_in_a_1 r
    free_in_a_2 := v.free_in_a_2 r
    free_in_a_3 := v.free_in_a_3 r
    free_in_a_4 := v.free_in_a_4 r
    free_in_a_5 := v.free_in_a_5 r
    free_in_a_6 := v.free_in_a_6 r
    free_in_a_7 := v.free_in_a_7 r
  }
  bBytes := {
    free_in_b_0 := v.free_in_b_0 r
    free_in_b_1 := v.free_in_b_1 r
    free_in_b_2 := v.free_in_b_2 r
    free_in_b_3 := v.free_in_b_3 r
    free_in_b_4 := v.free_in_b_4 r
    free_in_b_5 := v.free_in_b_5 r
    free_in_b_6 := v.free_in_b_6 r
    free_in_b_7 := v.free_in_b_7 r
  }
  cBytes := {
    free_in_c_0 := v.free_in_c_0 r
    free_in_c_1 := v.free_in_c_1 r
    free_in_c_2 := v.free_in_c_2 r
    free_in_c_3 := v.free_in_c_3 r
    free_in_c_4 := v.free_in_c_4 r
    free_in_c_5 := v.free_in_c_5 r
    free_in_c_6 := v.free_in_c_6 r
    free_in_c_7 := v.free_in_c_7 r
  }
  chain := {
    carry_0 := v.carry_0 r
    carry_1 := v.carry_1 r
    carry_2 := v.carry_2 r
    carry_3 := v.carry_3 r
    carry_4 := v.carry_4 r
    carry_5 := v.carry_5 r
    carry_6 := v.carry_6 r
    carry_7 := v.carry_7 r
    b_op := v.b_op r
    b_op_or_sext := v.b_op_or_sext r
  }
  mode := {
    mode32 := v.mode32 r
    result_is_a := v.result_is_a r
    use_first_byte := v.use_first_byte r
    c_is_signed := v.c_is_signed r
    mode32_and_c_is_signed := v.mode32_and_c_is_signed r
  }

/-- The 7 F-typed Binary row constraints at row `r`, expressed against
    a `Valid_Binary` via its named accessors (`v.mode32 r`, etc.). -/
def constraints_at (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r : ℕ) : Prop :=
  v.mode32 r * (1 - v.mode32 r) = 0
  ∧ v.carry_7 r * (1 - v.carry_7 r) = 0
  ∧ v.result_is_a r * (1 - v.result_is_a r) = 0
  ∧ v.use_first_byte r * (1 - v.use_first_byte r) = 0
  ∧ v.c_is_signed r * (1 - v.c_is_signed r) = 0
  ∧ v.b_op_or_sext r
      - (v.mode32 r * (v.c_is_signed r + 512 - v.b_op r) + v.b_op r) = 0
  ∧ v.mode32_and_c_is_signed r - v.mode32 r * v.c_is_signed r = 0

@[reducible]
def aLoValue (row : BinaryRow FGL) : FGL :=
  row.aBytes.free_in_a_0 + 256 * row.aBytes.free_in_a_1
    + 65536 * row.aBytes.free_in_a_2 + 16777216 * row.aBytes.free_in_a_3

@[reducible]
def aHiValue (row : BinaryRow FGL) : FGL :=
  row.aBytes.free_in_a_4 + 256 * row.aBytes.free_in_a_5
    + 65536 * row.aBytes.free_in_a_6 + 16777216 * row.aBytes.free_in_a_7

@[reducible]
def bLoValue (row : BinaryRow FGL) : FGL :=
  row.bBytes.free_in_b_0 + 256 * row.bBytes.free_in_b_1
    + 65536 * row.bBytes.free_in_b_2 + 16777216 * row.bBytes.free_in_b_3

@[reducible]
def bHiValue (row : BinaryRow FGL) : FGL :=
  row.bBytes.free_in_b_4 + 256 * row.bBytes.free_in_b_5
    + 65536 * row.bBytes.free_in_b_6 + 16777216 * row.bBytes.free_in_b_7

@[reducible]
def cLoValue (row : BinaryRow FGL) : FGL :=
  row.cBytes.free_in_c_0 + 256 * row.cBytes.free_in_c_1
    + 65536 * row.cBytes.free_in_c_2 + 16777216 * row.cBytes.free_in_c_3
    + row.chain.carry_7

@[reducible]
def cHiValue (row : BinaryRow FGL) : FGL :=
  row.cBytes.free_in_c_4 + 256 * row.cBytes.free_in_c_5
    + 65536 * row.cBytes.free_in_c_6 + 16777216 * row.cBytes.free_in_c_7

@[reducible]
def opBusMessage (row : BinaryRow FGL) : OpBusMessage FGL :=
  { op := row.chain.b_op + 16 * row.mode.mode32
    a_lo := aLoValue row
    a_hi := aHiValue row
    b_lo := bLoValue row
    b_hi := bHiValue row
    c_lo := cLoValue row
    c_hi := cHiValue row
    flag := row.chain.carry_7
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

theorem opBusMessage_toEntry_rowAt_eq_opBus_row
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r : ℕ) :
    OpBusMessage.toEntry (opBusMessage (rowAt v r)) 1 =
      ZiskFv.Airs.OperationBus.opBus_row_Binary v r := by
  rfl

/-- **Bridge theorem.** Converts v1's named-accessor constraint
    hypotheses into the Component's `rowAt`-projected Spec form. -/
theorem spec_of_valid
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r : ℕ)
    (_h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h_mode32, h_carry_7, h_result_is_a, h_use_first_byte, h_c_is_signed,
          h_b_op_or_sext, h_m32_cs⟩ := h_constraints
  exact spec_via_component (rowAt v r)
    (by simpa [sub_eq_add_neg] using h_mode32)
    (by simpa [sub_eq_add_neg] using h_carry_7)
    (by simpa [sub_eq_add_neg] using h_result_is_a)
    (by simpa [sub_eq_add_neg] using h_use_first_byte)
    (by simpa [sub_eq_add_neg] using h_c_is_signed)
    (by simpa [sub_eq_add_neg] using h_b_op_or_sext)
    (by simpa [sub_eq_add_neg] using h_m32_cs)

end ZiskFv.AirsClean.Binary
