import ZiskFv.AirsClean.Binary.Circuit
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Channels.OperationBus
import ZiskFv.Channels.BinaryTable

/-!
# `Valid_Binary` ↔ `BinaryRow` compatibility

Post-F1 Bridge: all 20 columns reached via named accessors on
`Valid_Binary FGL FGL`. No `Circuit.main`/`v.circuit` left.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open ZiskFv.Channels.OperationBus
open ZiskFv.Channels.BinaryTable

open ZiskFv.Airs.Tables.BinaryTable in
/-- The eight legacy `BinaryTable.wf_properties` facts for the exact rows
    emitted by Binary's static-table lookup path. -/
abbrev StaticBinaryTableWfFacts (row : BinaryRow FGL) : Prop :=
    wf_properties (BinaryTableMessage.toEntry (lookupMessage0Row row) 1)
  ∧ wf_properties (BinaryTableMessage.toEntry (lookupMessage1Row row) 1)
  ∧ wf_properties (BinaryTableMessage.toEntry (lookupMessage2Row row) 1)
  ∧ wf_properties (BinaryTableMessage.toEntry (lookupMessage3Row row) 1)
  ∧ wf_properties (BinaryTableMessage.toEntry (lookupMessage4Row row) 1)
  ∧ wf_properties (BinaryTableMessage.toEntry (lookupMessage5Row row) 1)
  ∧ wf_properties (BinaryTableMessage.toEntry (lookupMessage6Row row) 1)
  ∧ wf_properties (BinaryTableMessage.toEntry (lookupMessage7Row row) 1)

@[reducible]
def constVar (row : BinaryRow FGL) : Var BinaryRow FGL where
  aBytes := {
    free_in_a_0 := .const row.aBytes.free_in_a_0
    free_in_a_1 := .const row.aBytes.free_in_a_1
    free_in_a_2 := .const row.aBytes.free_in_a_2
    free_in_a_3 := .const row.aBytes.free_in_a_3
    free_in_a_4 := .const row.aBytes.free_in_a_4
    free_in_a_5 := .const row.aBytes.free_in_a_5
    free_in_a_6 := .const row.aBytes.free_in_a_6
    free_in_a_7 := .const row.aBytes.free_in_a_7 }
  bBytes := {
    free_in_b_0 := .const row.bBytes.free_in_b_0
    free_in_b_1 := .const row.bBytes.free_in_b_1
    free_in_b_2 := .const row.bBytes.free_in_b_2
    free_in_b_3 := .const row.bBytes.free_in_b_3
    free_in_b_4 := .const row.bBytes.free_in_b_4
    free_in_b_5 := .const row.bBytes.free_in_b_5
    free_in_b_6 := .const row.bBytes.free_in_b_6
    free_in_b_7 := .const row.bBytes.free_in_b_7 }
  cBytes := {
    free_in_c_0 := .const row.cBytes.free_in_c_0
    free_in_c_1 := .const row.cBytes.free_in_c_1
    free_in_c_2 := .const row.cBytes.free_in_c_2
    free_in_c_3 := .const row.cBytes.free_in_c_3
    free_in_c_4 := .const row.cBytes.free_in_c_4
    free_in_c_5 := .const row.cBytes.free_in_c_5
    free_in_c_6 := .const row.cBytes.free_in_c_6
    free_in_c_7 := .const row.cBytes.free_in_c_7 }
  chain := {
    carry_0 := .const row.chain.carry_0
    carry_1 := .const row.chain.carry_1
    carry_2 := .const row.chain.carry_2
    carry_3 := .const row.chain.carry_3
    carry_4 := .const row.chain.carry_4
    carry_5 := .const row.chain.carry_5
    carry_6 := .const row.chain.carry_6
    carry_7 := .const row.chain.carry_7
    b_op := .const row.chain.b_op
    b_op_or_sext := .const row.chain.b_op_or_sext }
  mode := {
    mode32 := .const row.mode.mode32
    result_is_a := .const row.mode.result_is_a
    use_first_byte := .const row.mode.use_first_byte
    c_is_signed := .const row.mode.c_is_signed
    mode32_and_c_is_signed := .const row.mode.mode32_and_c_is_signed }

open ZiskFv.Airs.Tables.BinaryTable in
/-- Constant-row specialization of the lookup-aware BinaryTable channel path.
    The eight returned facts are sourced from `mainWithBinaryTable`'s channel
    pulls, not from `bin_table_consumer_wf`. This is C6 groundwork for C7:
    the theorem is local until the balanced BinaryTable provider side exists. -/
theorem binary_table_wf_of_lookup_aware_const_soundness
    (offset : ℕ) (env : Environment FGL) (row : BinaryRow FGL)
    (h_holds :
      ConstraintsHold.Soundness env
        ((mainWithBinaryTable (constVar row)).operations offset)) :
    StaticBinaryTableWfFacts row := by
  simp only [mainWithBinaryTable, main, circuit_norm] at h_holds
  rcases h_holds with
    ⟨_h0, _h1, _h2, _h3, _h4, _h5, _h6,
      h0, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨ by simpa [BinaryTableChannel, BinaryTableMessage.toEntry] using h0
        , by simpa [BinaryTableChannel, BinaryTableMessage.toEntry] using h1
        , by simpa [BinaryTableChannel, BinaryTableMessage.toEntry] using h2
        , by simpa [BinaryTableChannel, BinaryTableMessage.toEntry] using h3
        , by simpa [BinaryTableChannel, BinaryTableMessage.toEntry] using h4
        , by simpa [BinaryTableChannel, BinaryTableMessage.toEntry] using h5
        , by simpa [BinaryTableChannel, BinaryTableMessage.toEntry] using h6
        , by simpa [BinaryTableChannel, BinaryTableMessage.toEntry, sub_eq_add_neg] using h7 ⟩

/-- Constant-row specialization of the static-provider BinaryTable lookup
    path. The eight returned facts are exact decoded-row memberships in
    `AirsClean.BinaryTable.binaryTable`, sourced from
    `mainWithStaticBinaryTable`'s Clean `lookup (Table.fromStatic ...)`
    operations.

    This is the provider-side counterpart to
    `binary_table_wf_of_lookup_aware_const_soundness`: it proves membership
    in the static table, not yet the semantic `wf_properties` projection. -/
theorem binary_table_specs_of_static_lookup_const_soundness
    (offset : ℕ) (env : Environment FGL) (row : BinaryRow FGL)
    (h_holds :
      ConstraintsHold.Soundness env
        ((mainWithStaticBinaryTable (constVar row)).operations offset)) :
    StaticBinaryTableSpecFacts row := by
  simp only [mainWithStaticBinaryTable, main, circuit_norm] at h_holds
  rcases h_holds with
    ⟨_h0, _h1, _h2, _h3, _h4, _h5, _h6,
      h0, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨ by simpa [Lookup.Soundness, Table.fromStatic, StaticTable.toTable,
                    Table.toRaw] using h0
        , by simpa [Lookup.Soundness, Table.fromStatic, StaticTable.toTable,
                    Table.toRaw] using h1
        , by simpa [Lookup.Soundness, Table.fromStatic, StaticTable.toTable,
                    Table.toRaw] using h2
        , by simpa [Lookup.Soundness, Table.fromStatic, StaticTable.toTable,
                    Table.toRaw] using h3
        , by simpa [Lookup.Soundness, Table.fromStatic, StaticTable.toTable,
                    Table.toRaw] using h4
        , by simpa [Lookup.Soundness, Table.fromStatic, StaticTable.toTable,
                    Table.toRaw] using h5
        , by simpa [Lookup.Soundness, Table.fromStatic, StaticTable.toTable,
                    Table.toRaw] using h6
        , by
            simp [Lookup.Soundness, Table.fromStatic, StaticTable.toTable,
              Table.toRaw, lookupMessage7Row, lookupFlags7Row, sub_eq_add_neg] at h7 ⊢
            exact h7 ⟩

open ZiskFv.Airs.Tables.BinaryTable in
/-- Static-provider BinaryTable lookup path, projected all the way to the
    legacy semantic `wf_properties` facts. Unlike
    `binary_table_wf_of_lookup_aware_const_soundness`, this consumes exact
    membership in `AirsClean.BinaryTable.binaryTable` and the proved
    membership-to-semantics projections, not `bin_table_consumer_wf`. -/
theorem binary_table_wf_of_static_lookup_const_soundness
    (offset : ℕ) (env : Environment FGL) (row : BinaryRow FGL)
    (h_holds :
      ConstraintsHold.Soundness env
        ((mainWithStaticBinaryTable (constVar row)).operations offset)) :
    StaticBinaryTableWfFacts row := by
  have h_specs := binary_table_specs_of_static_lookup_const_soundness offset env row h_holds
  rcases h_specs with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨ ZiskFv.AirsClean.BinaryTable.spec_wf_properties h0
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h1
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h2
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h3
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h4
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h5
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h6
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h7 ⟩

/-- Project the lookup-aware Binary component's static-table spec facts to
    the legacy semantic `wf_properties` bundle consumed by row-native
    Binary proofs. -/
theorem static_table_wf_facts_of_spec_facts
    (row : BinaryRow FGL)
    (h_static : StaticBinaryTableSpecFacts row) :
    StaticBinaryTableWfFacts row := by
  rcases h_static with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨ ZiskFv.AirsClean.BinaryTable.spec_wf_properties h0
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h1
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h2
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h3
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h4
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h5
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h6
        , ZiskFv.AirsClean.BinaryTable.spec_wf_properties h7 ⟩

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

@[reducible]
def validOfRow (row : BinaryRow FGL) :
    ZiskFv.Airs.Binary.Valid_Binary FGL FGL where
  b_op := fun _ => row.chain.b_op
  free_in_a_0 := fun _ => row.aBytes.free_in_a_0
  free_in_a_1 := fun _ => row.aBytes.free_in_a_1
  free_in_a_2 := fun _ => row.aBytes.free_in_a_2
  free_in_a_3 := fun _ => row.aBytes.free_in_a_3
  free_in_a_4 := fun _ => row.aBytes.free_in_a_4
  free_in_a_5 := fun _ => row.aBytes.free_in_a_5
  free_in_a_6 := fun _ => row.aBytes.free_in_a_6
  free_in_a_7 := fun _ => row.aBytes.free_in_a_7
  free_in_b_0 := fun _ => row.bBytes.free_in_b_0
  free_in_b_1 := fun _ => row.bBytes.free_in_b_1
  free_in_b_2 := fun _ => row.bBytes.free_in_b_2
  free_in_b_3 := fun _ => row.bBytes.free_in_b_3
  free_in_b_4 := fun _ => row.bBytes.free_in_b_4
  free_in_b_5 := fun _ => row.bBytes.free_in_b_5
  free_in_b_6 := fun _ => row.bBytes.free_in_b_6
  free_in_b_7 := fun _ => row.bBytes.free_in_b_7
  free_in_c_0 := fun _ => row.cBytes.free_in_c_0
  free_in_c_1 := fun _ => row.cBytes.free_in_c_1
  free_in_c_2 := fun _ => row.cBytes.free_in_c_2
  free_in_c_3 := fun _ => row.cBytes.free_in_c_3
  free_in_c_4 := fun _ => row.cBytes.free_in_c_4
  free_in_c_5 := fun _ => row.cBytes.free_in_c_5
  free_in_c_6 := fun _ => row.cBytes.free_in_c_6
  free_in_c_7 := fun _ => row.cBytes.free_in_c_7
  carry_0 := fun _ => row.chain.carry_0
  carry_1 := fun _ => row.chain.carry_1
  carry_2 := fun _ => row.chain.carry_2
  carry_3 := fun _ => row.chain.carry_3
  carry_4 := fun _ => row.chain.carry_4
  carry_5 := fun _ => row.chain.carry_5
  carry_6 := fun _ => row.chain.carry_6
  carry_7 := fun _ => row.chain.carry_7
  mode32 := fun _ => row.mode.mode32
  result_is_a := fun _ => row.mode.result_is_a
  use_first_byte := fun _ => row.mode.use_first_byte
  c_is_signed := fun _ => row.mode.c_is_signed
  b_op_or_sext := fun _ => row.chain.b_op_or_sext
  mode32_and_c_is_signed := fun _ => row.mode.mode32_and_c_is_signed
  gsum := fun _ => 0
  im_0 := fun _ => 0
  im_1 := fun _ => 0
  im_2 := fun _ => 0
  im_3 := fun _ => 0

theorem rowAt_validOfRow_zero (row : BinaryRow FGL) :
    rowAt (validOfRow row) 0 = row := by
  cases row
  rfl

/-- Project the lookup-aware Binary component's algebraic `Spec` to the
    legacy `core_every_row` predicate on the one-row `validOfRow` view. -/
theorem core_every_row_of_spec
    (row : BinaryRow FGL) (h_spec : Spec row) :
    ZiskFv.Airs.Binary.core_every_row (validOfRow row) 0 := by
  rcases h_spec with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  exact ⟨ by simpa [validOfRow, ZiskFv.Airs.Binary.boolean_mode32,
            sub_eq_add_neg] using h0
        , by simpa [validOfRow, ZiskFv.Airs.Binary.boolean_carry_7,
            sub_eq_add_neg] using h1
        , by simpa [validOfRow, ZiskFv.Airs.Binary.boolean_result_is_a,
            sub_eq_add_neg] using h2
        , by simpa [validOfRow, ZiskFv.Airs.Binary.boolean_use_first_byte,
            sub_eq_add_neg] using h3
        , by simpa [validOfRow, ZiskFv.Airs.Binary.boolean_c_is_signed,
            sub_eq_add_neg] using h4
        , by simpa [validOfRow, ZiskFv.Airs.Binary.b_op_or_sext_def_holds,
            sub_eq_add_neg] using h5
        , by simpa [validOfRow,
            ZiskFv.Airs.Binary.mode32_and_c_is_signed_def_holds,
            sub_eq_add_neg] using h6 ⟩

/-- Exact static BinaryTable membership rules out the ambiguous
    `b_op + 16 * mode32 = 16` / `mode32 = 1` shape. If the Binary op-bus
    emission is XOR, the row's high-byte opcode column is also XOR. -/
theorem static_table_b_op_or_sext_eq_of_xor_emit
    (row : BinaryRow FGL)
    (h_spec : Spec row)
    (h_static : StaticBinaryTableSpecFacts row)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (16 : FGL)) :
    row.chain.b_op_or_sext.val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR := by
  rcases h_spec with ⟨h_mode32, _, _, _, _, h_bop_or_sext_def, _⟩
  rcases h_static with ⟨_, _, _, h3, _, _, _, _⟩
  have h_bop_or_eq_of_mode32_zero
      (h_zero : row.mode.mode32 = 0) :
      row.chain.b_op_or_sext = row.chain.b_op := by
    have h_eq := sub_eq_zero.mp h_bop_or_sext_def
    rw [h_zero] at h_eq
    simpa using h_eq
  have h_mode : row.mode.mode32 = 0 ∨ row.mode.mode32 = 1 := by
    rcases mul_eq_zero.mp h_mode32 with h_zero | h_one_sub
    · exact Or.inl h_zero
    · exact Or.inr ((sub_eq_zero.mp h_one_sub).symm)
  rcases h_mode with h_zero | h_one
  · have h_bop : row.chain.b_op = (16 : FGL) := by
      simpa [h_zero] using h_emit
    rw [h_bop_or_eq_of_mode32_zero h_zero, h_bop]
    norm_num [ZiskFv.Airs.Tables.BinaryTable.OP_XOR]
  · have h_bop_zero : row.chain.b_op = 0 := by
      rw [h_one] at h_emit
      simpa using (add_right_cancel h_emit)
    have h_ne := ZiskFv.AirsClean.BinaryTable.spec_op_val_ne_zero h3
    exact False.elim (h_ne (by simp [lookupMessage3Row, h_bop_zero]))

/-- Exact static BinaryTable membership also pins the low-byte opcode and
    `mode32` for an emitted XOR row. -/
theorem static_table_xor_mode_pins_of_emit
    (row : BinaryRow FGL)
    (h_spec : Spec row)
    (h_static : StaticBinaryTableSpecFacts row)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (16 : FGL)) :
    row.mode.mode32 = 0
      ∧ row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR
      ∧ row.chain.b_op_or_sext.val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR := by
  rcases h_spec with ⟨h_mode32, _, _, _, _, h_bop_or_sext_def, _⟩
  rcases h_static with ⟨_, _, _, h3, _, _, _, _⟩
  have h_mode : row.mode.mode32 = 0 ∨ row.mode.mode32 = 1 := by
    rcases mul_eq_zero.mp h_mode32 with h_zero | h_one_sub
    · exact Or.inl h_zero
    · exact Or.inr ((sub_eq_zero.mp h_one_sub).symm)
  rcases h_mode with h_zero | h_one
  · have h_bop : row.chain.b_op = (16 : FGL) := by
      simpa [h_zero] using h_emit
    have h_bop_or_eq : row.chain.b_op_or_sext = row.chain.b_op := by
      have h_eq := sub_eq_zero.mp h_bop_or_sext_def
      rw [h_zero] at h_eq
      simpa using h_eq
    refine ⟨h_zero, ?_, ?_⟩
    · rw [h_bop]
      norm_num [ZiskFv.Airs.Tables.BinaryTable.OP_XOR]
    · rw [h_bop_or_eq, h_bop]
      norm_num [ZiskFv.Airs.Tables.BinaryTable.OP_XOR]
  · have h_bop_zero : row.chain.b_op = 0 := by
      rw [h_one] at h_emit
      simpa using (add_right_cancel h_emit)
    have h_ne := ZiskFv.AirsClean.BinaryTable.spec_op_val_ne_zero h3
    exact False.elim (h_ne (by simp [lookupMessage3Row, h_bop_zero]))

/-- Exact static BinaryTable membership plus the Binary boolean/core row
    constraints pin the 64-bit logic op-bus shapes without the legacy
    range-bus column bounds. -/
theorem static_table_logic_mode_pins_of_emit
    (row : BinaryRow FGL)
    (h_spec : Spec row)
    (h_static : StaticBinaryTableSpecFacts row)
    (op_val : ℕ)
    (h_op_logic :
      op_val = ZiskFv.Airs.Tables.BinaryTable.OP_AND
        ∨ op_val = ZiskFv.Airs.Tables.BinaryTable.OP_OR
        ∨ op_val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_val : FGL)) :
    row.mode.mode32 = 0
      ∧ row.chain.b_op.val = op_val
      ∧ row.chain.b_op_or_sext.val = op_val := by
  rcases h_spec with ⟨h_mode32, _, _, _, _, h_bop_or_sext_def, _⟩
  rcases h_static with ⟨h0, _, _, _, _, _, _, _⟩
  have h_bop_lt : row.chain.b_op.val < 514 := by
    have h := ZiskFv.AirsClean.BinaryTable.spec_op_val_lt_514 h0
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h
  have h_bop_ne_zero : row.chain.b_op.val ≠ 0 := by
    have h := ZiskFv.AirsClean.BinaryTable.spec_op_val_ne_zero h0
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry] using h
  have h_op_small : op_val < 17 := by
    rcases h_op_logic with h | h | h <;>
      simp [h, ZiskFv.Airs.Tables.BinaryTable.OP_AND,
        ZiskFv.Airs.Tables.BinaryTable.OP_OR,
        ZiskFv.Airs.Tables.BinaryTable.OP_XOR]
  have h_mode : row.mode.mode32 = 0 ∨ row.mode.mode32 = 1 := by
    rcases mul_eq_zero.mp h_mode32 with h_zero | h_one_sub
    · exact Or.inl h_zero
    · exact Or.inr ((sub_eq_zero.mp h_one_sub).symm)
  rcases h_mode with h_zero | h_one
  · have h_bop : row.chain.b_op = (op_val : FGL) := by
      simpa [h_zero] using h_emit
    have h_bop_or_eq : row.chain.b_op_or_sext = row.chain.b_op := by
      have h_eq := sub_eq_zero.mp h_bop_or_sext_def
      rw [h_zero] at h_eq
      simpa using h_eq
    refine ⟨h_zero, ?_, ?_⟩
    · have h_val := congrArg Fin.val h_bop
      rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : op_val < GL_prime)] at h_val
      exact h_val
    · rw [h_bop_or_eq]
      have h_val := congrArg Fin.val h_bop
      rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : op_val < GL_prime)] at h_val
      exact h_val
  · have hval : row.chain.b_op.val + 16 = op_val := by
      have hv := congrArg Fin.val h_emit
      rw [h_one, Fin.val_add, Fin.val_mul, Fin.val_natCast] at hv
      have hsmall : row.chain.b_op.val + 16 < GL_prime := by omega
      simp [Nat.mod_eq_of_lt hsmall,
        Nat.mod_eq_of_lt (by omega : 16 < GL_prime),
        Nat.mod_eq_of_lt (by omega : op_val < GL_prime)] at hv
      exact hv
    have h_bop_zero : row.chain.b_op.val = 0 := by omega
    exact False.elim (h_bop_ne_zero h_bop_zero)

/-- Shared C7 witness surface for Binary's static-table lookup path.
    This is intentionally family-level and row-indexed; it is the shape a
    terminal Binary-family ensemble can provide once the static provider is
    wired into the same Clean path. -/
def StaticLookupSoundness (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) : Prop :=
  ∀ (r offset : ℕ) (env : Environment FGL),
    ConstraintsHold.Soundness env
      ((mainWithStaticBinaryTable (constVar (rowAt v r))).operations offset)

/-- Project the shared C7 Binary static-lookup witness to the legacy
    per-byte semantic facts for row `r`. -/
theorem static_lookup_wf_facts
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r offset : ℕ)
    (env : Environment FGL) (h_static : StaticLookupSoundness v) :
    StaticBinaryTableWfFacts (rowAt v r) :=
  binary_table_wf_of_static_lookup_const_soundness offset env (rowAt v r)
    (h_static r offset env)

/-- Project the shared C7 Binary static-lookup witness to the exact static
    BinaryTable membership facts for row `r`. This is stronger than
    `static_lookup_wf_facts` and is needed when downstream code must rule out
    ambiguous opcode shapes before projecting semantic `wf_properties`. -/
theorem static_lookup_spec_facts
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r offset : ℕ)
    (env : Environment FGL) (h_static : StaticLookupSoundness v) :
    StaticBinaryTableSpecFacts (rowAt v r) :=
  binary_table_specs_of_static_lookup_const_soundness offset env (rowAt v r)
    (h_static r offset env)

/-- The same static-lookup path also contains Binary's seven F-typed core
    constraints, projected to the Clean-row `Spec` shape. -/
theorem spec_of_static_lookup
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r offset : ℕ)
    (env : Environment FGL) (h_static : StaticLookupSoundness v) :
    Spec (rowAt v r) := by
  have h_holds := h_static r offset env
  simp only [mainWithStaticBinaryTable, main, circuit_norm] at h_holds
  rcases h_holds with
    ⟨h0, h1, h2, h3, h4, h5, h6, _h7, _h8, _h9, _h10, _h11, _h12, _h13, _h14⟩
  exact ⟨ by simpa [rowAt, sub_eq_add_neg] using h0
        , by simpa [rowAt, sub_eq_add_neg] using h1
        , by simpa [rowAt, sub_eq_add_neg] using h2
        , by simpa [rowAt, sub_eq_add_neg] using h3
        , by simpa [rowAt, sub_eq_add_neg] using h4
        , by simpa [rowAt, sub_eq_add_neg] using h5
        , by simpa [rowAt, sub_eq_add_neg] using h6 ⟩

/-- The same static-lookup path also contains Binary's seven F-typed core
    constraints before the eight table lookups. This projects those
    constraints back to the legacy `core_every_row` predicate, so C7 callers
    do not need to supply Binary core facts separately from
    `StaticLookupSoundness`. -/
theorem core_every_row_of_static_lookup
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r offset : ℕ)
    (env : Environment FGL) (h_static : StaticLookupSoundness v) :
    ZiskFv.Airs.Binary.core_every_row v r := by
  have h_holds := h_static r offset env
  simp only [mainWithStaticBinaryTable, main, circuit_norm] at h_holds
  rcases h_holds with
    ⟨h0, h1, h2, h3, h4, h5, h6, _h7, _h8, _h9, _h10, _h11, _h12, _h13, _h14⟩
  exact ⟨ by simpa [ZiskFv.Airs.Binary.boolean_mode32, sub_eq_add_neg] using h0
        , by simpa [ZiskFv.Airs.Binary.boolean_carry_7, sub_eq_add_neg] using h1
        , by simpa [ZiskFv.Airs.Binary.boolean_result_is_a, sub_eq_add_neg] using h2
        , by simpa [ZiskFv.Airs.Binary.boolean_use_first_byte, sub_eq_add_neg] using h3
        , by simpa [ZiskFv.Airs.Binary.boolean_c_is_signed, sub_eq_add_neg] using h4
        , by simpa [ZiskFv.Airs.Binary.b_op_or_sext_def_holds, sub_eq_add_neg] using h5
        , by simpa [ZiskFv.Airs.Binary.mode32_and_c_is_signed_def_holds,
            sub_eq_add_neg] using h6 ⟩

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

theorem aByteCols_eval_eq
    (env : Environment FGL) (cols : BinaryAByteCols (Expression FGL)) :
    eval env cols =
      { free_in_a_0 := Expression.eval env cols.free_in_a_0
        free_in_a_1 := Expression.eval env cols.free_in_a_1
        free_in_a_2 := Expression.eval env cols.free_in_a_2
        free_in_a_3 := Expression.eval env cols.free_in_a_3
        free_in_a_4 := Expression.eval env cols.free_in_a_4
        free_in_a_5 := Expression.eval env cols.free_in_a_5
        free_in_a_6 := Expression.eval env cols.free_in_a_6
        free_in_a_7 := Expression.eval env cols.free_in_a_7 } := by
  rw [ProvableStruct.eval_eq_eval]
  cases cols
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]

theorem bByteCols_eval_eq
    (env : Environment FGL) (cols : BinaryBByteCols (Expression FGL)) :
    eval env cols =
      { free_in_b_0 := Expression.eval env cols.free_in_b_0
        free_in_b_1 := Expression.eval env cols.free_in_b_1
        free_in_b_2 := Expression.eval env cols.free_in_b_2
        free_in_b_3 := Expression.eval env cols.free_in_b_3
        free_in_b_4 := Expression.eval env cols.free_in_b_4
        free_in_b_5 := Expression.eval env cols.free_in_b_5
        free_in_b_6 := Expression.eval env cols.free_in_b_6
        free_in_b_7 := Expression.eval env cols.free_in_b_7 } := by
  rw [ProvableStruct.eval_eq_eval]
  cases cols
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]

theorem cByteCols_eval_eq
    (env : Environment FGL) (cols : BinaryCByteCols (Expression FGL)) :
    eval env cols =
      { free_in_c_0 := Expression.eval env cols.free_in_c_0
        free_in_c_1 := Expression.eval env cols.free_in_c_1
        free_in_c_2 := Expression.eval env cols.free_in_c_2
        free_in_c_3 := Expression.eval env cols.free_in_c_3
        free_in_c_4 := Expression.eval env cols.free_in_c_4
        free_in_c_5 := Expression.eval env cols.free_in_c_5
        free_in_c_6 := Expression.eval env cols.free_in_c_6
        free_in_c_7 := Expression.eval env cols.free_in_c_7 } := by
  rw [ProvableStruct.eval_eq_eval]
  cases cols
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]

theorem chainCols_eval_eq
    (env : Environment FGL) (cols : BinaryChainCols (Expression FGL)) :
    eval env cols =
      { carry_0 := Expression.eval env cols.carry_0
        carry_1 := Expression.eval env cols.carry_1
        carry_2 := Expression.eval env cols.carry_2
        carry_3 := Expression.eval env cols.carry_3
        carry_4 := Expression.eval env cols.carry_4
        carry_5 := Expression.eval env cols.carry_5
        carry_6 := Expression.eval env cols.carry_6
        carry_7 := Expression.eval env cols.carry_7
        b_op := Expression.eval env cols.b_op
        b_op_or_sext := Expression.eval env cols.b_op_or_sext } := by
  rw [ProvableStruct.eval_eq_eval]
  cases cols
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]

theorem modeCols_eval_eq
    (env : Environment FGL) (cols : BinaryModeCols (Expression FGL)) :
    eval env cols =
      { mode32 := Expression.eval env cols.mode32
        result_is_a := Expression.eval env cols.result_is_a
        use_first_byte := Expression.eval env cols.use_first_byte
        c_is_signed := Expression.eval env cols.c_is_signed
        mode32_and_c_is_signed :=
          Expression.eval env cols.mode32_and_c_is_signed } := by
  rw [ProvableStruct.eval_eq_eval]
  cases cols
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]

theorem eval_opBusMessageExpr
    (env : Environment FGL) (row : Var BinaryRow FGL) :
    eval env (opBusMessageExpr row) = opBusMessage (eval env row) := by
  cases row
  simp only [opBusMessageExpr, opBusMessage, aLoValue, aHiValue,
    bLoValue, bHiValue, cLoValue, cHiValue, ProvableStruct.eval_eq_eval]
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]
  simp [aByteCols_eval_eq, bByteCols_eval_eq, cByteCols_eval_eq,
    chainCols_eval_eq, modeCols_eval_eq, Expression.eval]

theorem staticLookupComponent_eval_opBusMessageExpr
    (env : Environment FGL) :
    eval env (opBusMessageExpr staticLookupComponent.rowInputVar) =
      opBusMessage (staticLookupComponent.rowInput env) := by
  rw [eval_opBusMessageExpr]
  exact congrArg opBusMessage
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset staticLookupComponent.Input 0 env))

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
