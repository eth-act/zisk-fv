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
    wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 2 * row.mode.use_first_byte
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_0
        b_byte := row.bBytes.free_in_b_0
        cin := 0
        c_byte := row.cBytes.free_in_c_0
        flags := row.chain.carry_0 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 0
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_1
        b_byte := row.bBytes.free_in_b_1
        cin := row.chain.carry_0
        c_byte := row.cBytes.free_in_c_1
        flags := row.chain.carry_1 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 0
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_2
        b_byte := row.bBytes.free_in_b_2
        cin := row.chain.carry_1
        c_byte := row.cBytes.free_in_c_2
        flags := row.chain.carry_2 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := row.mode.mode32
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_3
        b_byte := row.bBytes.free_in_b_3
        cin := row.chain.carry_2
        c_byte := row.cBytes.free_in_c_3
        flags := row.chain.carry_3 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 0
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_4
        b_byte := row.bBytes.free_in_b_4
        cin := row.chain.carry_3
        c_byte := row.cBytes.free_in_c_4
        flags := row.chain.carry_4 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 0
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_5
        b_byte := row.bBytes.free_in_b_5
        cin := row.chain.carry_4
        c_byte := row.cBytes.free_in_c_5
        flags := row.chain.carry_5 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 0
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_6
        b_byte := row.bBytes.free_in_b_6
        cin := row.chain.carry_5
        c_byte := row.cBytes.free_in_c_6
        flags := row.chain.carry_6 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 1 - row.mode.mode32
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_7
        b_byte := row.bBytes.free_in_b_7
        cin := row.chain.carry_6
        c_byte := row.cBytes.free_in_c_7
        flags := row.chain.carry_7 } 1) := by
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
    ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
      { pos_ind := 2 * row.mode.use_first_byte
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_0
        b_byte := row.bBytes.free_in_b_0
        cin := 0
        c_byte := row.cBytes.free_in_c_0
        flags := row.chain.carry_0 }
  ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
      { pos_ind := 0
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_1
        b_byte := row.bBytes.free_in_b_1
        cin := row.chain.carry_0
        c_byte := row.cBytes.free_in_c_1
        flags := row.chain.carry_1 }
  ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
      { pos_ind := 0
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_2
        b_byte := row.bBytes.free_in_b_2
        cin := row.chain.carry_1
        c_byte := row.cBytes.free_in_c_2
        flags := row.chain.carry_2 }
  ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
      { pos_ind := row.mode.mode32
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_3
        b_byte := row.bBytes.free_in_b_3
        cin := row.chain.carry_2
        c_byte := row.cBytes.free_in_c_3
        flags := row.chain.carry_3 }
  ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
      { pos_ind := 0
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_4
        b_byte := row.bBytes.free_in_b_4
        cin := row.chain.carry_3
        c_byte := row.cBytes.free_in_c_4
        flags := row.chain.carry_4 }
  ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
      { pos_ind := 0
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_5
        b_byte := row.bBytes.free_in_b_5
        cin := row.chain.carry_4
        c_byte := row.cBytes.free_in_c_5
        flags := row.chain.carry_5 }
  ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
      { pos_ind := 0
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_6
        b_byte := row.bBytes.free_in_b_6
        cin := row.chain.carry_5
        c_byte := row.cBytes.free_in_c_6
        flags := row.chain.carry_6 }
  ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
      { pos_ind := 1 - row.mode.mode32
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_7
        b_byte := row.bBytes.free_in_b_7
        cin := row.chain.carry_6
        c_byte := row.cBytes.free_in_c_7
        flags := row.chain.carry_7 } := by
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
        , by simpa [Lookup.Soundness, Table.fromStatic, StaticTable.toTable,
                    Table.toRaw, sub_eq_add_neg] using h7 ⟩

open ZiskFv.Airs.Tables.BinaryTable in
/-- The eight legacy `BinaryTable.wf_properties` facts for the exact rows
    emitted by Binary's static-table lookup path. This is the shared C7 target
    shape: downstream Binary proofs should consume this fact rather than call
    `bin_table_consumer_wf` directly. -/
abbrev StaticBinaryTableWfFacts (row : BinaryRow FGL) : Prop :=
    wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 2 * row.mode.use_first_byte
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_0
        b_byte := row.bBytes.free_in_b_0
        cin := 0
        c_byte := row.cBytes.free_in_c_0
        flags := row.chain.carry_0 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 0
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_1
        b_byte := row.bBytes.free_in_b_1
        cin := row.chain.carry_0
        c_byte := row.cBytes.free_in_c_1
        flags := row.chain.carry_1 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 0
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_2
        b_byte := row.bBytes.free_in_b_2
        cin := row.chain.carry_1
        c_byte := row.cBytes.free_in_c_2
        flags := row.chain.carry_2 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := row.mode.mode32
        op := row.chain.b_op
        a_byte := row.aBytes.free_in_a_3
        b_byte := row.bBytes.free_in_b_3
        cin := row.chain.carry_2
        c_byte := row.cBytes.free_in_c_3
        flags := row.chain.carry_3 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 0
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_4
        b_byte := row.bBytes.free_in_b_4
        cin := row.chain.carry_3
        c_byte := row.cBytes.free_in_c_4
        flags := row.chain.carry_4 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 0
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_5
        b_byte := row.bBytes.free_in_b_5
        cin := row.chain.carry_4
        c_byte := row.cBytes.free_in_c_5
        flags := row.chain.carry_5 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 0
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_6
        b_byte := row.bBytes.free_in_b_6
        cin := row.chain.carry_5
        c_byte := row.cBytes.free_in_c_6
        flags := row.chain.carry_6 } 1)
  ∧ wf_properties (BinaryTableMessage.toEntry
      { pos_ind := 1 - row.mode.mode32
        op := row.chain.b_op_or_sext
        a_byte := row.aBytes.free_in_a_7
        b_byte := row.bBytes.free_in_b_7
        cin := row.chain.carry_6
        c_byte := row.cBytes.free_in_c_7
        flags := row.chain.carry_7 } 1)

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
