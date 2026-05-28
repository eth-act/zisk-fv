import ZiskFv.AirsClean.BinaryExtension.Circuit
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Channels.OperationBus
import ZiskFv.Channels.BinaryExtensionTable

/-!
# `Valid_BinaryExtension` ↔ `BinaryExtensionRow` compatibility

Post-D3 Bridge: all 30 columns reached via named accessors on
`Valid_BinaryExtension FGL FGL`. No `Circuit.main`/`v.circuit` left.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks
open ZiskFv.Channels.OperationBus
open ZiskFv.Channels.BinaryExtensionTable

@[reducible]
def rowAt (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (r : ℕ) :
    BinaryExtensionRow FGL where
  aCols := {
    free_in_a_0 := v.free_in_a_0 r
    free_in_a_1 := v.free_in_a_1 r
    free_in_a_2 := v.free_in_a_2 r
    free_in_a_3 := v.free_in_a_3 r
    free_in_a_4 := v.free_in_a_4 r
    free_in_a_5 := v.free_in_a_5 r
    free_in_a_6 := v.free_in_a_6 r
    free_in_a_7 := v.free_in_a_7 r
  }
  cColsLo := {
    free_in_c_0 := v.free_in_c_0 r
    free_in_c_1 := v.free_in_c_1 r
    free_in_c_2 := v.free_in_c_2 r
    free_in_c_3 := v.free_in_c_3 r
    free_in_c_4 := v.free_in_c_4 r
    free_in_c_5 := v.free_in_c_5 r
    free_in_c_6 := v.free_in_c_6 r
    free_in_c_7 := v.free_in_c_7 r
  }
  cColsHi := {
    free_in_c_8 := v.free_in_c_8 r
    free_in_c_9 := v.free_in_c_9 r
    free_in_c_10 := v.free_in_c_10 r
    free_in_c_11 := v.free_in_c_11 r
    free_in_c_12 := v.free_in_c_12 r
    free_in_c_13 := v.free_in_c_13 r
    free_in_c_14 := v.free_in_c_14 r
    free_in_c_15 := v.free_in_c_15 r
  }
  flags := {
    op := v.op r
    free_in_b := v.free_in_b r
    op_is_shift := v.op_is_shift r
    b_0 := v.b_0 r
    b_1 := v.b_1 r
  }

@[reducible]
def validOfRow (row : BinaryExtensionRow FGL) :
    ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL where
  op := fun _ => row.flags.op
  free_in_a_0 := fun _ => row.aCols.free_in_a_0
  free_in_a_1 := fun _ => row.aCols.free_in_a_1
  free_in_a_2 := fun _ => row.aCols.free_in_a_2
  free_in_a_3 := fun _ => row.aCols.free_in_a_3
  free_in_a_4 := fun _ => row.aCols.free_in_a_4
  free_in_a_5 := fun _ => row.aCols.free_in_a_5
  free_in_a_6 := fun _ => row.aCols.free_in_a_6
  free_in_a_7 := fun _ => row.aCols.free_in_a_7
  free_in_b := fun _ => row.flags.free_in_b
  free_in_c_0 := fun _ => row.cColsLo.free_in_c_0
  free_in_c_1 := fun _ => row.cColsLo.free_in_c_1
  free_in_c_2 := fun _ => row.cColsLo.free_in_c_2
  free_in_c_3 := fun _ => row.cColsLo.free_in_c_3
  free_in_c_4 := fun _ => row.cColsLo.free_in_c_4
  free_in_c_5 := fun _ => row.cColsLo.free_in_c_5
  free_in_c_6 := fun _ => row.cColsLo.free_in_c_6
  free_in_c_7 := fun _ => row.cColsLo.free_in_c_7
  free_in_c_8 := fun _ => row.cColsHi.free_in_c_8
  free_in_c_9 := fun _ => row.cColsHi.free_in_c_9
  free_in_c_10 := fun _ => row.cColsHi.free_in_c_10
  free_in_c_11 := fun _ => row.cColsHi.free_in_c_11
  free_in_c_12 := fun _ => row.cColsHi.free_in_c_12
  free_in_c_13 := fun _ => row.cColsHi.free_in_c_13
  free_in_c_14 := fun _ => row.cColsHi.free_in_c_14
  free_in_c_15 := fun _ => row.cColsHi.free_in_c_15
  op_is_shift := fun _ => row.flags.op_is_shift
  b_0 := fun _ => row.flags.b_0
  b_1 := fun _ => row.flags.b_1
  gsum := fun _ => 0
  im_0 := fun _ => 0
  im_1 := fun _ => 0
  im_2 := fun _ => 0
  im_3 := fun _ => 0
  im_high_degree_0 := fun _ => 0

theorem rowAt_validOfRow_zero (row : BinaryExtensionRow FGL) :
    rowAt (validOfRow row) 0 = row := by
  cases row
  rfl

@[reducible]
def constVar (row : BinaryExtensionRow FGL) : Var BinaryExtensionRow FGL :=
  { aCols := {
      free_in_a_0 := .const row.aCols.free_in_a_0
      free_in_a_1 := .const row.aCols.free_in_a_1
      free_in_a_2 := .const row.aCols.free_in_a_2
      free_in_a_3 := .const row.aCols.free_in_a_3
      free_in_a_4 := .const row.aCols.free_in_a_4
      free_in_a_5 := .const row.aCols.free_in_a_5
      free_in_a_6 := .const row.aCols.free_in_a_6
      free_in_a_7 := .const row.aCols.free_in_a_7 }
    cColsLo := {
      free_in_c_0 := .const row.cColsLo.free_in_c_0
      free_in_c_1 := .const row.cColsLo.free_in_c_1
      free_in_c_2 := .const row.cColsLo.free_in_c_2
      free_in_c_3 := .const row.cColsLo.free_in_c_3
      free_in_c_4 := .const row.cColsLo.free_in_c_4
      free_in_c_5 := .const row.cColsLo.free_in_c_5
      free_in_c_6 := .const row.cColsLo.free_in_c_6
      free_in_c_7 := .const row.cColsLo.free_in_c_7 }
    cColsHi := {
      free_in_c_8 := .const row.cColsHi.free_in_c_8
      free_in_c_9 := .const row.cColsHi.free_in_c_9
      free_in_c_10 := .const row.cColsHi.free_in_c_10
      free_in_c_11 := .const row.cColsHi.free_in_c_11
      free_in_c_12 := .const row.cColsHi.free_in_c_12
      free_in_c_13 := .const row.cColsHi.free_in_c_13
      free_in_c_14 := .const row.cColsHi.free_in_c_14
      free_in_c_15 := .const row.cColsHi.free_in_c_15 }
    flags := {
      op := .const row.flags.op
      free_in_b := .const row.flags.free_in_b
      op_is_shift := .const row.flags.op_is_shift
      b_0 := .const row.flags.b_0
      b_1 := .const row.flags.b_1 } }

open ZiskFv.Airs.Tables.BinaryExtensionTable in
/-- Constant-row specialization of the lookup-aware BinaryExtensionTable
    channel path. The eight returned facts are sourced from
    `mainWithBinaryExtensionTable`'s channel pulls, not from
    `bin_ext_table_consumer_wf`. This is C7 groundwork: the theorem is local
    until the balanced BinaryExtensionTable provider side exists. -/
theorem binary_extension_table_wf_of_lookup_aware_const_soundness
    (offset : ℕ) (env : Environment FGL) (row : BinaryExtensionRow FGL)
    (h_holds :
      ConstraintsHold.Soundness env
        ((mainWithBinaryExtensionTable (constVar row)).operations offset)) :
    wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 0
        a_byte := row.aCols.free_in_a_0
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_0
        c_hi_byte := row.cColsLo.free_in_c_1
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 1
        a_byte := row.aCols.free_in_a_1
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_2
        c_hi_byte := row.cColsLo.free_in_c_3
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 2
        a_byte := row.aCols.free_in_a_2
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_4
        c_hi_byte := row.cColsLo.free_in_c_5
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 3
        a_byte := row.aCols.free_in_a_3
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_6
        c_hi_byte := row.cColsLo.free_in_c_7
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 4
        a_byte := row.aCols.free_in_a_4
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_8
        c_hi_byte := row.cColsHi.free_in_c_9
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 5
        a_byte := row.aCols.free_in_a_5
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_10
        c_hi_byte := row.cColsHi.free_in_c_11
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 6
        a_byte := row.aCols.free_in_a_6
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_12
        c_hi_byte := row.cColsHi.free_in_c_13
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 7
        a_byte := row.aCols.free_in_a_7
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_14
        c_hi_byte := row.cColsHi.free_in_c_15
        op_is_shift := row.flags.op_is_shift } 1) := by
  simp only [mainWithBinaryExtensionTable, main, circuit_norm] at h_holds
  rcases h_holds with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨ by simpa [BinaryExtensionTableChannel,
                    BinaryExtensionTableMessage.toEntry] using h0
        , by simpa [BinaryExtensionTableChannel,
                    BinaryExtensionTableMessage.toEntry] using h1
        , by simpa [BinaryExtensionTableChannel,
                    BinaryExtensionTableMessage.toEntry] using h2
        , by simpa [BinaryExtensionTableChannel,
                    BinaryExtensionTableMessage.toEntry] using h3
        , by simpa [BinaryExtensionTableChannel,
                    BinaryExtensionTableMessage.toEntry] using h4
        , by simpa [BinaryExtensionTableChannel,
                    BinaryExtensionTableMessage.toEntry] using h5
        , by simpa [BinaryExtensionTableChannel,
                    BinaryExtensionTableMessage.toEntry] using h6
        , by simpa [BinaryExtensionTableChannel,
                    BinaryExtensionTableMessage.toEntry] using h7 ⟩

/-- Constant-row specialization of the static-provider
    BinaryExtensionTable lookup path. The eight returned facts are exact
    decoded-row memberships in
    `AirsClean.BinaryExtensionTable.binaryExtensionTable`, sourced from
    `mainWithStaticBinaryExtensionTable`'s Clean
    `lookup (Table.fromStatic ...)` operations.

    This proves provider-side table membership only. Semantic
    `wf_properties` projection and load-bearing opcode rewiring remain C7
    work. -/
theorem binary_extension_table_specs_of_static_lookup_const_soundness
    (offset : ℕ) (env : Environment FGL) (row : BinaryExtensionRow FGL)
    (h_holds :
      ConstraintsHold.Soundness env
        ((mainWithStaticBinaryExtensionTable (constVar row)).operations offset)) :
    ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
      { op := row.flags.op
        byte_index := 0
        a_byte := row.aCols.free_in_a_0
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_0
        c_hi_byte := row.cColsLo.free_in_c_1
        op_is_shift := row.flags.op_is_shift }
  ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
      { op := row.flags.op
        byte_index := 1
        a_byte := row.aCols.free_in_a_1
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_2
        c_hi_byte := row.cColsLo.free_in_c_3
        op_is_shift := row.flags.op_is_shift }
  ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
      { op := row.flags.op
        byte_index := 2
        a_byte := row.aCols.free_in_a_2
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_4
        c_hi_byte := row.cColsLo.free_in_c_5
        op_is_shift := row.flags.op_is_shift }
  ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
      { op := row.flags.op
        byte_index := 3
        a_byte := row.aCols.free_in_a_3
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_6
        c_hi_byte := row.cColsLo.free_in_c_7
        op_is_shift := row.flags.op_is_shift }
  ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
      { op := row.flags.op
        byte_index := 4
        a_byte := row.aCols.free_in_a_4
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_8
        c_hi_byte := row.cColsHi.free_in_c_9
        op_is_shift := row.flags.op_is_shift }
  ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
      { op := row.flags.op
        byte_index := 5
        a_byte := row.aCols.free_in_a_5
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_10
        c_hi_byte := row.cColsHi.free_in_c_11
        op_is_shift := row.flags.op_is_shift }
  ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
      { op := row.flags.op
        byte_index := 6
        a_byte := row.aCols.free_in_a_6
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_12
        c_hi_byte := row.cColsHi.free_in_c_13
        op_is_shift := row.flags.op_is_shift }
  ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
      { op := row.flags.op
        byte_index := 7
        a_byte := row.aCols.free_in_a_7
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_14
        c_hi_byte := row.cColsHi.free_in_c_15
        op_is_shift := row.flags.op_is_shift } := by
  simp only [mainWithStaticBinaryExtensionTable, main, circuit_norm] at h_holds
  rcases h_holds with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
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
                    Table.toRaw] using h7 ⟩

open ZiskFv.Airs.Tables.BinaryExtensionTable in
/-- The eight legacy `BinaryExtensionTable.wf_properties` facts for the exact
    rows emitted by BinaryExtension's static-table lookup path. This is the
    shared C7 target shape for replacing direct uses of
    `bin_ext_table_consumer_wf`. -/
abbrev StaticBinaryExtensionTableWfFacts (row : BinaryExtensionRow FGL) : Prop :=
    wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 0
        a_byte := row.aCols.free_in_a_0
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_0
        c_hi_byte := row.cColsLo.free_in_c_1
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 1
        a_byte := row.aCols.free_in_a_1
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_2
        c_hi_byte := row.cColsLo.free_in_c_3
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 2
        a_byte := row.aCols.free_in_a_2
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_4
        c_hi_byte := row.cColsLo.free_in_c_5
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 3
        a_byte := row.aCols.free_in_a_3
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsLo.free_in_c_6
        c_hi_byte := row.cColsLo.free_in_c_7
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 4
        a_byte := row.aCols.free_in_a_4
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_8
        c_hi_byte := row.cColsHi.free_in_c_9
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 5
        a_byte := row.aCols.free_in_a_5
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_10
        c_hi_byte := row.cColsHi.free_in_c_11
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 6
        a_byte := row.aCols.free_in_a_6
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_12
        c_hi_byte := row.cColsHi.free_in_c_13
        op_is_shift := row.flags.op_is_shift } 1)
  ∧ wf_properties (BinaryExtensionTableMessage.toEntry
      { op := row.flags.op
        byte_index := 7
        a_byte := row.aCols.free_in_a_7
        shift_amount := row.flags.free_in_b
        c_lo_byte := row.cColsHi.free_in_c_14
        c_hi_byte := row.cColsHi.free_in_c_15
        op_is_shift := row.flags.op_is_shift } 1)

abbrev ShiftB0RangeSpecFact (row : BinaryExtensionRow FGL) : Prop :=
  row.flags.b_0.val < 2 ^ 24

open ZiskFv.Airs.Tables.BinaryExtensionTable in
/-- Static-provider BinaryExtensionTable lookup path, projected all the way to
    the legacy semantic `wf_properties` facts. This consumes exact membership
    in `AirsClean.BinaryExtensionTable.binaryExtensionTable` plus the proved
    membership-to-semantics projections, not `bin_ext_table_consumer_wf`. -/
theorem binary_extension_table_wf_of_static_lookup_const_soundness
    (offset : ℕ) (env : Environment FGL) (row : BinaryExtensionRow FGL)
    (h_holds :
      ConstraintsHold.Soundness env
        ((mainWithStaticBinaryExtensionTable (constVar row)).operations offset)) :
    StaticBinaryExtensionTableWfFacts row := by
  have h_specs :=
    binary_extension_table_specs_of_static_lookup_const_soundness offset env row h_holds
  rcases h_specs with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨ ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h0
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h1
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h2
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h3
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h4
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h5
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h6
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h7 ⟩

/-- BinaryExtension has zero F-typed per-row constraints. -/
def constraints_at
    (_v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (_r : ℕ) :
    Prop := True

/-- Shared C7 witness surface for BinaryExtension's static-table lookup path.
    This remains a family-level row-indexed predicate until the terminal
    Binary-family ensemble wires the static provider into the same Clean path. -/
def StaticLookupSoundness
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) : Prop :=
  ∀ (r offset : ℕ) (env : Environment FGL),
    ConstraintsHold.Soundness env
      ((mainWithStaticBinaryExtensionTable (constVar (rowAt v r))).operations offset)

/-- Project the shared C7 BinaryExtension static-lookup witness to the legacy
    per-byte semantic facts for row `r`. -/
theorem static_lookup_wf_facts
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r offset : ℕ) (env : Environment FGL) (h_static : StaticLookupSoundness v) :
    StaticBinaryExtensionTableWfFacts (rowAt v r) :=
  binary_extension_table_wf_of_static_lookup_const_soundness offset env (rowAt v r)
    (h_static r offset env)

/-!
## Operation-bus bridge

The Clean component emits an `OpBusMessage`; the pre-Clean equivalence layer
still consumes `OperationBusEntry`. These definitions and theorems are the
provider-side bridge C7 will use when replacing the consolidated
operation-bus permutation axiom with Clean channel balancing.
-/

@[reducible]
def aLoValue (row : BinaryExtensionRow FGL) : FGL :=
  row.aCols.free_in_a_0 + 256 * row.aCols.free_in_a_1
    + 65536 * row.aCols.free_in_a_2 + 16777216 * row.aCols.free_in_a_3

@[reducible]
def aHiValue (row : BinaryExtensionRow FGL) : FGL :=
  row.aCols.free_in_a_4 + 256 * row.aCols.free_in_a_5
    + 65536 * row.aCols.free_in_a_6 + 16777216 * row.aCols.free_in_a_7

@[reducible]
def opBusMessage (row : BinaryExtensionRow FGL) : OpBusMessage FGL :=
  { op := row.flags.op
    a_lo := row.flags.op_is_shift * (aLoValue row - row.flags.b_0) + row.flags.b_0
    a_hi := row.flags.op_is_shift * (aHiValue row - row.flags.b_1) + row.flags.b_1
    b_lo :=
      row.flags.op_is_shift * (row.flags.free_in_b + 256 * row.flags.b_0 - aLoValue row)
        + aLoValue row
    b_hi := row.flags.op_is_shift * (row.flags.b_1 - aHiValue row) + aHiValue row
    c_lo :=
      row.cColsLo.free_in_c_0 + row.cColsLo.free_in_c_2
        + row.cColsLo.free_in_c_4 + row.cColsLo.free_in_c_6
        + row.cColsHi.free_in_c_8 + row.cColsHi.free_in_c_10
        + row.cColsHi.free_in_c_12 + row.cColsHi.free_in_c_14
    c_hi :=
      row.cColsLo.free_in_c_1 + row.cColsLo.free_in_c_3
        + row.cColsLo.free_in_c_5 + row.cColsLo.free_in_c_7
        + row.cColsHi.free_in_c_9 + row.cColsHi.free_in_c_11
        + row.cColsHi.free_in_c_13 + row.cColsHi.free_in_c_15
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

theorem opBusMessage_toEntry_rowAt_eq_opBus_row
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (r : ℕ) :
    OpBusMessage.toEntry (opBusMessage (rowAt v r)) 1 =
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r := by
  rfl

theorem spec_of_valid
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (r : ℕ)
    (_h_assumptions : Assumptions (rowAt v r))
    (_h_constraints : constraints_at v r) :
    Spec (rowAt v r) :=
  spec_via_component (rowAt v r)

end ZiskFv.AirsClean.BinaryExtension
