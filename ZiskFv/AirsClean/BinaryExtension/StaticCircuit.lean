import ZiskFv.AirsClean.BinaryExtension.Bridge
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Lookup-aware BinaryExtension Clean component

Static-table variant of the BinaryExtension component. The plain
`BinaryExtension.component` exposes only the operation-bus provider row because
the AIR has no F-only local assertions. This component uses
`mainWithStaticBinaryExtensionTable`, so its `Spec` records the eight decoded
BinaryExtensionTable memberships for the same row that provides the op-bus
message.

## Trust note

No axioms. Completeness is a constructibility claim for rows equal to
`binaryExtensionStaticRowOf ...`: the eight per-byte lookup tuples are built
from explicit BinaryExtensionTable indices, shared opcode/shift slots are
related by semantic table-entry consistency facts, and `b_0`/`b_1` remain free
row operands. `shiftStaticLookupCircuit` additionally requires the explicit
`b_0.val < 2^24` side condition demanded by its range lookup. These claims do
not say that arbitrary input rows are honest BinaryExtension executions.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.BinaryExtensionTable (BinaryExtensionTableMessage)

abbrev BinaryExtensionTableIndex :=
  Fin ZiskFv.AirsClean.BinaryExtensionTable.tableSize

@[reducible]
def binaryExtensionTableRow
    (i : BinaryExtensionTableIndex) : BinaryExtensionTableMessage FGL :=
  ZiskFv.AirsClean.BinaryExtensionTable.rowOfIndex i.val

lemma binaryExtensionTableMessage_eq_of_shared
    (t : BinaryExtensionTableMessage FGL)
    (op byteIndex shiftAmount opIsShift : FGL)
    (h_op : t.op = op) (h_byte : t.byte_index = byteIndex)
    (h_shift : t.shift_amount = shiftAmount)
    (h_opShift : t.op_is_shift = opIsShift) :
    { op := op
      byte_index := byteIndex
      a_byte := t.a_byte
      shift_amount := shiftAmount
      c_lo_byte := t.c_lo_byte
      c_hi_byte := t.c_hi_byte
      op_is_shift := opIsShift } = t := by
  cases t
  simp at h_op h_byte h_shift h_opShift ⊢
  subst_vars
  simp

/-- Honest BinaryExtension static-lookup row built from eight table indices.
    Unique byte/result columns are copied from their table rows. The shared
    opcode, shift amount, and shift flag use row 0, with consistency facts in
    the circuit `ProverAssumptions` tying rows 1-7 back to it. -/
def binaryExtensionStaticRowOf
    (i0 i1 i2 i3 i4 i5 i6 i7 : BinaryExtensionTableIndex)
    (b0 b1 : FGL) : BinaryExtensionRow FGL :=
  let t0 := binaryExtensionTableRow i0
  let t1 := binaryExtensionTableRow i1
  let t2 := binaryExtensionTableRow i2
  let t3 := binaryExtensionTableRow i3
  let t4 := binaryExtensionTableRow i4
  let t5 := binaryExtensionTableRow i5
  let t6 := binaryExtensionTableRow i6
  let t7 := binaryExtensionTableRow i7
  { aCols :=
      { free_in_a_0 := t0.a_byte
        free_in_a_1 := t1.a_byte
        free_in_a_2 := t2.a_byte
        free_in_a_3 := t3.a_byte
        free_in_a_4 := t4.a_byte
        free_in_a_5 := t5.a_byte
        free_in_a_6 := t6.a_byte
        free_in_a_7 := t7.a_byte }
    cColsLo :=
      { free_in_c_0 := t0.c_lo_byte
        free_in_c_1 := t0.c_hi_byte
        free_in_c_2 := t1.c_lo_byte
        free_in_c_3 := t1.c_hi_byte
        free_in_c_4 := t2.c_lo_byte
        free_in_c_5 := t2.c_hi_byte
        free_in_c_6 := t3.c_lo_byte
        free_in_c_7 := t3.c_hi_byte }
    cColsHi :=
      { free_in_c_8 := t4.c_lo_byte
        free_in_c_9 := t4.c_hi_byte
        free_in_c_10 := t5.c_lo_byte
        free_in_c_11 := t5.c_hi_byte
        free_in_c_12 := t6.c_lo_byte
        free_in_c_13 := t6.c_hi_byte
        free_in_c_14 := t7.c_lo_byte
        free_in_c_15 := t7.c_hi_byte }
    flags :=
      { op := t0.op
        free_in_b := t0.shift_amount
        op_is_shift := t0.op_is_shift
        b_0 := b0
        b_1 := b1 } }

abbrev StaticBinaryExtensionTableSpecFacts
    (row : BinaryExtensionRow FGL) : Prop :=
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
          op_is_shift := row.flags.op_is_shift }

def staticLookupCircuit : GeneralFormalCircuit FGL BinaryExtensionRow unit :=
  { binaryExtensionWithStaticTableElaborated with
    exposedChannels row _ :=
      expose OpBusChannel [OpBusChannel.pushed (opBusMessageExpr row)]
    channelsLawful := by
      simp only [circuit_norm, mainWithStaticBinaryExtensionTable, main,
        opBusMessageExpr, aLo, aHi, OpBusChannel]
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row ∧ StaticBinaryExtensionTableSpecFacts row
    -- Completeness covers index-route rows: lookup tuple columns are copied
    -- from BinaryExtensionTable indices, and shared slots are tied by
    -- semantic consistency facts between those table entries.
    ProverAssumptions := fun row _ _ =>
      ∃ i0 i1 i2 i3 i4 i5 i6 i7 b0 b1,
        (binaryExtensionTableRow i0).byte_index = 0 ∧
        (binaryExtensionTableRow i1).byte_index = 1 ∧
        (binaryExtensionTableRow i1).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i1).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i1).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i2).byte_index = 2 ∧
        (binaryExtensionTableRow i2).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i2).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i2).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i3).byte_index = 3 ∧
        (binaryExtensionTableRow i3).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i3).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i3).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i4).byte_index = 4 ∧
        (binaryExtensionTableRow i4).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i4).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i4).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i5).byte_index = 5 ∧
        (binaryExtensionTableRow i5).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i5).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i5).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i6).byte_index = 6 ∧
        (binaryExtensionTableRow i6).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i6).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i6).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i7).byte_index = 7 ∧
        (binaryExtensionTableRow i7).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i7).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i7).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        row = binaryExtensionStaticRowOf i0 i1 i2 i3 i4 i5 i6 i7 b0 b1
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h_holds
        exact ⟨
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h0,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h1,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h2,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h3,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h4,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h5,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h6,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h7 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel, Lookup.completeness_def]
      obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, b0, b1,
        h0_byte,
        h1_byte, h1_op, h1_shift, h1_opShift,
        h2_byte, h2_op, h2_shift, h2_opShift,
        h3_byte, h3_op, h3_shift, h3_opShift,
        h4_byte, h4_op, h4_shift, h4_opShift,
        h5_byte, h5_op, h5_shift, h5_opShift,
        h6_byte, h6_op, h6_shift, h6_opShift,
        h7_byte, h7_op, h7_shift, h7_opShift, hrow⟩ := h_assumptions
      injection hrow with h_aCols h_cColsLo h_cColsHi h_flags
      injection h_aCols with h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
      injection h_cColsLo with h_c0 h_c1 h_c2 h_c3 h_c4 h_c5 h_c6 h_c7
      injection h_cColsHi with h_c8 h_c9 h_c10 h_c11 h_c12 h_c13 h_c14 h_c15
      injection h_flags with h_op h_freeInB h_opIsShift h_b0 h_b1
      subst_vars
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨i0, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 0
              a_byte := (binaryExtensionTableRow i0).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i0).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i0).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i0
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i0)
            (binaryExtensionTableRow i0).op 0 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift rfl h0_byte rfl rfl⟩
      · exact ⟨i1, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 1
              a_byte := (binaryExtensionTableRow i1).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i1).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i1).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i1
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i1)
            (binaryExtensionTableRow i0).op 1 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h1_op h1_byte h1_shift h1_opShift⟩
      · exact ⟨i2, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 2
              a_byte := (binaryExtensionTableRow i2).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i2).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i2).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i2
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i2)
            (binaryExtensionTableRow i0).op 2 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h2_op h2_byte h2_shift h2_opShift⟩
      · exact ⟨i3, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 3
              a_byte := (binaryExtensionTableRow i3).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i3).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i3).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i3
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i3)
            (binaryExtensionTableRow i0).op 3 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h3_op h3_byte h3_shift h3_opShift⟩
      · exact ⟨i4, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 4
              a_byte := (binaryExtensionTableRow i4).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i4).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i4).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i4
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i4)
            (binaryExtensionTableRow i0).op 4 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h4_op h4_byte h4_shift h4_opShift⟩
      · exact ⟨i5, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 5
              a_byte := (binaryExtensionTableRow i5).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i5).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i5).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i5
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i5)
            (binaryExtensionTableRow i0).op 5 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h5_op h5_byte h5_shift h5_opShift⟩
      · exact ⟨i6, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 6
              a_byte := (binaryExtensionTableRow i6).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i6).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i6).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i6
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i6)
            (binaryExtensionTableRow i0).op 6 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h6_op h6_byte h6_shift h6_opShift⟩
      · exact ⟨i7, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 7
              a_byte := (binaryExtensionTableRow i7).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i7).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i7).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i7
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i7)
            (binaryExtensionTableRow i0).op 7 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h7_op h7_byte h7_shift h7_opShift⟩ }

def shiftStaticLookupCircuit : GeneralFormalCircuit FGL BinaryExtensionRow unit :=
  { binaryExtensionWithStaticTableAndShiftRangeElaborated with
    exposedChannels row _ :=
      expose OpBusChannel [OpBusChannel.pushed (opBusMessageExpr row)]
    channelsLawful := by
      simp only [circuit_norm, mainWithStaticBinaryExtensionTableAndShiftRange,
        mainWithStaticBinaryExtensionTable, main, opBusMessageExpr, aLo, aHi,
        OpBusChannel]
    Assumptions := fun _ _ => True
    Spec := fun row _ _ =>
      Spec row ∧ StaticBinaryExtensionTableSpecFacts row ∧ ShiftB0RangeSpecFact row
    -- Completeness covers the same index-route rows as `staticLookupCircuit`,
    -- with an additional semantic range fact for the selected shift operand.
    ProverAssumptions := fun row _ _ =>
      ∃ i0 i1 i2 i3 i4 i5 i6 i7 b0 b1,
        (binaryExtensionTableRow i0).byte_index = 0 ∧
        (binaryExtensionTableRow i1).byte_index = 1 ∧
        (binaryExtensionTableRow i1).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i1).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i1).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i2).byte_index = 2 ∧
        (binaryExtensionTableRow i2).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i2).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i2).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i3).byte_index = 3 ∧
        (binaryExtensionTableRow i3).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i3).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i3).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i4).byte_index = 4 ∧
        (binaryExtensionTableRow i4).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i4).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i4).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i5).byte_index = 5 ∧
        (binaryExtensionTableRow i5).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i5).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i5).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i6).byte_index = 6 ∧
        (binaryExtensionTableRow i6).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i6).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i6).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        (binaryExtensionTableRow i7).byte_index = 7 ∧
        (binaryExtensionTableRow i7).op = (binaryExtensionTableRow i0).op ∧
        (binaryExtensionTableRow i7).shift_amount =
          (binaryExtensionTableRow i0).shift_amount ∧
        (binaryExtensionTableRow i7).op_is_shift =
          (binaryExtensionTableRow i0).op_is_shift ∧
        b0.val < 2 ^ 24 ∧
        row = binaryExtensionStaticRowOf i0 i1 i2 i3 i4 i5 i6 i7 b0 b1
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h_b0⟩ := h_holds
        exact ⟨
          ⟨ by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h0,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h1,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h2,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h3,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h4,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h5,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h6,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h7 ⟩,
          by simpa [ShiftB0RangeSpecFact] using h_b0 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel, Lookup.completeness_def]
      obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, b0, b1,
        h0_byte,
        h1_byte, h1_op, h1_shift, h1_opShift,
        h2_byte, h2_op, h2_shift, h2_opShift,
        h3_byte, h3_op, h3_shift, h3_opShift,
        h4_byte, h4_op, h4_shift, h4_opShift,
        h5_byte, h5_op, h5_shift, h5_opShift,
        h6_byte, h6_op, h6_shift, h6_opShift,
        h7_byte, h7_op, h7_shift, h7_opShift, h_b0Range, hrow⟩ := h_assumptions
      injection hrow with h_aCols h_cColsLo h_cColsHi h_flags
      injection h_aCols with h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
      injection h_cColsLo with h_c0 h_c1 h_c2 h_c3 h_c4 h_c5 h_c6 h_c7
      injection h_cColsHi with h_c8 h_c9 h_c10 h_c11 h_c12 h_c13 h_c14 h_c15
      injection h_flags with h_op h_freeInB h_opIsShift h_b0 h_b1
      subst_vars
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨i0, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 0
              a_byte := (binaryExtensionTableRow i0).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i0).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i0).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i0
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i0)
            (binaryExtensionTableRow i0).op 0 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift rfl h0_byte rfl rfl⟩
      · exact ⟨i1, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 1
              a_byte := (binaryExtensionTableRow i1).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i1).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i1).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i1
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i1)
            (binaryExtensionTableRow i0).op 1 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h1_op h1_byte h1_shift h1_opShift⟩
      · exact ⟨i2, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 2
              a_byte := (binaryExtensionTableRow i2).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i2).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i2).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i2
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i2)
            (binaryExtensionTableRow i0).op 2 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h2_op h2_byte h2_shift h2_opShift⟩
      · exact ⟨i3, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 3
              a_byte := (binaryExtensionTableRow i3).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i3).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i3).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i3
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i3)
            (binaryExtensionTableRow i0).op 3 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h3_op h3_byte h3_shift h3_opShift⟩
      · exact ⟨i4, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 4
              a_byte := (binaryExtensionTableRow i4).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i4).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i4).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i4
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i4)
            (binaryExtensionTableRow i0).op 4 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h4_op h4_byte h4_shift h4_opShift⟩
      · exact ⟨i5, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 5
              a_byte := (binaryExtensionTableRow i5).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i5).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i5).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i5
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i5)
            (binaryExtensionTableRow i0).op 5 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h5_op h5_byte h5_shift h5_opShift⟩
      · exact ⟨i6, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 6
              a_byte := (binaryExtensionTableRow i6).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i6).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i6).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i6
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i6)
            (binaryExtensionTableRow i0).op 6 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h6_op h6_byte h6_shift h6_opShift⟩
      · exact ⟨i7, by
          change
            { op := (binaryExtensionTableRow i0).op
              byte_index := 7
              a_byte := (binaryExtensionTableRow i7).a_byte
              shift_amount := (binaryExtensionTableRow i0).shift_amount
              c_lo_byte := (binaryExtensionTableRow i7).c_lo_byte
              c_hi_byte := (binaryExtensionTableRow i7).c_hi_byte
              op_is_shift := (binaryExtensionTableRow i0).op_is_shift } =
              binaryExtensionTableRow i7
          exact binaryExtensionTableMessage_eq_of_shared (binaryExtensionTableRow i7)
            (binaryExtensionTableRow i0).op 7 (binaryExtensionTableRow i0).shift_amount
            (binaryExtensionTableRow i0).op_is_shift h7_op h7_byte h7_shift h7_opShift⟩
      · exact h_b0Range }

def staticLookupComponent : Air.Flat.Component FGL := ⟨ staticLookupCircuit ⟩

def shiftStaticLookupComponent : Air.Flat.Component FGL := ⟨ shiftStaticLookupCircuit ⟩

theorem staticLookupComponent_interactionsWith_opBus :
    staticLookupComponent.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (opBusMessageExpr staticLookupComponent.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed (opBusMessageExpr staticLookupComponent.rowInputVar)).toRaw)]⟩ ∈
    staticLookupComponent.exposedChannels
  simp only [staticLookupComponent, staticLookupCircuit,
    binaryExtensionWithStaticTableElaborated, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil]

theorem shiftStaticLookupComponent_interactionsWith_opBus :
    shiftStaticLookupComponent.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (opBusMessageExpr shiftStaticLookupComponent.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed
        (opBusMessageExpr shiftStaticLookupComponent.rowInputVar)).toRaw)]⟩ ∈
    shiftStaticLookupComponent.exposedChannels
  simp only [shiftStaticLookupComponent, shiftStaticLookupCircuit,
    binaryExtensionWithStaticTableAndShiftRangeElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil]

theorem staticLookupComponent_spec
    (env : Environment FGL) :
    staticLookupComponent.Spec env =
      (Spec (staticLookupComponent.rowInput env)
        ∧ StaticBinaryExtensionTableSpecFacts
          (staticLookupComponent.rowInput env)) := by
  rfl

theorem shiftStaticLookupComponent_spec
    (env : Environment FGL) :
    shiftStaticLookupComponent.Spec env =
      (Spec (shiftStaticLookupComponent.rowInput env)
        ∧ StaticBinaryExtensionTableSpecFacts
          (shiftStaticLookupComponent.rowInput env)
        ∧ ShiftB0RangeSpecFact
          (shiftStaticLookupComponent.rowInput env)) := by
  rfl

theorem static_table_wf_facts_of_spec_facts
    (row : BinaryExtensionRow FGL)
    (h_specs : StaticBinaryExtensionTableSpecFacts row) :
    StaticBinaryExtensionTableWfFacts row := by
  rcases h_specs with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨ ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h0
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h1
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h2
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h3
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h4
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h5
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h6
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h7 ⟩

theorem static_table_op_val_ne_bitwise_of_spec_facts
    (row : BinaryExtensionRow FGL)
    (h_specs : StaticBinaryExtensionTableSpecFacts row) :
    row.flags.op.val ≠ 14 ∧ row.flags.op.val ≠ 15 ∧ row.flags.op.val ≠ 16 := by
  exact ZiskFv.AirsClean.BinaryExtensionTable.spec_op_val_ne_bitwise h_specs.1

theorem static_table_op_val_ne_compare_of_spec_facts
    (row : BinaryExtensionRow FGL)
    (h_specs : StaticBinaryExtensionTableSpecFacts row) :
    row.flags.op.val ≠ 6 ∧ row.flags.op.val ≠ 7 := by
  exact ZiskFv.AirsClean.BinaryExtensionTable.spec_op_val_ne_compare h_specs.1

theorem static_table_op_val_ne_W_add_sub_of_spec_facts
    (row : BinaryExtensionRow FGL)
    (h_specs : StaticBinaryExtensionTableSpecFacts row) :
    row.flags.op.val ≠ 0x1A ∧ row.flags.op.val ≠ 0x1B := by
  exact ZiskFv.AirsClean.BinaryExtensionTable.spec_op_val_ne_W_add_sub h_specs.1

/-- A row accepted by the lookup-aware BinaryExtension component cannot carry
    Binary-table bitwise opcodes (`AND`/`OR`/`XOR`, values 14/15/16). -/
theorem staticLookupComponent_op_val_ne_bitwise_of_spec
    (env : Environment FGL)
    (h_spec : staticLookupComponent.Spec env) :
    (staticLookupComponent.rowInput env).flags.op.val ≠ 14
      ∧ (staticLookupComponent.rowInput env).flags.op.val ≠ 15
      ∧ (staticLookupComponent.rowInput env).flags.op.val ≠ 16 := by
  rw [staticLookupComponent_spec] at h_spec
  exact static_table_op_val_ne_bitwise_of_spec_facts
    (staticLookupComponent.rowInput env) h_spec.2

/-- A row accepted by the lookup-aware BinaryExtension component cannot carry
    Binary-table comparison opcodes (`LTU`/`LT`, values 6/7). -/
theorem staticLookupComponent_op_val_ne_compare_of_spec
    (env : Environment FGL)
    (h_spec : staticLookupComponent.Spec env) :
    (staticLookupComponent.rowInput env).flags.op.val ≠ 6
      ∧ (staticLookupComponent.rowInput env).flags.op.val ≠ 7 := by
  rw [staticLookupComponent_spec] at h_spec
  exact static_table_op_val_ne_compare_of_spec_facts
    (staticLookupComponent.rowInput env) h_spec.2

/-- A row accepted by the lookup-aware BinaryExtension component cannot carry
    Main W-mode ADD/SUB opcodes (`ADDW`/`SUBW`, values 0x1A/0x1B). -/
theorem staticLookupComponent_op_val_ne_W_add_sub_of_spec
    (env : Environment FGL)
    (h_spec : staticLookupComponent.Spec env) :
    (staticLookupComponent.rowInput env).flags.op.val ≠ 0x1A
      ∧ (staticLookupComponent.rowInput env).flags.op.val ≠ 0x1B := by
  rw [staticLookupComponent_spec] at h_spec
  exact static_table_op_val_ne_W_add_sub_of_spec_facts
    (staticLookupComponent.rowInput env) h_spec.2

/-- A row accepted by the shift-aware lookup BinaryExtension component cannot
    carry Binary-table bitwise opcodes (`AND`/`OR`/`XOR`, values 14/15/16). -/
theorem shiftStaticLookupComponent_op_val_ne_bitwise_of_spec
    (env : Environment FGL)
    (h_spec : shiftStaticLookupComponent.Spec env) :
    (shiftStaticLookupComponent.rowInput env).flags.op.val ≠ 14
      ∧ (shiftStaticLookupComponent.rowInput env).flags.op.val ≠ 15
      ∧ (shiftStaticLookupComponent.rowInput env).flags.op.val ≠ 16 := by
  rw [shiftStaticLookupComponent_spec] at h_spec
  exact static_table_op_val_ne_bitwise_of_spec_facts
    (shiftStaticLookupComponent.rowInput env) h_spec.2.1

/-- A row accepted by the shift-aware lookup BinaryExtension component cannot
    carry Binary-table comparison opcodes (`LTU`/`LT`, values 6/7). -/
theorem shiftStaticLookupComponent_op_val_ne_compare_of_spec
    (env : Environment FGL)
    (h_spec : shiftStaticLookupComponent.Spec env) :
    (shiftStaticLookupComponent.rowInput env).flags.op.val ≠ 6
      ∧ (shiftStaticLookupComponent.rowInput env).flags.op.val ≠ 7 := by
  rw [shiftStaticLookupComponent_spec] at h_spec
  exact static_table_op_val_ne_compare_of_spec_facts
    (shiftStaticLookupComponent.rowInput env) h_spec.2.1

/-- A row accepted by the shift-aware lookup BinaryExtension component cannot
    carry Main W-mode ADD/SUB opcodes (`ADDW`/`SUBW`, values 0x1A/0x1B). -/
theorem shiftStaticLookupComponent_op_val_ne_W_add_sub_of_spec
    (env : Environment FGL)
    (h_spec : shiftStaticLookupComponent.Spec env) :
    (shiftStaticLookupComponent.rowInput env).flags.op.val ≠ 0x1A
      ∧ (shiftStaticLookupComponent.rowInput env).flags.op.val ≠ 0x1B := by
  rw [shiftStaticLookupComponent_spec] at h_spec
  exact static_table_op_val_ne_W_add_sub_of_spec_facts
    (shiftStaticLookupComponent.rowInput env) h_spec.2.1

theorem aCols_eval_eq
    (env : Environment FGL) (cols : BinaryExtensionACols (Expression FGL)) :
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

theorem cColsLo_eval_eq
    (env : Environment FGL) (cols : BinaryExtensionCColsLo (Expression FGL)) :
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

theorem cColsHi_eval_eq
    (env : Environment FGL) (cols : BinaryExtensionCColsHi (Expression FGL)) :
    eval env cols =
      { free_in_c_8 := Expression.eval env cols.free_in_c_8
        free_in_c_9 := Expression.eval env cols.free_in_c_9
        free_in_c_10 := Expression.eval env cols.free_in_c_10
        free_in_c_11 := Expression.eval env cols.free_in_c_11
        free_in_c_12 := Expression.eval env cols.free_in_c_12
        free_in_c_13 := Expression.eval env cols.free_in_c_13
        free_in_c_14 := Expression.eval env cols.free_in_c_14
        free_in_c_15 := Expression.eval env cols.free_in_c_15 } := by
  rw [ProvableStruct.eval_eq_eval]
  cases cols
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]

theorem flags_eval_eq
    (env : Environment FGL) (flags : BinaryExtensionFlags (Expression FGL)) :
    eval env flags =
      { op := Expression.eval env flags.op
        free_in_b := Expression.eval env flags.free_in_b
        op_is_shift := Expression.eval env flags.op_is_shift
        b_0 := Expression.eval env flags.b_0
        b_1 := Expression.eval env flags.b_1 } := by
  rw [ProvableStruct.eval_eq_eval]
  cases flags
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]

theorem flags_eval_op
    (env : Environment FGL) (flags : BinaryExtensionFlags (Expression FGL)) :
    (eval env flags).op = Expression.eval env flags.op := by
  rw [flags_eval_eq]

theorem row_eval_flags_op
    (env : Environment FGL) (row : Var BinaryExtensionRow FGL) :
    (eval env row).flags.op = Expression.eval env row.flags.op := by
  rw [ProvableStruct.eval_eq_eval]
  cases row
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go]
  exact flags_eval_op env _

theorem eval_opBusMessageExpr
    (env : Environment FGL) (row : Var BinaryExtensionRow FGL) :
    eval env (opBusMessageExpr row) = opBusMessage (eval env row) := by
  cases row
  simp only [opBusMessageExpr, opBusMessage, aLo, aHi, aLoValue, aHiValue,
    ProvableStruct.eval_eq_eval]
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]
  simp [aCols_eval_eq, cColsLo_eval_eq, cColsHi_eval_eq, flags_eval_eq, Expression.eval,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- Evaluating the static BinaryExtension op-bus expression preserves the
    row's opcode slot. Kept local to avoid unfolding the full row expression
    in Binary-family balance proofs. -/
theorem staticLookupComponent_eval_opBusMessageExpr_op
    (env : Environment FGL) :
    (eval env (opBusMessageExpr staticLookupComponent.rowInputVar)).op =
      (staticLookupComponent.rowInput env).flags.op := by
  rw [ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
  change Expression.eval env staticLookupComponent.rowInputVar.flags.op =
    (staticLookupComponent.rowInput env).flags.op
  rw [← row_eval_flags_op env staticLookupComponent.rowInputVar]
  exact congrArg (fun row : BinaryExtensionRow FGL => row.flags.op)
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset staticLookupComponent.Input 0 env))

theorem shiftStaticLookupComponent_eval_opBusMessageExpr_op
    (env : Environment FGL) :
    (eval env (opBusMessageExpr shiftStaticLookupComponent.rowInputVar)).op =
      (shiftStaticLookupComponent.rowInput env).flags.op := by
  rw [ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
  change Expression.eval env shiftStaticLookupComponent.rowInputVar.flags.op =
    (shiftStaticLookupComponent.rowInput env).flags.op
  rw [← row_eval_flags_op env shiftStaticLookupComponent.rowInputVar]
  exact congrArg (fun row : BinaryExtensionRow FGL => row.flags.op)
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset shiftStaticLookupComponent.Input 0 env))

theorem shiftStaticLookupComponent_eval_opBusMessageExpr
    (env : Environment FGL) :
    eval env (opBusMessageExpr shiftStaticLookupComponent.rowInputVar) =
      opBusMessage (shiftStaticLookupComponent.rowInput env) := by
  rw [eval_opBusMessageExpr]
  exact congrArg opBusMessage
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset shiftStaticLookupComponent.Input 0 env))

end ZiskFv.AirsClean.BinaryExtension
