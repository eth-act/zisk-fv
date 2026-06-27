import ZiskFv.AirsClean.Binary.Constraints
import ZiskFv.AirsClean.Binary.Soundness
import ZiskFv.AirsClean.CompletenessHelpers
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Binary Clean Component (Phase C6)

Packages ZisK's Binary AIR as a Clean `Air.Flat.Component`.

The component covers the 7 F-typed constraints and the operation-bus push.
BinaryTable lookup semantics still flow through the existing table-soundness
boundary until the Binary-family terminal phase.

## Trust note

No axioms. Completeness for `circuit` is a constructibility claim for rows
equal to `binaryRowOf ...`: Boolean mode/flag columns are honest bits,
`b_op_or_sext` and `mode32_and_c_is_signed` are computed from them, and byte
and carry-chain columns outside these equations remain free. The static
lookup circuit strengthens this with explicit BinaryTable row indices and
semantic table-entry consistency facts; it does not claim arbitrary input rows
are honest Binary executions.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.BinaryTable (BinaryTableMessage)

/-- Computed `b_op_or_sext` column for Binary honest rows. -/
def binaryBOpOrSextOf (mode32 cIsSigned : Bool) (bOp : FGL) : FGL :=
  boolF mode32 * (boolF cIsSigned + 512 - bOp) + bOp

/-- Computed `mode32_and_c_is_signed` column for Binary honest rows. -/
def binaryMode32AndCIsSignedOf (mode32 cIsSigned : Bool) : FGL :=
  boolF mode32 * boolF cIsSigned

/-- Honest row for the Binary algebraic slice. Mode flags and final carry are
    Boolean operands; the two dependent columns are computed from them. -/
def binaryRowOf (mode32 resultIsA useFirstByte cIsSigned carry7 : Bool)
    (aBytes : BinaryAByteCols FGL) (bBytes : BinaryBByteCols FGL)
    (cBytes : BinaryCByteCols FGL)
    (carry0 carry1 carry2 carry3 carry4 carry5 carry6 bOp : FGL) :
    BinaryRow FGL :=
  { aBytes := aBytes
    bBytes := bBytes
    cBytes := cBytes
    chain :=
      { carry_0 := carry0
        carry_1 := carry1
        carry_2 := carry2
        carry_3 := carry3
        carry_4 := carry4
        carry_5 := carry5
        carry_6 := carry6
        carry_7 := boolF carry7
        b_op := bOp
        b_op_or_sext := binaryBOpOrSextOf mode32 cIsSigned bOp }
    mode :=
      { mode32 := boolF mode32
        result_is_a := boolF resultIsA
        use_first_byte := boolF useFirstByte
        c_is_signed := boolF cIsSigned
        mode32_and_c_is_signed := binaryMode32AndCIsSignedOf mode32 cIsSigned } }

def circuit : GeneralFormalCircuit FGL BinaryRow unit :=
  { binaryElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers rows built by `binaryRowOf`: Boolean columns are
    -- honest bits and dependent mux columns are computed by the builder.
    ProverAssumptions := fun row _ _ =>
      ∃ mode32 resultIsA useFirstByte cIsSigned carry7
        aBytes bBytes cBytes carry0 carry1 carry2 carry3 carry4 carry5 carry6 bOp,
        row = binaryRowOf mode32 resultIsA useFirstByte cIsSigned carry7
          aBytes bBytes cBytes carry0 carry1 carry2 carry3 carry4 carry5 carry6 bOp
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h_holds
        exact ⟨ by simpa [sub_eq_add_neg] using h0
              , by simpa [sub_eq_add_neg] using h1
              , by simpa [sub_eq_add_neg] using h2
              , by simpa [sub_eq_add_neg] using h3
              , by simpa [sub_eq_add_neg] using h4
              , by simpa [sub_eq_add_neg] using h5
              , by simpa [sub_eq_add_neg] using h6 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel]
      obtain ⟨mode32, resultIsA, useFirstByte, cIsSigned, carry7,
        aBytes, bBytes, cBytes, carry0, carry1, carry2, carry3, carry4,
        carry5, carry6, bOp, hrow⟩ := h_assumptions
      injection hrow with h_aBytes h_bBytes h_cBytes h_chain h_mode
      subst aBytes
      subst bBytes
      subst cBytes
      injection h_chain with h_carry0 h_carry1 h_carry2 h_carry3 h_carry4 h_carry5
        h_carry6 h_carry7 h_bOp h_bOpOrSext
      injection h_mode with h_mode32 h_resultIsA h_useFirstByte h_cIsSigned
        h_mode32AndCIsSigned
      subst_vars
      simp [binaryBOpOrSextOf, binaryMode32AndCIsSignedOf]
      ring_nf }

def component : Air.Flat.Component FGL := { circuit := circuit }

@[reducible]
def lookupFlags012Row (row : BinaryRow FGL) (carry : FGL) : FGL :=
  carry + 2 * row.mode.result_is_a + 4 * row.mode.use_first_byte

@[reducible]
def lookupFlags3456Row (row : BinaryRow FGL) (carry : FGL) : FGL :=
  carry + 2 * row.mode.result_is_a + 4 * row.mode.use_first_byte
    + 8 * row.mode.mode32_and_c_is_signed

@[reducible]
def lookupFlags7Row (row : BinaryRow FGL) : FGL :=
  row.chain.carry_7 + 2 * row.mode.result_is_a + 4 * row.mode.use_first_byte
    + 8 * row.mode.c_is_signed

@[reducible]
def lookupMessage0Row (row : BinaryRow FGL) : BinaryTableMessage FGL :=
  { pos_ind := 2 * row.mode.use_first_byte
    op := row.chain.b_op
    a_byte := row.aBytes.free_in_a_0
    b_byte := row.bBytes.free_in_b_0
    cin := 0
    c_byte := row.cBytes.free_in_c_0
    flags := lookupFlags012Row row row.chain.carry_0 }

@[reducible]
def lookupMessage1Row (row : BinaryRow FGL) : BinaryTableMessage FGL :=
  { pos_ind := 0
    op := row.chain.b_op
    a_byte := row.aBytes.free_in_a_1
    b_byte := row.bBytes.free_in_b_1
    cin := row.chain.carry_0
    c_byte := row.cBytes.free_in_c_1
    flags := lookupFlags012Row row row.chain.carry_1 }

@[reducible]
def lookupMessage2Row (row : BinaryRow FGL) : BinaryTableMessage FGL :=
  { pos_ind := 0
    op := row.chain.b_op
    a_byte := row.aBytes.free_in_a_2
    b_byte := row.bBytes.free_in_b_2
    cin := row.chain.carry_1
    c_byte := row.cBytes.free_in_c_2
    flags := lookupFlags012Row row row.chain.carry_2 }

@[reducible]
def lookupMessage3Row (row : BinaryRow FGL) : BinaryTableMessage FGL :=
  { pos_ind := row.mode.mode32
    op := row.chain.b_op
    a_byte := row.aBytes.free_in_a_3
    b_byte := row.bBytes.free_in_b_3
    cin := row.chain.carry_2
    c_byte := row.cBytes.free_in_c_3
    flags := lookupFlags3456Row row row.chain.carry_3 }

@[reducible]
def lookupMessage4Row (row : BinaryRow FGL) : BinaryTableMessage FGL :=
  { pos_ind := 0
    op := row.chain.b_op_or_sext
    a_byte := row.aBytes.free_in_a_4
    b_byte := row.bBytes.free_in_b_4
    cin := row.chain.carry_3
    c_byte := row.cBytes.free_in_c_4
    flags := lookupFlags3456Row row row.chain.carry_4 }

@[reducible]
def lookupMessage5Row (row : BinaryRow FGL) : BinaryTableMessage FGL :=
  { pos_ind := 0
    op := row.chain.b_op_or_sext
    a_byte := row.aBytes.free_in_a_5
    b_byte := row.bBytes.free_in_b_5
    cin := row.chain.carry_4
    c_byte := row.cBytes.free_in_c_5
    flags := lookupFlags3456Row row row.chain.carry_5 }

@[reducible]
def lookupMessage6Row (row : BinaryRow FGL) : BinaryTableMessage FGL :=
  { pos_ind := 0
    op := row.chain.b_op_or_sext
    a_byte := row.aBytes.free_in_a_6
    b_byte := row.bBytes.free_in_b_6
    cin := row.chain.carry_5
    c_byte := row.cBytes.free_in_c_6
    flags := lookupFlags3456Row row row.chain.carry_6 }

@[reducible]
def lookupMessage7Row (row : BinaryRow FGL) : BinaryTableMessage FGL :=
  { pos_ind := 1 - row.mode.mode32
    op := row.chain.b_op_or_sext
    a_byte := row.aBytes.free_in_a_7
    b_byte := row.bBytes.free_in_b_7
    cin := row.chain.carry_6
    c_byte := row.cBytes.free_in_c_7
    flags := lookupFlags7Row row }

abbrev BinaryTableIndex := Fin ZiskFv.AirsClean.BinaryTable.tableSize

@[reducible]
def binaryTableRow (i : BinaryTableIndex) : BinaryTableMessage FGL :=
  ZiskFv.AirsClean.BinaryTable.rowOfIndex i.val

lemma binaryTableMessage_eq_of_shared (t : BinaryTableMessage FGL)
    (pos op cin flags : FGL)
    (h_pos : t.pos_ind = pos) (h_op : t.op = op)
    (h_cin : t.cin = cin) (h_flags : t.flags = flags) :
    { pos_ind := pos
      op := op
      a_byte := t.a_byte
      b_byte := t.b_byte
      cin := cin
      c_byte := t.c_byte
      flags := flags } = t := by
  cases t
  simp at h_pos h_op h_cin h_flags ⊢
  subst_vars
  simp

/-- Honest Binary static-lookup row built from eight BinaryTable row indices.
    Unique byte columns are copied from their table rows; shared op/carry/mode
    data is represented by the Boolean operands plus semantic consistency facts
    in `staticLookupCircuit.ProverAssumptions`. -/
def binaryStaticRowOf (mode32 resultIsA useFirstByte cIsSigned carry7 : Bool)
    (i0 i1 i2 i3 i4 i5 i6 i7 : BinaryTableIndex) : BinaryRow FGL :=
  let t0 := binaryTableRow i0
  let t1 := binaryTableRow i1
  let t2 := binaryTableRow i2
  let t3 := binaryTableRow i3
  let t4 := binaryTableRow i4
  let t5 := binaryTableRow i5
  let t6 := binaryTableRow i6
  let t7 := binaryTableRow i7
  binaryRowOf mode32 resultIsA useFirstByte cIsSigned carry7
    { free_in_a_0 := t0.a_byte
      free_in_a_1 := t1.a_byte
      free_in_a_2 := t2.a_byte
      free_in_a_3 := t3.a_byte
      free_in_a_4 := t4.a_byte
      free_in_a_5 := t5.a_byte
      free_in_a_6 := t6.a_byte
      free_in_a_7 := t7.a_byte }
    { free_in_b_0 := t0.b_byte
      free_in_b_1 := t1.b_byte
      free_in_b_2 := t2.b_byte
      free_in_b_3 := t3.b_byte
      free_in_b_4 := t4.b_byte
      free_in_b_5 := t5.b_byte
      free_in_b_6 := t6.b_byte
      free_in_b_7 := t7.b_byte }
    { free_in_c_0 := t0.c_byte
      free_in_c_1 := t1.c_byte
      free_in_c_2 := t2.c_byte
      free_in_c_3 := t3.c_byte
      free_in_c_4 := t4.c_byte
      free_in_c_5 := t5.c_byte
      free_in_c_6 := t6.c_byte
      free_in_c_7 := t7.c_byte }
    t1.cin t2.cin t3.cin t4.cin t5.cin t6.cin t7.cin t0.op

abbrev StaticBinaryTableSpecFacts (row : BinaryRow FGL) : Prop :=
      ZiskFv.AirsClean.BinaryTable.binaryTable.Spec (lookupMessage0Row row)
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec (lookupMessage1Row row)
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec (lookupMessage2Row row)
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec (lookupMessage3Row row)
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec (lookupMessage4Row row)
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec (lookupMessage5Row row)
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec (lookupMessage6Row row)
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec (lookupMessage7Row row)

def staticLookupCircuit : GeneralFormalCircuit FGL BinaryRow unit :=
  { binaryWithStaticBinaryTableElaborated with
    exposedChannels row _ :=
      expose OpBusChannel [OpBusChannel.pushed (opBusMessageExpr row)]
    channelsLawful := by
      simp only [circuit_norm, mainWithStaticBinaryTable, main, opBusMessageExpr,
        OpBusChannel]
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row ∧ StaticBinaryTableSpecFacts row
    -- Completeness covers index-route rows: the eight lookup tuples are
    -- built from BinaryTable indices, with semantic consistency facts for
    -- shared mode/op/carry slots.
    ProverAssumptions := fun row _ _ =>
      ∃ mode32 resultIsA useFirstByte cIsSigned carry7
        i0 i1 i2 i3 i4 i5 i6 i7,
        (binaryTableRow i0).pos_ind = 2 * boolF useFirstByte ∧
        (binaryTableRow i0).cin = 0 ∧
        (binaryTableRow i0).flags =
          (binaryTableRow i1).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte ∧
        (binaryTableRow i1).pos_ind = 0 ∧
        (binaryTableRow i1).op = (binaryTableRow i0).op ∧
        (binaryTableRow i1).flags =
          (binaryTableRow i2).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte ∧
        (binaryTableRow i2).pos_ind = 0 ∧
        (binaryTableRow i2).op = (binaryTableRow i0).op ∧
        (binaryTableRow i2).flags =
          (binaryTableRow i3).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte ∧
        (binaryTableRow i3).pos_ind = boolF mode32 ∧
        (binaryTableRow i3).op = (binaryTableRow i0).op ∧
        (binaryTableRow i3).flags =
          (binaryTableRow i4).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte
            + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned ∧
        (binaryTableRow i4).pos_ind = 0 ∧
        (binaryTableRow i4).op =
          binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op ∧
        (binaryTableRow i4).flags =
          (binaryTableRow i5).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte
            + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned ∧
        (binaryTableRow i5).pos_ind = 0 ∧
        (binaryTableRow i5).op =
          binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op ∧
        (binaryTableRow i5).flags =
          (binaryTableRow i6).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte
            + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned ∧
        (binaryTableRow i6).pos_ind = 0 ∧
        (binaryTableRow i6).op =
          binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op ∧
        (binaryTableRow i6).flags =
          (binaryTableRow i7).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte
            + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned ∧
        (binaryTableRow i7).pos_ind = 1 - boolF mode32 ∧
        (binaryTableRow i7).op =
          binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op ∧
        (binaryTableRow i7).flags =
          boolF carry7 + 2 * boolF resultIsA + 4 * boolF useFirstByte
            + 8 * boolF cIsSigned ∧
        row = binaryStaticRowOf mode32 resultIsA useFirstByte cIsSigned carry7
          i0 i1 i2 i3 i4 i5 i6 i7
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
          h_holds
        exact ⟨ ⟨ by simpa [sub_eq_add_neg] using h0
                  , by simpa [sub_eq_add_neg] using h1
                  , by simpa [sub_eq_add_neg] using h2
                  , by simpa [sub_eq_add_neg] using h3
                  , by simpa [sub_eq_add_neg] using h4
                  , by simpa [sub_eq_add_neg] using h5
                  , by simpa [sub_eq_add_neg] using h6 ⟩
              , ⟨ by simp [lookupMessage0Row, lookupFlags012Row] at h7 ⊢; exact h7
                  , by simp [lookupMessage1Row, lookupFlags012Row] at h8 ⊢; exact h8
                  , by simp [lookupMessage2Row, lookupFlags012Row] at h9 ⊢; exact h9
                  , by simp [lookupMessage3Row, lookupFlags3456Row] at h10 ⊢; exact h10
                  , by simp [lookupMessage4Row, lookupFlags3456Row] at h11 ⊢; exact h11
                  , by simp [lookupMessage5Row, lookupFlags3456Row] at h12 ⊢; exact h12
                  , by simp [lookupMessage6Row, lookupFlags3456Row] at h13 ⊢; exact h13
                  , by
                      simp [lookupMessage7Row, lookupFlags7Row, sub_eq_add_neg] at h14 ⊢
                      exact h14 ⟩ ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel, Lookup.completeness_def]
      obtain ⟨mode32, resultIsA, useFirstByte, cIsSigned, carry7,
        i0, i1, i2, i3, i4, i5, i6, i7,
        h0_pos, h0_cin, h0_flags,
        h1_pos, h1_op, h1_flags,
        h2_pos, h2_op, h2_flags,
        h3_pos, h3_op, h3_flags,
        h4_pos, h4_op, h4_flags,
        h5_pos, h5_op, h5_flags,
        h6_pos, h6_op, h6_flags,
        h7_pos, h7_op, h7_flags, hrow⟩ := h_assumptions
      injection hrow with h_aBytes h_bBytes h_cBytes h_chain h_mode
      injection h_aBytes with h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7
      injection h_bBytes with h_b0 h_b1 h_b2 h_b3 h_b4 h_b5 h_b6 h_b7
      injection h_cBytes with h_c0 h_c1 h_c2 h_c3 h_c4 h_c5 h_c6 h_c7
      injection h_chain with h_carry0 h_carry1 h_carry2 h_carry3 h_carry4 h_carry5
        h_carry6 h_carry7 h_bOp h_bOpOrSext
      injection h_mode with h_mode32 h_resultIsA h_useFirstByte h_cIsSigned
        h_mode32AndCIsSigned
      subst_vars
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact boolF_booleanity_add mode32
      · exact boolF_booleanity_add carry7
      · exact boolF_booleanity_add resultIsA
      · exact boolF_booleanity_add useFirstByte
      · exact boolF_booleanity_add cIsSigned
      · simp [binaryBOpOrSextOf]
        ring_nf
      · simp [binaryMode32AndCIsSignedOf]
      · exact ⟨i0, by
          change
            { pos_ind := 2 * boolF useFirstByte
              op := (binaryTableRow i0).op
              a_byte := (binaryTableRow i0).a_byte
              b_byte := (binaryTableRow i0).b_byte
              cin := 0
              c_byte := (binaryTableRow i0).c_byte
              flags := (binaryTableRow i1).cin + 2 * boolF resultIsA
                + 4 * boolF useFirstByte } = binaryTableRow i0
          exact binaryTableMessage_eq_of_shared (binaryTableRow i0)
            (2 * boolF useFirstByte) (binaryTableRow i0).op 0
            ((binaryTableRow i1).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte)
            h0_pos rfl h0_cin h0_flags⟩
      · exact ⟨i1, by
          change
            { pos_ind := 0
              op := (binaryTableRow i0).op
              a_byte := (binaryTableRow i1).a_byte
              b_byte := (binaryTableRow i1).b_byte
              cin := (binaryTableRow i1).cin
              c_byte := (binaryTableRow i1).c_byte
              flags := (binaryTableRow i2).cin + 2 * boolF resultIsA
                + 4 * boolF useFirstByte } = binaryTableRow i1
          exact binaryTableMessage_eq_of_shared (binaryTableRow i1)
            0 (binaryTableRow i0).op (binaryTableRow i1).cin
            ((binaryTableRow i2).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte)
            h1_pos h1_op rfl h1_flags⟩
      · exact ⟨i2, by
          change
            { pos_ind := 0
              op := (binaryTableRow i0).op
              a_byte := (binaryTableRow i2).a_byte
              b_byte := (binaryTableRow i2).b_byte
              cin := (binaryTableRow i2).cin
              c_byte := (binaryTableRow i2).c_byte
              flags := (binaryTableRow i3).cin + 2 * boolF resultIsA
                + 4 * boolF useFirstByte } = binaryTableRow i2
          exact binaryTableMessage_eq_of_shared (binaryTableRow i2)
            0 (binaryTableRow i0).op (binaryTableRow i2).cin
            ((binaryTableRow i3).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte)
            h2_pos h2_op rfl h2_flags⟩
      · exact ⟨i3, by
          change
            { pos_ind := boolF mode32
              op := (binaryTableRow i0).op
              a_byte := (binaryTableRow i3).a_byte
              b_byte := (binaryTableRow i3).b_byte
              cin := (binaryTableRow i3).cin
              c_byte := (binaryTableRow i3).c_byte
              flags := (binaryTableRow i4).cin + 2 * boolF resultIsA
                + 4 * boolF useFirstByte
                + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned } = binaryTableRow i3
          exact binaryTableMessage_eq_of_shared (binaryTableRow i3)
            (boolF mode32) (binaryTableRow i0).op (binaryTableRow i3).cin
            ((binaryTableRow i4).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte
              + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned)
            h3_pos h3_op rfl h3_flags⟩
      · exact ⟨i4, by
          change
            { pos_ind := 0
              op := binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op
              a_byte := (binaryTableRow i4).a_byte
              b_byte := (binaryTableRow i4).b_byte
              cin := (binaryTableRow i4).cin
              c_byte := (binaryTableRow i4).c_byte
              flags := (binaryTableRow i5).cin + 2 * boolF resultIsA
                + 4 * boolF useFirstByte
                + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned } = binaryTableRow i4
          exact binaryTableMessage_eq_of_shared (binaryTableRow i4)
            0 (binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op)
            (binaryTableRow i4).cin
            ((binaryTableRow i5).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte
              + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned)
            h4_pos h4_op rfl h4_flags⟩
      · exact ⟨i5, by
          change
            { pos_ind := 0
              op := binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op
              a_byte := (binaryTableRow i5).a_byte
              b_byte := (binaryTableRow i5).b_byte
              cin := (binaryTableRow i5).cin
              c_byte := (binaryTableRow i5).c_byte
              flags := (binaryTableRow i6).cin + 2 * boolF resultIsA
                + 4 * boolF useFirstByte
                + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned } = binaryTableRow i5
          exact binaryTableMessage_eq_of_shared (binaryTableRow i5)
            0 (binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op)
            (binaryTableRow i5).cin
            ((binaryTableRow i6).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte
              + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned)
            h5_pos h5_op rfl h5_flags⟩
      · exact ⟨i6, by
          change
            { pos_ind := 0
              op := binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op
              a_byte := (binaryTableRow i6).a_byte
              b_byte := (binaryTableRow i6).b_byte
              cin := (binaryTableRow i6).cin
              c_byte := (binaryTableRow i6).c_byte
              flags := (binaryTableRow i7).cin + 2 * boolF resultIsA
                + 4 * boolF useFirstByte
                + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned } = binaryTableRow i6
          exact binaryTableMessage_eq_of_shared (binaryTableRow i6)
            0 (binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op)
            (binaryTableRow i6).cin
            ((binaryTableRow i7).cin + 2 * boolF resultIsA + 4 * boolF useFirstByte
              + 8 * binaryMode32AndCIsSignedOf mode32 cIsSigned)
            h6_pos h6_op rfl h6_flags⟩
      · exact ⟨i7, by
          change
            { pos_ind := 1 + -boolF mode32
              op := binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op
              a_byte := (binaryTableRow i7).a_byte
              b_byte := (binaryTableRow i7).b_byte
              cin := (binaryTableRow i7).cin
              c_byte := (binaryTableRow i7).c_byte
              flags := boolF carry7 + 2 * boolF resultIsA + 4 * boolF useFirstByte
                + 8 * boolF cIsSigned } = binaryTableRow i7
          exact binaryTableMessage_eq_of_shared (binaryTableRow i7)
            (1 + -boolF mode32)
            (binaryBOpOrSextOf mode32 cIsSigned (binaryTableRow i0).op)
            (binaryTableRow i7).cin
            (boolF carry7 + 2 * boolF resultIsA + 4 * boolF useFirstByte
              + 8 * boolF cIsSigned)
            (by simpa [sub_eq_add_neg] using h7_pos) h7_op rfl h7_flags⟩ }

def staticLookupComponent : Air.Flat.Component FGL := { circuit := staticLookupCircuit }

theorem staticLookupComponent_interactionsWith_opBus :
    staticLookupComponent.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (opBusMessageExpr staticLookupComponent.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed (opBusMessageExpr staticLookupComponent.rowInputVar)).toRaw)]⟩ ∈
    staticLookupComponent.exposedChannels
  simp only [staticLookupComponent, staticLookupCircuit,
    binaryWithStaticBinaryTableElaborated, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil]

theorem staticLookupComponent_spec
    (env : Environment FGL) :
    staticLookupComponent.Spec env =
      (Spec (staticLookupComponent.rowInput env)
        ∧ StaticBinaryTableSpecFacts (staticLookupComponent.rowInput env)) := by
  rfl

theorem component_interactionsWith_opBus :
    component.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (opBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed (opBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, binaryElaborated, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil]

theorem spec_via_component (row : BinaryRow FGL)
    (h0 : row.mode.mode32 * (1 + -row.mode.mode32) = 0)
    (h1 : row.chain.carry_7 * (1 + -row.chain.carry_7) = 0)
    (h2 : row.mode.result_is_a * (1 + -row.mode.result_is_a) = 0)
    (h3 : row.mode.use_first_byte * (1 + -row.mode.use_first_byte) = 0)
    (h4 : row.mode.c_is_signed * (1 + -row.mode.c_is_signed) = 0)
    (h5 :
      row.chain.b_op_or_sext
        + -(row.mode.mode32 * (row.mode.c_is_signed + 512 + -row.chain.b_op)
            + row.chain.b_op) = 0)
    (h6 : row.mode.mode32_and_c_is_signed
        + -(row.mode.mode32 * row.mode.c_is_signed) = 0) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, binaryElaborated,
    circuit_norm] at hsound
  refine (hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { aBytes := {
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
        mode32_and_c_is_signed := .const row.mode.mode32_and_c_is_signed } }
    row ?_ ?_).1
  · simp [circuit_norm]
  · simp only [circuit_norm]
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

end ZiskFv.AirsClean.Binary
