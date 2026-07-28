import ZiskFv.Compliance.ConstructionDivu
import ZiskFv.Compliance.Defects

/-!
# Signed DIV construction facts

This module constructs the signed remainder-bound Binary witness from the
physical Arith remainder consumer and its balance-selected static provider.
-/

namespace ZiskFv.Compliance

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

open Goldilocks
open Air
open ZiskFv.Airs.OperationBus
open ZiskFv.AirsClean.FullEnsemble

private lemma fgl_boolean_cases_div {x : FGL}
    (h : x * (1 - x) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

private def signedDivisorValue
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL) : ℤ :=
  (ZiskFv.PackedBitVec.MulNoWrap.packed4
    row.chunks.b_0.val row.chunks.b_1.val
    row.chunks.b_2.val row.chunks.b_3.val : ℤ)
    - row.flags.nb.val * (2 : ℤ) ^ 64

private lemma div_by_zero_zero_of_nonzero_signed_divisor
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_mode : ZiskFv.AirsClean.ArithMul.DivModeSpec row)
    (h_boundary : ZiskFv.AirsClean.ArithMul.DivBoundarySpec row)
    (r2 : BitVec 64)
    (h_rs2_value : r2.toInt = signedDivisorValue row)
    (h_r2_ne : r2.toInt ≠ 0) :
    row.flags.div_by_zero = 0 := by
  rcases fgl_boolean_cases_div h_mode.2.2.2.2.1 with h_zero | h_one
  · exact h_zero
  · have hb0 : row.chunks.b_0 = 0 := by
      have h := h_boundary.1
      rw [h_one] at h
      simpa using h
    have hb1 : row.chunks.b_1 = 0 := by
      have h := h_boundary.2.1
      rw [h_one] at h
      simpa using h
    have hb2 : row.chunks.b_2 = 0 := by
      have h := h_boundary.2.2.1
      rw [h_one] at h
      simpa using h
    have hb3 : row.chunks.b_3 = 0 := by
      have h := h_boundary.2.2.2.1
      rw [h_one] at h
      simpa using h
    rcases fgl_boolean_cases_div h_mode.2.2.2.2.2.2.2.2.2.1 with h_nb | h_nb
    · exfalso
      apply h_r2_ne
      rw [h_rs2_value]
      simp [signedDivisorValue, hb0, hb1, hb2, hb3, h_nb,
        ZiskFv.PackedBitVec.MulNoWrap.packed4]
    · exfalso
      have h_lower := BitVec.le_toInt r2
      rw [h_rs2_value] at h_lower
      norm_num [signedDivisorValue, hb0, hb1, hb2, hb3, h_nb,
        ZiskFv.PackedBitVec.MulNoWrap.packed4] at h_lower

theorem signedDiv_sign_cases_of_row
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_full : ZiskFv.AirsClean.ArithMul.FullSpec arow)
    (h_op : arow.flags.op = 186)
    (h_div_by_zero : arow.flags.div_by_zero = 0)
    (h_div_overflow : arow.flags.div_overflow = 0) :
    ArithDivOrdinarySignCases (vOfDivuRow arow) 0 := by
  unfold ArithDivOrdinarySignCases
  have h_table :
      ZiskFv.AirsClean.ArithDiv.ArithTableSpec
        (ZiskFv.AirsClean.ArithDiv.rowAt (vOfDivuRow arow) 0) :=
    (arithDiv_fullSpec_of_arithMul_fullSpec arow h_full).2.1
  rcases h_table with ⟨j, hrow⟩
  fin_cases j <;>
    simp [ZiskFv.AirsClean.ArithDiv.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op h_div_by_zero h_div_overflow ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, hna, hnb, hnp, _hnr, _hsext,
      hdbz, hoverflow, _hmain_mul, _hmain_div, _hsigned,
      _hrange_ab, _hrange_cd⟩
    simp_all [ZiskFv.PackedBitVec.SignedChunkLift.toIntZ]

/-- The completed Div constraints at the balance-selected signed-DIV row. -/
theorem divArow_sharedDivBlockSpec
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV) :
    ZiskFv.AirsClean.ArithMul.SharedDivBlockSpec
      (divArow trace binding i h_main_active h_main_op) := by
  unfold divArow
  set H := main_request_div_provided trace i h_main_active h_main_op with hH
  exact
    ZiskFv.AirsClean.FullEnsemble.arithMul_sharedDivBlockSpec_of_component_spec
      H.choose_spec.2.choose_spec.2.1
      (H.choose_spec.2.choose_spec.2.2.1
        H.choose_spec.2.choose H.choose_spec.2.choose_spec.1)

/-- The canonical legacy ArithDiv view of the balance-selected signed-DIV row. -/
noncomputable def divV
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV) :
    ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL :=
  vOfDivuRow (divArow trace binding i h_main_active h_main_op)

/-- Transport a trace-local exclusion proved for every physical signed-DIV
    provider row to the canonical balance-selected `divV`. -/
theorem divV_exclusions_of_provider_rows
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV)
    (op2 : BitVec 64)
    (h_provider :
      ∀ (providerTable : Air.Flat.Table FGL),
        providerTable ∈ trace.witness.allTables →
        ∀ (providerRow : Array FGL), providerRow ∈ providerTable.table →
        providerTable.component = arithMulProviderComponent →
        providerTable.component.Spec (providerTable.environment providerRow) →
        matches_entry
          (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
              (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                (providerTable.environment providerRow))) 1) →
        op2.toInt =
          Defects.signedDivisorInt
            (vOfDivuRow
              (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                (providerTable.environment providerRow))) 0 →
        ¬ Defects.DivRemForge op2
            (vOfDivuRow
              (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                (providerTable.environment providerRow))) 0
          ∧ ¬ Defects.SignedDivQuotientSignForge
            (vOfDivuRow
              (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                (providerTable.environment providerRow))) 0)
    (h_divisor :
      op2.toInt = Defects.signedDivisorInt
        (divV trace binding i h_main_active h_main_op) 0) :
    ¬ Defects.DivRemForge op2 (divV trace binding i h_main_active h_main_op) 0
      ∧ ¬ Defects.SignedDivQuotientSignForge
        (divV trace binding i h_main_active h_main_op) 0 := by
  unfold divV divArow at h_divisor ⊢
  let H := main_request_div_provided trace i h_main_active h_main_op
  exact h_provider H.choose H.choose_spec.1
    H.choose_spec.2.choose H.choose_spec.2.choose_spec.1
    H.choose_spec.2.choose_spec.2.1
    (H.choose_spec.2.choose_spec.2.2.1
      H.choose_spec.2.choose H.choose_spec.2.choose_spec.1)
    H.choose_spec.2.choose_spec.2.2.2 h_divisor

theorem divArow_op_eq
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV) :
    (divArow trace binding i h_main_active h_main_op).flags.op = 186 := by
  have h_match := divArow_match_row trace binding i h_main_active h_main_op
  have h_op_match := h_match.2.1
  rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
    show (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val).op
      = (mainOfTable trace.program trace.mainTable).op i.val from rfl,
    h_main_op] at h_op_match
  simpa [ZiskFv.Trusted.OP_DIV] using h_op_match.symm

/-- Complete static-table sign evidence for the selected signed-DIV row. -/
theorem divArow_sign_witness
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV) :
    ArithDivSignWitness (divV trace binding i h_main_active h_main_op) 0 := by
  let arow := divArow trace binding i h_main_active h_main_op
  have h_full := divArow_fullSpec_row trace binding i h_main_active h_main_op
  have h_op := divArow_op_eq trace binding i h_main_active h_main_op
  have h_table :
      ZiskFv.AirsClean.ArithDiv.ArithTableSpec
        (ZiskFv.AirsClean.ArithDiv.rowAt (vOfDivuRow arow) 0) :=
    (arithDiv_fullSpec_of_arithMul_fullSpec arow h_full).2.1
  refine ⟨?_, ?_⟩
  · intro h_div_by_zero h_div_overflow
    exact signedDiv_sign_cases_of_row arow h_full h_op
      (by simpa [divV, arow, vOfDivuRow] using h_div_by_zero)
      (by simpa [divV, arow, vOfDivuRow] using h_div_overflow)
  · intro h_div_overflow
    exact
      ZiskFv.AirsClean.ArithTableProjections.Div.div_overflow_sign_pins
        (vOfDivuRow arow) 0 h_table
        (by simpa [divV, arow, vOfDivuRow] using h_op)
        (by simpa [divV, arow, vOfDivuRow] using h_div_overflow)

private theorem signedDiv_selected_remainder_chain
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (brow : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_componentSpec :
      ZiskFv.AirsClean.Binary.Spec brow
        ∧ ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts brow)
    (h_core :
      ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow brow) 0)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts brow)
    (h_emit :
      brow.chain.b_op + 16 * brow.mode.mode32 =
        (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage arow).op)
    (h_nr : arow.flags.nr = 0 ∨ arow.flags.nr = 1)
    (h_nb : arow.flags.nb = 0 ∨ arow.flags.nb = 1) :
    (arow.flags.nr = 0 ∧ arow.flags.nb = 0 ∧
      ((ZiskFv.AirsClean.Binary.validOfRow brow).b_op 0).val =
        ZiskFv.Airs.Tables.BinaryTable.OP_LTU ∧
      ZiskFv.EquivCore.Bridge.Binary.BinaryChainStaticOut64
        (ZiskFv.AirsClean.Binary.validOfRow brow) 0
          ZiskFv.Airs.Tables.BinaryTable.OP_LTU)
    ∨ (arow.flags.nr = 1 ∧ arow.flags.nb = 0 ∧
      ((ZiskFv.AirsClean.Binary.validOfRow brow).b_op 0).val =
        ZiskFv.Airs.Tables.BinaryTable.OP_LT_ABS_NP ∧
      ZiskFv.EquivCore.Bridge.Binary.BinaryChainLtAbsNpStaticOut64
        (ZiskFv.AirsClean.Binary.validOfRow brow) 0)
    ∨ (arow.flags.nr = 0 ∧ arow.flags.nb = 1 ∧
      ((ZiskFv.AirsClean.Binary.validOfRow brow).b_op 0).val =
        ZiskFv.Airs.Tables.BinaryTable.OP_LT_ABS_PN ∧
      ZiskFv.EquivCore.Bridge.Binary.BinaryChainLtAbsPnStaticOut64
        (ZiskFv.AirsClean.Binary.validOfRow brow) 0)
    ∨ (arow.flags.nr = 1 ∧ arow.flags.nb = 1 ∧
      ((ZiskFv.AirsClean.Binary.validOfRow brow).b_op 0).val =
        ZiskFv.Airs.Tables.BinaryTable.OP_GT ∧
      ZiskFv.EquivCore.Bridge.Binary.BinaryChainGtStaticOut64
        (ZiskFv.AirsClean.Binary.validOfRow brow) 0) := by
  rcases h_nr with h_nr | h_nr <;> rcases h_nb with h_nb | h_nb
  · left
    have h_emit' : brow.chain.b_op + 16 * brow.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
      simpa [h_nr, h_nb, ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage,
        ZiskFv.Airs.Tables.BinaryTable.OP_LTU] using h_emit
    obtain ⟨h_mode, h_bop⟩ :=
      ZiskFv.AirsClean.Binary.static_table_remainder_bound_mode_pins_of_emit
        brow h_componentSpec.1 h_static _ (Or.inl rfl) h_emit'
    exact ⟨h_nr, h_nb, by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop,
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
        brow (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts brow h_static)
        _ h_core h_mode h_bop⟩
  · right; right; left
    have h_emit' : brow.chain.b_op + 16 * brow.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT_ABS_PN : FGL) := by
      simpa [h_nr, h_nb, ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage,
        ZiskFv.Airs.Tables.BinaryTable.OP_LT_ABS_PN] using h_emit
    obtain ⟨h_mode, h_bop⟩ :=
      ZiskFv.AirsClean.Binary.static_table_remainder_bound_mode_pins_of_emit
        brow h_componentSpec.1 h_static _
          (Or.inr (Or.inr (Or.inl rfl))) h_emit'
    exact ⟨h_nr, h_nb, by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop,
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_lt_abs_pn_discharge_64_of_static_row
        brow h_static
        (ZiskFv.AirsClean.Binary.static_table_lt_abs_pn_facts_of_spec_facts brow h_static)
        h_core h_mode h_bop⟩
  · right; left
    have h_emit' : brow.chain.b_op + 16 * brow.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT_ABS_NP : FGL) := by
      simpa [h_nr, h_nb, ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage,
        ZiskFv.Airs.Tables.BinaryTable.OP_LT_ABS_NP] using h_emit
    obtain ⟨h_mode, h_bop⟩ :=
      ZiskFv.AirsClean.Binary.static_table_remainder_bound_mode_pins_of_emit
        brow h_componentSpec.1 h_static _ (Or.inr (Or.inl rfl)) h_emit'
    exact ⟨h_nr, h_nb, by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop,
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_lt_abs_np_discharge_64_of_static_row
        brow h_static
        (ZiskFv.AirsClean.Binary.static_table_lt_abs_np_facts_of_spec_facts brow h_static)
        h_core h_mode h_bop⟩
  · right; right; right
    have h_emit' : brow.chain.b_op + 16 * brow.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_GT : FGL) := by
      simpa [h_nr, h_nb, ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage,
        ZiskFv.Airs.Tables.BinaryTable.OP_GT] using h_emit
    obtain ⟨h_mode, h_bop⟩ :=
      ZiskFv.AirsClean.Binary.static_table_remainder_bound_mode_pins_of_emit
        brow h_componentSpec.1 h_static _ (Or.inr (Or.inr (Or.inr rfl))) h_emit'
    exact ⟨h_nr, h_nb, by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop,
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_gt_discharge_64_of_static_row
        brow h_static
        (ZiskFv.AirsClean.Binary.static_table_gt_facts_of_spec_facts brow h_static)
        h_core h_mode h_bop⟩

private theorem signedDiv_remainder_bound_witness_of_rows
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (brow : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_componentSpec :
      ZiskFv.AirsClean.Binary.Spec brow
        ∧ ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts brow)
    (h_binaryMatch :
      matches_entry
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage arow) 1)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.Binary.opBusMessage brow) 1))
    (h_div : arow.flags.div = 1)
    (h_div_by_zero : arow.flags.div_by_zero = 0)
    (h_nr : arow.flags.nr = 0 ∨ arow.flags.nr = 1)
    (h_nb : arow.flags.nb = 0 ∨ arow.flags.nb = 1) :
    Nonempty (ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedRemainderBoundWitness
      (vOfDivuRow arow) 0) := by
  have h_core :
      ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow brow) 0 :=
    ZiskFv.AirsClean.Binary.core_every_row_of_spec brow h_componentSpec.1
  have h_static := h_componentSpec.2
  have h_emit :
      brow.chain.b_op + 16 * brow.mode.mode32 =
        (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage arow).op :=
    h_binaryMatch.2.1.symm
  have h_selected := signedDiv_selected_remainder_chain arow brow
    h_componentSpec h_core h_static h_emit h_nr h_nb
  have h_binaryMatch' :
      matches_entry
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage arow) 1)
        (opBus_row_Binary (ZiskFv.AirsClean.Binary.validOfRow brow) 0) := by
    rw [← ZiskFv.AirsClean.Binary.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [ZiskFv.AirsClean.Binary.rowAt_validOfRow_zero]
    exact h_binaryMatch
  refine ⟨{
    binary := ZiskFv.AirsClean.Binary.validOfRow brow
    r_binary := 0
    binary_core := h_core
    selected_chain := h_selected
    remainder_bound_match := ?_
  }⟩
  rw [← remainderBoundOpBusMessage_toEntry_eq_opBus_row_ArithDiv arow
    h_div h_div_by_zero]
  exact h_binaryMatch'

set_option maxHeartbeats 4000000 in
/-- An explicit accepted Arith provider row's active remainder-bound consumer
    is matched by the corresponding sign-selected static Binary chain. -/
theorem signedDiv_remainder_bound_witness_of_provider
    (trace : AcceptedZiskTrace numInstructions)
    (providerTable : Air.Flat.Table FGL)
    (h_providerTable : providerTable ∈ trace.witness.allTables)
    (providerRow : Array FGL) (h_providerRow : providerRow ∈ providerTable.table)
    (h_component :
      providerTable.component =
        ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_arow :
      arow = ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
        (providerTable.environment providerRow))
    (h_op : arow.flags.op = 186)
    (h_div_by_zero : arow.flags.div_by_zero = 0) :
    Nonempty (ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedRemainderBoundWitness
      (vOfDivuRow arow) 0) := by
  have h_completeSpec :
      ZiskFv.AirsClean.ArithMul.componentComplete.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_providerSpec
  rw [ZiskFv.AirsClean.ArithMul.componentComplete_spec] at h_completeSpec
  have h_full : ZiskFv.AirsClean.ArithMul.FullSpec arow := by
    simpa [h_arow] using h_completeSpec.1
  have h_div : arow.flags.div = 1 :=
    (ZiskFv.AirsClean.ArithTableProjections.Mul.div_mode_pins_of_row
      arow h_full.2.1 h_op).2.2.1
  have h_completed : ZiskFv.AirsClean.ArithMul.SharedDivBlockSpec arow := by
    simpa [h_arow] using h_completeSpec.2
  have h_nr := fgl_boolean_cases_div h_completed.1.2.2.2.2.2.2.2.2.2.2.1
  have h_nb := fgl_boolean_cases_div h_completed.1.2.2.2.2.2.2.2.2.2.1
  have h_op_provider :
      (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
        (providerTable.environment providerRow)).flags.op = 186 := by
    rw [← h_arow]
    exact h_op
  have h_div_by_zero_provider :
      (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
        (providerTable.environment providerRow)).flags.div_by_zero = 0 := by
    rw [← h_arow]
    exact h_div_by_zero
  obtain ⟨binaryTable, h_binaryTable, binaryRow, h_binaryRow,
      h_binarySpec, h_binaryComponent, h_binaryMatch⟩ :=
    signedDiv_remainder_bound_provider trace h_providerTable h_providerRow
      h_component h_providerSpec h_op_provider h_div_by_zero_provider
  set brow :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (binaryTable.environment binaryRow) with h_brow
  have h_componentSpec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (binaryTable.environment binaryRow) := by
    simpa [h_binaryComponent] using h_binarySpec
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_componentSpec
  change (ZiskFv.AirsClean.Binary.Spec brow
    ∧ ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts brow) at h_componentSpec
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
    at h_binaryMatch
  rw [← h_arow, ← h_brow] at h_binaryMatch
  exact signedDiv_remainder_bound_witness_of_rows arow brow h_componentSpec
    h_binaryMatch h_div h_div_by_zero h_nr h_nb

set_option maxHeartbeats 4000000 in
/-- The balance-selected signed DIV row's active remainder-bound consumer is
    matched by a concrete sign-selected static Binary chain. -/
theorem divArow_signed_remainder_bound_witness
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV)
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_arow : arow = divArow trace binding i h_main_active h_main_op)
    (h_div_by_zero : arow.flags.div_by_zero = 0) :
    Nonempty (ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedRemainderBoundWitness
      (vOfDivuRow arow) 0) := by
  set H := main_request_div_provided trace i h_main_active h_main_op with hH
  obtain ⟨h_providerTable, h_rest⟩ := H.choose_spec
  obtain ⟨h_providerRow, h_component, h_providerSpec, h_primaryMatch⟩ :=
    h_rest.choose_spec
  have h_arow_provider :
      arow = ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
        (H.choose.environment h_rest.choose) := by
    unfold divArow at h_arow
    rw [← hH] at h_arow
    exact h_arow
  have h_op_provider :
      (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
        (H.choose.environment h_rest.choose)).flags.op = 186 := by
    have h_op_match := h_primaryMatch.2.1
    rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
      show (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val).op
        = (mainOfTable trace.program trace.mainTable).op i.val from rfl,
      h_main_op] at h_op_match
    exact h_op_match.symm
  have h_op : arow.flags.op = 186 := by
    rw [h_arow_provider]
    exact h_op_provider
  exact signedDiv_remainder_bound_witness_of_provider trace H.choose
    h_providerTable h_rest.choose h_providerRow h_component
    (h_providerSpec h_rest.choose h_providerRow) arow h_arow_provider
    h_op h_div_by_zero

/-- A nonzero signed divisor activates the physical remainder consumer:
    the completed Div boundary equations rule out `div_by_zero = 1`. -/
theorem divArow_div_by_zero_zero_of_nonzero_divisor
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV)
    (r2 : BitVec 64)
    (h_rs2_value :
      r2.toInt =
        signedDivisorValue (divArow trace binding i h_main_active h_main_op))
    (h_r2_ne : r2.toInt ≠ 0) :
    (divArow trace binding i h_main_active h_main_op).flags.div_by_zero = 0 := by
  apply div_by_zero_zero_of_nonzero_signed_divisor
    (divArow trace binding i h_main_active h_main_op)
    (divArow_sharedDivBlockSpec trace binding i h_main_active h_main_op).1
    (divArow_sharedDivBlockSpec trace binding i h_main_active h_main_op).2.1 r2
  · exact h_rs2_value
  · exact h_r2_ne

end ZiskFv.Compliance
