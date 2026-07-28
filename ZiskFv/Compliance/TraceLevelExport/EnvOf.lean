import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.ConstructionAnd
import ZiskFv.Compliance.ConstructionLogic
import ZiskFv.Compliance.ConstructionCompare
import ZiskFv.Compliance.ConstructionIType
import ZiskFv.Compliance.ConstructionShift
import ZiskFv.Compliance.ConstructionAdd
import ZiskFv.Compliance.ConstructionWAlu
import ZiskFv.Compliance.ConstructionLui
import ZiskFv.Compliance.ConstructionAuipc
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.Compliance.ConstructionDiv
import ZiskFv.Compliance.ConstructionDivu
import ZiskFv.Compliance.ConstructionDivuw
import ZiskFv.Compliance.ConstructionRemu
import ZiskFv.Compliance.ConstructionRemuw
import ZiskFv.Compliance.ConstructionStore
import ZiskFv.Compliance.ConstructionLoad
import ZiskFv.Compliance.ConstructionBranch
import ZiskFv.Compliance.ConstructionJump
import ZiskFv.Compliance
import ZiskFv.Compliance.Defects
import ZiskFv.Compliance.TraceLevelExport.Base
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding
import ZiskFv.Compliance.TraceLevelExport.RowDataAluShift
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem
import ZiskFv.Compliance.TraceLevelExport.RowDataControl

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.EquivCore.Promises
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)
open Interaction

-- The M-extension row-computing defs are reducible/semireducible; structure-field
-- elaboration would otherwise whnf-reduce the full per-row ArithMul/ArithDiv
-- computation (a runaway). `seal` blocks that locally without touching the
-- committed construction proofs (which keep the defs as-is in their oleans).
seal mulwArow mulhuArow divArow divuArow divuwArow remuArow remuwArow

set_option maxHeartbeats 8000000

theorem busSub_rd_idx_of_decode
    {numInstructions : Nat}
    {trace : AcceptedZiskTrace numInstructions}
    {i : Fin trace.numInstructions}
    {execRow : List (Interaction.ExecutionBusEntry FGL)}
    {rd : regidx}
    (h_store_ind : (mainRowWithRomSub trace i).rom.store_ind = 0)
    (h_store_offset :
      (mainRowWithRomSub trace i).rom.store_offset =
        Transpiler.ind (regidx_to_fin rd)) :
    regidx_to_fin rd =
      Transpiler.wrap_to_regidx (busSub trace i execRow).e2.ptr := by
  have h_spec := RomDecodeBinding.mainAddressSpec_at trace ⟨i.val, trace.mainTable_index i⟩
  have h_addr2 := h_spec.2.2.1
  rw [busSub, ZiskFv.AirsClean.Main.cMemMessage,
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
  rw [h_addr2, h_store_offset, h_store_ind]
  simp [Transpiler.wrap_to_regidx_ind]

/-- The `OpEnvelope.fence` env CONSTRUCTED from a `RowData_fence`.  The
    trace-local `RowOutsideDefectRegion` FENCE arm and `stepStrong_fence` both use
    these decoded row pins, so the threaded `NoKnownDefect` obligation is the
    genuine `NoKnownDefect` of the exact env the proof feeds to
    `zisk_riscv_compliant_program_bus`. -/
noncomputable def fenceEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_fence trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.fence_input.PC) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  OpEnvelope.fence d.toInputs.fence_input d.toClaim.fm d.toClaim.fenceP d.toClaim.fenceS d.toClaim.rs d.toClaim.rd (Pilot.execRowOf trace i)
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
    { input_pc_eq := d.toInputs.h_input_pc
      input_priv_eq := d.toInputs.h_input_priv
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      nextPC_matches :=
        Pilot.sequential_nextPC_discharged trace i _ d.toDecode.h_idx
          d.toDecode.h_set_pc d.toDecode.h_jmp1 d.toDecode.h_jmp2
          d.toInputs.h_pc_bridge h_domain }

/-- The `OpEnvelope.mul` env CONSTRUCTED from a `RowData_mul`.  Once the dispatcher
    instantiates the trace-local `RowOutsideDefectRegion` MUL matcher with this
    row's arith witness, the resulting predicate is the genuine `NoKnownDefect` of
    the exact env `stepStrong_mul` feeds to `zisk_riscv_compliant_program_bus`.
    (Mirrors `fenceEnvOf`: a specific-env obligation, SATISFIABLE for an honest
    row.) -/
noncomputable def mulEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mul trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.mul_input.PC) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.mul d.toInputs.mul_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd d.toClaim.srs1 d.toClaim.srs2 bus d.toInputs.v d.toInputs.r_a
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
    d.toInputs.h_match_primary
    -- #100: DERIVE the bundled `nextPC_matches` from the in-circuit transition
    -- certificate (kernel-only `sequential_nextPC_discharged`) and re-attach it to
    -- the 14 caller-supplied value/data promises. MUL's Sail nextPC = PC + 4#64.
    (d.toInputs.promises.withNextPC (PureSpec.execute_MULH_mul_pure d.toInputs.mul_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.mul_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge h_domain)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds d.toInputs.h_row_constraints
    d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges d.toInputs.h_rs1_value d.toInputs.h_rs2_value

/-- **Instantiated satisfiability / non-vacuity witness for the threaded MUL obligation.**

    The matcher-instantiated MUL obligation corresponds to
    `Defects.NoKnownDefect (mulEnvOf …)` and is DISCHARGED from
    `RowData_mul.h_not_forge` (the honest product-sign shape).  Concretely: for
    the `.mul` env, the arith-div defect predicate is
    `False` and the FENCE defect predicate's negation is `True`, while the
    arith-mul defect predicate is exactly the two exceptional product-sign shapes
    that `h_not_forge` rules out.  Hence the threaded obligation is SATISFIABLE for
    the concrete `RowData_mul` witness, so the `.mul` arm of `root_soundness`
    does not rely on a contradictory binder.  The full trace-local
    `RowOutsideDefectRegion` premise is stronger: it requires this forge
    negation for every arith witness row whose operation-bus entry, including
    result lanes, matches the accepted Main row.  This lemma is the Lean-checked
    anti-vacuity guard for the instantiated strong-export MUL arm. -/
theorem mul_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mul trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.mul_input.PC) :
    Defects.NoKnownDefect (mulEnvOf trace binding i d h_domain) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simpa [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, mulEnvOf]
        using d.toInputs.h_not_forge
  | arithDivDynamicWitnessSoundness =>
      simp [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, mulEnvOf]
  | arithDivQuotientSignSoundness =>
      simp [Defects.Blocks, Defects.ArithDivQuotientSignShape, mulEnvOf]
  | memAlignNarrowLoadLaneSoundness =>
      exact Defects.no_memAlignNarrowLoadLaneShape (mulEnvOf trace binding i d h_domain)
  | memAlignSkippableProveSoundness =>
      exact Defects.no_memAlignSkippableProveShape (mulEnvOf trace binding i d h_domain)
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, mulEnvOf]

/-- The `OpEnvelope.mulh` env CONSTRUCTED from a `RowData_mulh`.  Mirrors
    `mulEnvOf`: a specific-env obligation, SATISFIABLE for an honest signed MULH
    row. -/
noncomputable def mulhEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulh trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.mulh_input.PC) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.mulh d.toInputs.mulh_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
    d.toInputs.h_match_secondary
    -- #100: DERIVE the bundled `nextPC_matches` (MULH Sail nextPC = PC + 4#64); see `mulEnvOf`.
    (d.toInputs.promises.withNextPC (PureSpec.execute_MULH_mulh_pure d.toInputs.mulh_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.mulh_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge h_domain)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds d.toInputs.h_row_constraints
    d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges d.toInputs.h_rs1_value d.toInputs.h_rs2_value

/-- The `OpEnvelope.mulhsu` env CONSTRUCTED from a `RowData_mulhsu`. -/
noncomputable def mulhsuEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulhsu trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.mulhsu_input.PC) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.mulhsu d.toInputs.mulhsu_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
    d.toInputs.h_match_secondary
    -- #100: DERIVE the bundled `nextPC_matches` (MULHSU Sail nextPC = PC + 4#64); see `mulEnvOf`.
    (d.toInputs.promises.withNextPC (PureSpec.execute_MULH_mulhsu_pure d.toInputs.mulhsu_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.mulhsu_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge h_domain)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds d.toInputs.h_row_constraints
    d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges d.toInputs.h_rs1_value d.toInputs.h_rs2_value

/-- **Instantiated non-vacuity / satisfiability witness for the threaded MULH obligation.**
    For an honest MULH row, `h_not_forge` rules out the two exceptional shapes the
    narrowed `MaliciousSignedMulWitnessShape` admits for op 181, so
    `NoKnownDefect (mulhEnvOf …)` is TRUE for the concrete row-data witness.  The
    trace-local exported premise additionally universally excludes every matching
    arith witness row for the accepted Main row. -/
theorem mulh_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulh trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.mulh_input.PC) :
    Defects.NoKnownDefect (mulhEnvOf trace binding i d h_domain) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simpa [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, mulhEnvOf]
        using d.toInputs.h_not_forge
  | arithDivDynamicWitnessSoundness =>
      simp [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, mulhEnvOf]
  | arithDivQuotientSignSoundness =>
      simp [Defects.Blocks, Defects.ArithDivQuotientSignShape, mulhEnvOf]
  | memAlignNarrowLoadLaneSoundness =>
      exact Defects.no_memAlignNarrowLoadLaneShape (mulhEnvOf trace binding i d h_domain)
  | memAlignSkippableProveSoundness =>
      exact Defects.no_memAlignSkippableProveShape (mulhEnvOf trace binding i d h_domain)
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, mulhEnvOf]

/-- Instantiated satisfiability witness for the threaded MULHSU obligation (companion of
    `mulh_noKnownDefect_of_rowData`). -/
theorem mulhsu_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulhsu trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.mulhsu_input.PC) :
    Defects.NoKnownDefect (mulhsuEnvOf trace binding i d h_domain) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simpa [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, mulhsuEnvOf]
        using d.toInputs.h_not_forge
  | arithDivDynamicWitnessSoundness =>
      simp [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, mulhsuEnvOf]
  | arithDivQuotientSignSoundness =>
      simp [Defects.Blocks, Defects.ArithDivQuotientSignShape, mulhsuEnvOf]
  | memAlignNarrowLoadLaneSoundness =>
      exact Defects.no_memAlignNarrowLoadLaneShape (mulhsuEnvOf trace binding i d h_domain)
  | memAlignSkippableProveSoundness =>
      exact Defects.no_memAlignSkippableProveShape (mulhsuEnvOf trace binding i d h_domain)
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, mulhsuEnvOf]

private structure DivEnvFacts
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (d : RowData_div trace binding i)
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL) : Prop where
  full : ZiskFv.AirsClean.ArithMul.FullSpec arow
  shared : ZiskFv.AirsClean.ArithMul.SharedDivBlockSpec arow
  matchPrimary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv (vOfDivuRow arow) 0)
  sign : ArithDivSignWitness (vOfDivuRow arow) 0
  op : arow.flags.op = 186
  rs1 :
    d.toInputs.div_input.r1_val.toInt =
      (ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((vOfDivuRow arow).c_0 0).val ((vOfDivuRow arow).c_1 0).val
        ((vOfDivuRow arow).c_2 0).val ((vOfDivuRow arow).c_3 0).val : ℤ)
        - ((vOfDivuRow arow).np 0).val * (2 : ℤ) ^ 64
  rs2 :
    d.toInputs.div_input.r2_val.toInt =
      (ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((vOfDivuRow arow).b_0 0).val ((vOfDivuRow arow).b_1 0).val
        ((vOfDivuRow arow).b_2 0).val ((vOfDivuRow arow).b_3 0).val : ℤ)
        - ((vOfDivuRow arow).nb 0).val * (2 : ℤ) ^ 64
  remainder :
    d.toInputs.div_input.r2_val.toInt ≠ 0 →
      Nonempty (ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedRemainderBoundWitness
        (vOfDivuRow arow) 0)

set_option maxHeartbeats 4000000 in
/-- The `OpEnvelope.div` env CONSTRUCTED from a `RowData_div`.  Once the dispatcher
    instantiates the trace-local `RowOutsideDefectRegion` DIV matcher with this
    row's ArithDiv witness and witness-derived divisor, the resulting predicate is
    the genuine `NoKnownDefect` of the exact env `stepStrong_div` feeds to
    `zisk_riscv_compliant_program_bus`.  (Mirrors `mulEnvOf`: a specific-env
    obligation, SATISFIABLE for an honest signed DIV row whose `|r| ≠ |op2|`.) -/
private theorem exists_divEnvOf_of_arow
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_div trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.div_input.PC)
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (facts : DivEnvFacts trace binding i d arow)
    (h_known_remainder :
      ¬ Defects.DivRemForge d.toInputs.div_input.r2_val
        (vOfDivuRow arow) 0)
    (h_known_sign :
      ¬ Defects.SignedDivQuotientSignForge
        (vOfDivuRow arow) 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.DIV (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd, false)))
        (binding i) =
      ZiskFv.Channels.state_effect_via_channels
        ⟨(busSub trace i (Pilot.execRowOf trace i)).exec_row,
          [(busSub trace i (Pilot.execRowOf trace i)).e0,
            (busSub trace i (Pilot.execRowOf trace i)).e1,
            (busSub trace i (Pilot.execRowOf trace i)).e2]⟩
        (binding i) := by
  let bus := busSub trace i (Pilot.execRowOf trace i)
  let v := vOfDivuRow arow
  have h_full_div :
      ZiskFv.AirsClean.ArithDiv.FullSpec
        (ZiskFv.AirsClean.ArithDiv.rowAt v 0) := by
    change ZiskFv.AirsClean.ArithDiv.FullSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt (vOfDivuRow arow) 0)
    exact arithDiv_fullSpec_of_arithMul_fullSpec arow facts.full
  let arith_table : ArithDivTableWitness v 0 :=
    arithDivTableWitness_of_fullSpec h_full_div
  let arith_chunk_ranges : ArithDivChunkRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithDiv.chunkRangeLookupWitness_of_spec
      h_full_div.1 facts.full.2.2.2.1
  let arith_carry_ranges : ArithDivSignedCarryRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithDiv.signedCarryRangeLookupWitness_of_spec
      h_full_div.1 facts.full.2.2.2.2.1
  have h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v 0 := by
    change ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46
      (vOfDivuRow arow) 0
    exact divu_row_constraints_of_arithMul_fullSpec arow facts.full
  have h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v 0 := by
    change ZiskFv.Airs.ArithDiv.div_boundary_constraints (vOfDivuRow arow) 0
    rcases facts.shared with ⟨h_mode, h_boundary, h_inverse, h_scope, _⟩
    rcases h_mode with
      ⟨h_main_div, h_main_mul, _, h_signed, h_dbz, h_overflow, _⟩
    rcases h_boundary with
      ⟨hb0, hb1, hb2, hb3, ha0, ha1, ha2, ha3,
        hob0, hob1, hob2, hob3, hoc0, hoc1, hoc2, hoc3⟩
    rcases h_scope with ⟨hs0, hs1, hs2, hs3, hs4⟩
    exact ⟨h_main_div, h_main_mul, h_signed, h_dbz, h_overflow,
      hb0, hb1, hb2, hb3, ha0, ha1, ha2, ha3,
      hob0, hob1, hob2, hob3, hoc0, hoc1, hoc2, hoc3,
      h_inverse, hs0, hs1, hs2, hs3, hs4⟩
  have h_bools :
      (v.na 0 = 0 ∨ v.na 0 = 1) ∧
      (v.nb 0 = 0 ∨ v.nb 0 = 1) ∧
      (v.nr 0 = 0 ∨ v.nr 0 = 1) := by
    rcases facts.shared.1 with
      ⟨_, _, _, _, _, _, _, _, h_na, h_nb, h_nr, _, _⟩
    refine ⟨?_, ?_, ?_⟩
    · rcases mul_eq_zero.mp h_na with h | h
      · exact Or.inl (by simpa only [vOfDivuRow] using h)
      · exact Or.inr (by simpa only [vOfDivuRow] using (sub_eq_zero.mp h).symm)
    · rcases mul_eq_zero.mp h_nb with h | h
      · exact Or.inl (by simpa only [vOfDivuRow] using h)
      · exact Or.inr (by simpa only [vOfDivuRow] using (sub_eq_zero.mp h).symm)
    · rcases mul_eq_zero.mp h_nr with h | h
      · exact Or.inl (by simpa only [vOfDivuRow] using h)
      · exact Or.inr (by simpa only [vOfDivuRow] using (sub_eq_zero.mp h).symm)
  have h_r_le_of_nonzero :
      d.toInputs.div_input.r2_val.toInt ≠ 0 →
        ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 0).val (v.d_1 0).val (v.d_2 0).val (v.d_3 0).val : ℤ)
          - (v.nr 0).val * (2 : ℤ) ^ 64).natAbs
            ≤ d.toInputs.div_input.r2_val.toInt.natAbs := by
    intro h_r2_ne
    obtain ⟨w⟩ := facts.remainder h_r2_ne
    have h_op_v : v.op 0 = 186 := by
      simpa only [v, vOfDivuRow] using facts.op
    have h_bound :=
      ZiskFv.EquivCore.Bridge.Arith.arith_div_remainder_bound_signed
        w arith_chunk_ranges.ranges arith_table.spec
        arith_table.indexed_ranges h_op_v
    rw [facts.rs2]
    exact h_bound
  let env : OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
    OpEnvelope.div d.toInputs.div_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus v 0 d.toDecode.pins
    facts.matchPrimary
    -- #100: DERIVE the bundled `nextPC_matches` (DIV Sail nextPC = PC + 4#64); see `mulEnvOf`.
    -- The DivRemForge value-defect gate is untouched.
    (d.toInputs.promises.withNextPC (PureSpec.execute_DIVREM_div_pure d.toInputs.div_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.div_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge h_domain)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds h_row_constraints h_boundary
    arith_table arith_chunk_ranges arith_carry_ranges
    h_bools.1 h_bools.2.1 h_bools.2.2
    facts.sign
      facts.rs1 facts.rs2 h_r_le_of_nonzero
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32,
      d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h)
      h_known_remainder h_known_sign trivial
  exact
    (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

set_option maxHeartbeats 8000000 in
theorem exists_divEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (d : RowData_div trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.div_input.PC)
    (h_known_remainder :
      ¬ Defects.DivRemForge d.toInputs.div_input.r2_val
        (divV trace binding i d.toDecode.h_main_active d.toDecode.h_main_op) 0)
    (h_known_sign :
      ¬ Defects.SignedDivQuotientSignForge
        (divV trace binding i d.toDecode.h_main_active d.toDecode.h_main_op) 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.DIV (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd, false)))
        (binding i) =
      ZiskFv.Channels.state_effect_via_channels
        ⟨(busSub trace i (Pilot.execRowOf trace i)).exec_row,
          [(busSub trace i (Pilot.execRowOf trace i)).e0,
            (busSub trace i (Pilot.execRowOf trace i)).e1,
            (busSub trace i (Pilot.execRowOf trace i)).e2]⟩
        (binding i) := by
  have h_rem :
      d.toInputs.div_input.r2_val.toInt ≠ 0 →
        Nonempty (ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedRemainderBoundWitness
          (divV trace binding i d.toDecode.h_main_active d.toDecode.h_main_op) 0) := by
    intro h_ne
    have h_dbz :=
      divArow_div_by_zero_zero_of_nonzero_divisor trace binding i
        d.toDecode.h_main_active d.toDecode.h_main_op
        d.toInputs.div_input.r2_val
        (d.toInputs.h_rs2_value
          d.toDecode.h_main_active d.toDecode.h_main_op)
        h_ne
    exact divArow_signed_remainder_bound_witness trace binding i
      d.toDecode.h_main_active d.toDecode.h_main_op
      (divArow trace binding i d.toDecode.h_main_active d.toDecode.h_main_op)
      rfl h_dbz
  let arow := divArow trace binding i
    d.toDecode.h_main_active d.toDecode.h_main_op
  let facts : DivEnvFacts trace binding i d arow := {
    full := divArow_fullSpec_row trace binding i
      d.toDecode.h_main_active d.toDecode.h_main_op
    shared := divArow_sharedDivBlockSpec trace binding i
      d.toDecode.h_main_active d.toDecode.h_main_op
    matchPrimary := divArow_match trace binding i
      d.toDecode.h_main_active d.toDecode.h_main_op
    sign := divArow_sign_witness trace binding i
      d.toDecode.h_main_active d.toDecode.h_main_op
    op := divArow_op_eq trace binding i
      d.toDecode.h_main_active d.toDecode.h_main_op
    rs1 := d.toInputs.h_rs1_value d.toDecode.h_main_active d.toDecode.h_main_op
    rs2 := d.toInputs.h_rs2_value d.toDecode.h_main_active d.toDecode.h_main_op
    remainder := h_rem
  }
  exact exists_divEnvOf_of_arow trace binding i d h_domain arow facts
    h_known_remainder h_known_sign

/-- The `OpEnvelope.rem` env CONSTRUCTED from a `RowData_rem` (secondary lane). -/
noncomputable def remEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_rem trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.rem_input.PC) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.rem d.toInputs.rem_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a d.toDecode.pins
    d.toInputs.h_match_secondary
    -- #100: DERIVE the bundled `nextPC_matches` (REM Sail nextPC = PC + 4#64); see `mulEnvOf`.
    (d.toInputs.promises.withNextPC (PureSpec.execute_DIVREM_rem_pure d.toInputs.rem_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.rem_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge h_domain)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds d.toInputs.h_row_constraints
    d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges
    d.toInputs.h_na_bool d.toInputs.h_nb_bool d.toInputs.h_nr_bool d.toInputs.h_np_xor d.toInputs.h_nr_pin
    d.toInputs.h_rs1_value d.toInputs.h_rs2_value d.toInputs.h_r_le d.toInputs.h_r_sign

/-- The `OpEnvelope.divw` env CONSTRUCTED from a `RowData_divw` (W-mode primary). -/
noncomputable def divwEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_divw trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.divw_input.PC) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.divw d.toInputs.divw_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a d.toDecode.pins
    d.toInputs.h_match_primary
    -- #100: DERIVE the bundled `nextPC_matches` (DIVW Sail nextPC = PC + 4#64); see `mulEnvOf`.
    (d.toInputs.promises.withNextPC (PureSpec.execute_DIVREM_divw_pure d.toInputs.divw_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.divw_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge h_domain)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds
    d.toInputs.h_row_constraints d.toInputs.h_boundary d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges
    d.toInputs.h_na_bool d.toInputs.h_nb_bool d.toInputs.h_nr_bool d.toInputs.h_np_xor d.toInputs.h_nr_pin d.toInputs.h_m32_v d.toInputs.h_div_v
    d.toInputs.h_a23 d.toInputs.h_b23 d.toInputs.h_d23 d.toInputs.h_c23 d.toInputs.h_byte_lo d.toInputs.h_sext_choice
    d.toInputs.h_rs1_value d.toInputs.h_rs2_value d.toInputs.h_r_le d.toInputs.h_r_sign

/-- The `OpEnvelope.remw` env CONSTRUCTED from a `RowData_remw` (W-mode secondary). -/
noncomputable def remwEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_remw trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.remw_input.PC) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.remw d.toInputs.remw_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a d.toDecode.pins
    d.toInputs.h_match_secondary
    -- #100: DERIVE the bundled `nextPC_matches` (REMW Sail nextPC = PC + 4#64); see `mulEnvOf`.
    (d.toInputs.promises.withNextPC (PureSpec.execute_DIVREM_remw_pure d.toInputs.remw_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.remw_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge h_domain)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds
    d.toInputs.h_row_constraints d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges
    d.toInputs.h_na_bool d.toInputs.h_nb_bool d.toInputs.h_nr_bool d.toInputs.h_np_xor d.toInputs.h_nr_pin d.toInputs.h_m32_v d.toInputs.h_div_v
    d.toInputs.h_a23 d.toInputs.h_b23 d.toInputs.h_d23 d.toInputs.h_c23 d.toInputs.h_byte_lo d.toInputs.h_sext_choice
    d.toInputs.h_rs1_value d.toInputs.h_rs2_value d.toInputs.h_r_le d.toInputs.h_r_sign

/-- Instantiated satisfiability witness for the threaded REM obligation (companion of
    the selected-row DIV construction; secondary remainder lane). -/
theorem rem_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_rem trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.rem_input.PC) :
    Defects.NoKnownDefect (remEnvOf trace binding i d h_domain) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simp [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, remEnvOf]
  | arithDivDynamicWitnessSoundness =>
      simp [Defects.Blocks, Defects.ArithDivDynamicWitnessShape,
        Defects.signedRemainderInt, remEnvOf]
      intro _ h_eq
      exact d.toInputs.h_not_forge h_eq
  | arithDivQuotientSignSoundness =>
      simp [Defects.Blocks, Defects.ArithDivQuotientSignShape, remEnvOf]
  | memAlignNarrowLoadLaneSoundness =>
      exact Defects.no_memAlignNarrowLoadLaneShape (remEnvOf trace binding i d h_domain)
  | memAlignSkippableProveSoundness =>
      exact Defects.no_memAlignSkippableProveShape (remEnvOf trace binding i d h_domain)
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, remEnvOf]

/-- Instantiated satisfiability witness for the threaded DIVW obligation (W-mode analogue of
    `div_noKnownDefect_of_rowData`; narrowed shape `|r₃₂| ≠ |op2₃₂|`). -/
theorem divw_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_divw trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.divw_input.PC) :
    Defects.NoKnownDefect (divwEnvOf trace binding i d h_domain) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simp [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, divwEnvOf]
  | arithDivDynamicWitnessSoundness =>
      simpa [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, divwEnvOf]
        using d.toInputs.h_not_forge
  | arithDivQuotientSignSoundness =>
      simp [Defects.Blocks, Defects.ArithDivQuotientSignShape, divwEnvOf]
  | memAlignNarrowLoadLaneSoundness =>
      exact Defects.no_memAlignNarrowLoadLaneShape (divwEnvOf trace binding i d h_domain)
  | memAlignSkippableProveSoundness =>
      exact Defects.no_memAlignSkippableProveShape (divwEnvOf trace binding i d h_domain)
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, divwEnvOf]

/-- Instantiated satisfiability witness for the threaded REMW obligation (companion of
    `divw_noKnownDefect_of_rowData`; W-mode secondary remainder lane). -/
theorem remw_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_remw trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.remw_input.PC) :
    Defects.NoKnownDefect (remwEnvOf trace binding i d h_domain) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simp [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, remwEnvOf]
  | arithDivDynamicWitnessSoundness =>
      simpa [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, remwEnvOf]
        using d.toInputs.h_not_forge
  | arithDivQuotientSignSoundness =>
      simp [Defects.Blocks, Defects.ArithDivQuotientSignShape, remwEnvOf]
  | memAlignNarrowLoadLaneSoundness =>
      exact Defects.no_memAlignNarrowLoadLaneShape (remwEnvOf trace binding i d h_domain)
  | memAlignSkippableProveSoundness =>
      exact Defects.no_memAlignSkippableProveShape (remwEnvOf trace binding i d h_domain)
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, remwEnvOf]

/-! ### Bridge lemmas: row-data forge predicates ≡ OpEnvelope defect shapes

Each bridge is `Iff.rfl`: once the dispatcher instantiates the trace-local
`RowOutsideDefectRegion` matcher with the arith witness row already present in
`RowData_<op>`, the resulting row-data predicate and the `OpEnvelope`-based defect
shape at the corresponding `<op>EnvOf` env are DEFINITIONALLY the same
proposition.  These are the faithfulness audit for the re-expression: the
`Iff.rfl` proofs would fail if the instantiated predicate were even slightly
weaker or stronger than the original `OpEnvelope` shape. -/

theorem signedMulForge_iff_mulShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mul trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.mul_input.PC) :
    Defects.SignedMulForge d.toInputs.v d.toInputs.r_a
      ↔ Defects.MaliciousSignedMulWitnessShape (mulEnvOf trace binding i d h_domain) := Iff.rfl

theorem signedMulForge_iff_mulhShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulh trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.mulh_input.PC) :
    Defects.SignedMulForge d.toInputs.v d.toInputs.r_a
      ↔ Defects.MaliciousSignedMulWitnessShape (mulhEnvOf trace binding i d h_domain) := Iff.rfl

theorem signedMulForge_iff_mulhsuShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulhsu trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.mulhsu_input.PC) :
    Defects.SignedMulForge d.toInputs.v d.toInputs.r_a
      ↔ Defects.MaliciousSignedMulWitnessShape (mulhsuEnvOf trace binding i d h_domain) := Iff.rfl

theorem divRemForge_iff_remShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_rem trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.rem_input.PC) :
    Defects.DivRemForge d.toInputs.rem_input.r2_val d.toInputs.v d.toInputs.r_a
      ↔ Defects.ArithDivDynamicWitnessShape (remEnvOf trace binding i d h_domain) := Iff.rfl

theorem divRemForgeW_iff_divwShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_divw trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.divw_input.PC) :
    Defects.DivRemForgeW d.toInputs.divw_input.r2_val d.toInputs.v d.toInputs.r_a
      ↔ Defects.ArithDivDynamicWitnessShape (divwEnvOf trace binding i d h_domain) := Iff.rfl

theorem divRemForgeW_iff_remwShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_remw trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.remw_input.PC) :
    Defects.DivRemForgeW d.toInputs.remw_input.r2_val d.toInputs.v d.toInputs.r_a
      ↔ Defects.ArithDivDynamicWitnessShape (remwEnvOf trace binding i d h_domain) := Iff.rfl

theorem fenceKnownGood_iff_fenceShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_fence trace binding i)
    (h_domain : SequentialPcDomain d.toInputs.fence_input.PC) :
    Defects.FenceKnownGood d.toClaim.fm d.toClaim.rs d.toClaim.rd
      ↔ Defects.FenceKnownGoodShape (fenceEnvOf trace binding i d h_domain) := Iff.rfl


end ZiskFv.Compliance
