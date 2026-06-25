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
import ZiskFv.Compliance.TraceLevelExport.RowDataAluShift
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem
import ZiskFv.Compliance.TraceLevelExport.RowDataControl
import ZiskFv.Compliance.TraceLevelExport.EnvOf

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
seal mulwArow mulhuArow divuArow divuwArow remuArow remuwArow

set_option maxHeartbeats 8000000

/-! ## Trace-level export: env-constructed channel-balance form

The theorems below are the trace-level export over the accepted trace.  For each
arm they prove the EXACT
conclusion of the OLD global theorem `zisk_riscv_compliant_program_bus` — the
channel-balance `state_effect_via_channels` form — but with the `OpEnvelope`
**constructed from the accepted trace** (rather than supplied as a parameter).
The envelope per row is assembled by re-running the same provider-match /
input-assembly derivations `construction_<op>_sound` uses internally; the three
global-theorem hypotheses are discharged in place:
`aeneasBridgeTrust` from the derived row-binding facts, `memoryTimelineConstruction`
trivially (non-load arms), and `NoKnownDefect` trivially (the strengthened arms
are all non-defect opcodes).  Hence anything the old theorem yields for these
arms, the strengthened theorem yields from the trace.

Non-vacuity: each envelope is the real `OpEnvelope.<op>` over the committed
trace's `mainOfTable` row; `execRow` remains a genuine ∀-binder inside the
`RowData_<op>`; `NoKnownDefect` is a TRUE fact (not a contradictory hypothesis);
no `False.elim` or contradictory pair is used.
-/

/-- Strengthened `sub` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.sub` arm
    from accepted-trace data (reusing `construction_sub_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.sub`. -/
theorem stepStrong_sub
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sub trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sub .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SUB))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_sub_provided
      trace i d.h_main_active d.h_main_op
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SUB :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.sub_input.r1_val d.sub_input.r2_val d.sub_input.rd d.sub_input.PC
      (PureSpec.execute_RTYPE_sub_pure d.sub_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_SUB : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_SUB, ZiskFv.Trusted.OP_SUB] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_SUB (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_SUB])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.sub_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.sub_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.sub_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.sub_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sub d.sub_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1

/-- Strengthened `and` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.and` arm
    from accepted-trace data (reusing `construction_and_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.and`. -/
theorem stepStrong_and
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_and trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .and .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.AND))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_logic_provided
      trace i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_AND :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.and_input.r1_val d.and_input.r2_val d.and_input.rd d.and_input.PC
      (PureSpec.execute_RTYPE_and_pure d.and_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_AND : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND, ZiskFv.Trusted.OP_AND] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_AND (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_AND])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_AND h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_AND :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.and_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.and_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.and_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.and_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.and d.and_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1

/-- Strengthened `or` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.or` arm
    from accepted-trace data (reusing `construction_or_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.or`. -/
theorem stepStrong_or
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_or trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .or .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.OR))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_logic_provided
      trace i d.h_main_active (Or.inr (Or.inl d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_OR :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.or_input.r1_val d.or_input.r2_val d.or_input.rd d.or_input.PC
      (PureSpec.execute_RTYPE_or_pure d.or_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_OR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_OR, ZiskFv.Trusted.OP_OR] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_OR (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_OR])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_OR h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_OR :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.or_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.or_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.or_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.or_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.or d.or_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1

/-- Strengthened `xor` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.xor` arm
    from accepted-trace data (reusing `construction_xor_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.xor`. -/
theorem stepStrong_xor
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_xor trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .xor .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.XOR))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_logic_provided
      trace i d.h_main_active (Or.inr (Or.inr d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_XOR :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.xor_input.r1_val d.xor_input.r2_val d.xor_input.rd d.xor_input.PC
      (PureSpec.execute_RTYPE_xor_pure d.xor_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  -- XOR's table op is 16, NOT `< 16`, so it takes the op=16 mode-pin route
  -- (`static_table_logic_mode_pins_of_emit` + `byte_chain_discharge_logic_of_static_row`),
  -- exactly as `construction_xor_sound` does internally.
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  obtain ⟨h_row_spec, h_static⟩ := h_component_spec
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_XOR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_XOR, ZiskFv.Trusted.OP_XOR] using
      d.h_main_op
  obtain ⟨_, h_bop_row, h_bop_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      providerInput h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_XOR
      (.inr (.inr rfl)) h_emit
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_XOR :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      providerInput h_facts ZiskFv.Airs.Tables.BinaryTable.OP_XOR h_bop_row h_bop_or_sext
  have h_input_r1_row :
      d.xor_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.xor_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.xor_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.xor_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.xor d.xor_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1

/-- Strengthened `slt` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.slt` arm
    from accepted-trace data (reusing `construction_slt_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.slt`. -/
theorem stepStrong_slt
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_slt trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .slt .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLT))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_compare_provided
      trace i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_LT :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.slt_input.r1_val d.slt_input.r2_val d.slt_input.rd d.slt_input.PC
      (PureSpec.execute_RTYPE_slt_pure d.slt_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LT h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.slt_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.slt_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.slt_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.slt_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.slt d.slt_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1

/-- Strengthened `sltu` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.sltu` arm
    from accepted-trace data (reusing `construction_sltu_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.sltu`. -/
theorem stepStrong_sltu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sltu trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sltu .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLTU))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_compare_provided
      trace i d.h_main_active (Or.inr d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_LTU :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.sltu_input.r1_val d.sltu_input.r2_val d.sltu_input.rd d.sltu_input.PC
      (PureSpec.execute_RTYPE_sltu_pure d.sltu_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU, ZiskFv.Trusted.OP_LTU] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LTU :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.sltu_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.sltu_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.sltu_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.sltu_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sltu d.sltu_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1


/-- Strengthened `andi` step: channel-balance conclusion via constructed
    `OpEnvelope.andi` + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.andi`. -/
theorem stepStrong_andi
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_andi trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .andi .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ANDI))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_logic_provided
      trace i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_AND :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.andi_input.r1_val d.andi_input.imm d.andi_input.rd d.andi_input.PC
      (PureSpec.execute_ITYPE_andi_pure d.andi_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_AND : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND, ZiskFv.Trusted.OP_AND] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_AND (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_AND])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_AND h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_AND :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.andi_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.andi_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_imm_row :
      BitVec.signExtend 64 d.andi_input.imm
        = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m providerInput i.val d.andi_input.imm h_matches h_m32_zero h_match
        d.h_andi_subset
  let env : OpEnvelope state m i.val :=
    OpEnvelope.andi d.andi_input d.r1 d.rd d.imm zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_imm_row d.h_andi_subset h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_imm_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.1

/-- Strengthened `ori` step: channel-balance conclusion via constructed
    `OpEnvelope.ori` + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.ori`. -/
theorem stepStrong_ori
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_ori trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .ori .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ORI))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_logic_provided
      trace i d.h_main_active (Or.inr (Or.inl d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_OR :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.ori_input.r1_val d.ori_input.imm d.ori_input.rd d.ori_input.PC
      (PureSpec.execute_ITYPE_ori_pure d.ori_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_OR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_OR, ZiskFv.Trusted.OP_OR] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_OR (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_OR])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_OR h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_OR :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.ori_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.ori_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_imm_row :
      BitVec.signExtend 64 d.ori_input.imm
        = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m providerInput i.val d.ori_input.imm h_matches h_m32_zero h_match
        d.h_ori_subset
  let env : OpEnvelope state m i.val :=
    OpEnvelope.ori d.ori_input d.r1 d.rd d.imm zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_imm_row d.h_ori_subset h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_imm_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.1

/-- Strengthened `xori` step: channel-balance conclusion via constructed
    `OpEnvelope.xori` + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.xori`. -/
theorem stepStrong_xori
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_xori trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .xori .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.XORI))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_logic_provided
      trace i d.h_main_active (Or.inr (Or.inr d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_XOR :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.xori_input.r1_val d.xori_input.imm d.xori_input.rd d.xori_input.PC
      (PureSpec.execute_ITYPE_xori_pure d.xori_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  obtain ⟨h_row_spec, h_static⟩ := h_component_spec
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_XOR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_XOR, ZiskFv.Trusted.OP_XOR] using
      d.h_main_op
  obtain ⟨_, h_bop_row, h_bop_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      providerInput h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_XOR
      (.inr (.inr rfl)) h_emit
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_XOR :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      providerInput h_facts ZiskFv.Airs.Tables.BinaryTable.OP_XOR h_bop_row h_bop_or_sext
  have h_input_r1_row :
      d.xori_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.xori_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_imm_row :
      BitVec.signExtend 64 d.xori_input.imm
        = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m providerInput i.val d.xori_input.imm h_matches h_m32_zero h_match
        d.h_xori_subset
  let env : OpEnvelope state m i.val :=
    OpEnvelope.xori d.xori_input d.r1 d.rd d.imm zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_imm_row d.h_xori_subset h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_imm_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.1

/-- Strengthened `slti` step: channel-balance conclusion via constructed
    `OpEnvelope.slti` + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.slti`. -/
theorem stepStrong_slti
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_slti trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .slti .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTI))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_compare_provided
      trace i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_LT :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.slti_input.r1_val d.slti_input.imm d.slti_input.rd d.slti_input.PC
      (PureSpec.execute_ITYPE_slti_pure d.slti_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LT h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.slti_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.slti_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  let env : OpEnvelope state m i.val :=
    OpEnvelope.slti d.slti_input d.r1 d.rd d.imm zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_m32_zero h_input_r1_row d.h_slti_subset h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_m32_zero, h_input_r1_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.1

/-- Strengthened `sltiu` step: channel-balance conclusion via constructed
    `OpEnvelope.sltiu` + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.sltiu`. -/
theorem stepStrong_sltiu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sltiu trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sltiu .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTIU))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_compare_provided
      trace i d.h_main_active (Or.inr d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_LTU :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.sltiu_input.r1_val d.sltiu_input.imm d.sltiu_input.rd d.sltiu_input.PC
      (PureSpec.execute_ITYPE_sltiu_pure d.sltiu_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU, ZiskFv.Trusted.OP_LTU] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LTU :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.sltiu_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.sltiu_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sltiu d.sltiu_input d.r1 d.rd d.imm zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_m32_zero h_input_r1_row d.h_sltiu_subset h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_m32_zero, h_input_r1_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.1



/-- Strengthened `sll` step: channel-balance via constructed `OpEnvelope.sll`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.sll`. -/
theorem stepStrong_sll
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sll trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sll .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLL))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.sll_input.r1_val d.sll_input.r2_val d.sll_input.rd d.sll_input.PC
      (PureSpec.execute_RTYPE_sll_pure d.sll_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inl (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.sll_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_0_shift_pin_row_of_facts m _ i.val (regidx_to_fin d.r2) d.sll_input.r2_val
      h_m32_zero d.h_b_lo_t d.h_b_hi_t d.h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sll d.sll_input d.r1 d.r2 d.rd providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1

/-- Strengthened `srl` step: channel-balance via constructed `OpEnvelope.srl`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.srl`. -/
theorem stepStrong_srl
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_srl trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .srl .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRL))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active (Or.inr (Or.inl d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.srl_input.r1_val d.srl_input.r2_val d.srl_input.rd d.srl_input.PC
      (PureSpec.execute_RTYPE_srl_pure d.srl_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      ((fun h => Or.inr (Or.inl h)) (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.srl_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_0_shift_pin_row_of_facts m _ i.val (regidx_to_fin d.r2) d.srl_input.r2_val
      h_m32_zero d.h_b_lo_t d.h_b_hi_t d.h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.srl d.srl_input d.r1 d.r2 d.rd providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1

/-- Strengthened `sra` step: channel-balance via constructed `OpEnvelope.sra`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.sra`. -/
theorem stepStrong_sra
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sra trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sra .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRA))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active (Or.inr (Or.inr (Or.inl d.h_main_op)))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.sra_input.r1_val d.sra_input.r2_val d.sra_input.rd d.sra_input.PC
      (PureSpec.execute_RTYPE_sra_pure d.sra_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      ((fun h => Or.inr (Or.inr (Or.inl h))) (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.sra_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_0_shift_pin_row_of_facts m _ i.val (regidx_to_fin d.r2) d.sra_input.r2_val
      h_m32_zero d.h_b_lo_t d.h_b_hi_t d.h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sra d.sra_input d.r1 d.r2 d.rd providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1

/-- Strengthened `slli` step: channel-balance via constructed `OpEnvelope.slli`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.slli`. -/
theorem stepStrong_slli
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_slli trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .slli .. => True | _ => False)) :
    execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SLLI)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
      state d.slli_input.r1_val d.slli_input.shamt d.slli_input.rd d.slli_input.PC
      (PureSpec.execute_SHIFTIOP_slli_pure d.slli_input).nextPC
      d.r1 d.rd d.shamt bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_shamt_eq := d.h_input_shamt,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inl (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.slli_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :
      d.slli_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)) := by
    rw [d.h_input_shamt]
    exact shift_imm_shift_pin_row_of_facts m _ i.val d.shamt
      d.h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.slli d.slli_input d.r1 d.rd d.shamt providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1

/-- Strengthened `srli` step: channel-balance via constructed `OpEnvelope.srli`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.srli`. -/
theorem stepStrong_srli
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_srli trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .srli .. => True | _ => False)) :
    execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRLI)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active (Or.inr (Or.inl d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
      state d.srli_input.r1_val d.srli_input.shamt d.srli_input.rd d.srli_input.PC
      (PureSpec.execute_SHIFTIOP_srli_pure d.srli_input).nextPC
      d.r1 d.rd d.shamt bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_shamt_eq := d.h_input_shamt,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      ((fun h => Or.inr (Or.inl h)) (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.srli_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :
      d.srli_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)) := by
    rw [d.h_input_shamt]
    exact shift_imm_shift_pin_row_of_facts m _ i.val d.shamt
      d.h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.srli d.srli_input d.r1 d.rd d.shamt providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1

/-- Strengthened `srai` step: channel-balance via constructed `OpEnvelope.srai`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.srai`. -/
theorem stepStrong_srai
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_srai trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .srai .. => True | _ => False)) :
    execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRAI)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active (Or.inr (Or.inr (Or.inl d.h_main_op)))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
      state d.srai_input.r1_val d.srai_input.shamt d.srai_input.rd d.srai_input.PC
      (PureSpec.execute_SHIFTIOP_srai_pure d.srai_input).nextPC
      d.r1 d.rd d.shamt bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_shamt_eq := d.h_input_shamt,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      ((fun h => Or.inr (Or.inr (Or.inl h))) (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.srai_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :
      d.srai_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)) := by
    rw [d.h_input_shamt]
    exact shift_imm_shift_pin_row_of_facts m _ i.val d.shamt
      d.h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.srai d.srai_input d.r1 d.rd d.shamt providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1



/-- Strengthened `subw` step: channel-balance via constructed `OpEnvelope.subw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.subw`. -/
theorem stepStrong_subw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_subw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .subw .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SUBW))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_w_provided
      trace i d.h_main_active (Or.inr d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SUB_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := d.h_m32
  have ha0 : (providerInput.aBytes.free_in_a_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.1
  have ha1 : (providerInput.aBytes.free_in_a_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.1
  have ha2 : (providerInput.aBytes.free_in_a_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.1
  have ha3 : (providerInput.aBytes.free_in_a_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.1
  have h_input_r1_extract :
      (Sail.BitVec.extractLsb d.subw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowA32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a32_row
        m providerInput i.val (regidx_to_fin d.r1) d.subw_input.r1_val
        ha0 ha1 ha2 ha3 h_m32_one d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have hb0 : (providerInput.bBytes.free_in_b_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.2.1
  have hb1 : (providerInput.bBytes.free_in_b_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.2.1
  have hb2 : (providerInput.bBytes.free_in_b_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.2.1
  have hb3 : (providerInput.bBytes.free_in_b_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.2.1
  have h_input_r2_extract :
      (Sail.BitVec.extractLsb d.subw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowB32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b32_row
        m providerInput i.val (regidx_to_fin d.r2) d.subw_input.r2_val
        hb0 hb1 hb2 hb3 h_m32_one d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.subw_input.r1_val d.subw_input.r2_val d.subw_input.rd d.subw_input.PC
      (PureSpec.execute_RTYPE_subw_pure d.subw_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.subw d.subw_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_extract h_input_r2_extract h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_extract, h_input_r2_extract⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.1

/-- Strengthened `addw` step: channel-balance via constructed `OpEnvelope.addw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.addw`. -/
theorem stepStrong_addw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_addw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .addw .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.ADDW))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_w_provided
      trace i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := d.h_m32
  have ha0 : (providerInput.aBytes.free_in_a_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.1
  have ha1 : (providerInput.aBytes.free_in_a_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.1
  have ha2 : (providerInput.aBytes.free_in_a_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.1
  have ha3 : (providerInput.aBytes.free_in_a_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.1
  have h_input_r1_extract :
      (Sail.BitVec.extractLsb d.addw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowA32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a32_row
        m providerInput i.val (regidx_to_fin d.r1) d.addw_input.r1_val
        ha0 ha1 ha2 ha3 h_m32_one d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have hb0 : (providerInput.bBytes.free_in_b_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.2.1
  have hb1 : (providerInput.bBytes.free_in_b_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.2.1
  have hb2 : (providerInput.bBytes.free_in_b_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.2.1
  have hb3 : (providerInput.bBytes.free_in_b_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.2.1
  have h_input_r2_extract :
      (Sail.BitVec.extractLsb d.addw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowB32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b32_row
        m providerInput i.val (regidx_to_fin d.r2) d.addw_input.r2_val
        hb0 hb1 hb2 hb3 h_m32_one d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.addw_input.r1_val d.addw_input.r2_val d.addw_input.rd d.addw_input.PC
      (PureSpec.execute_RTYPE_addw_pure d.addw_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.addw d.addw_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_extract h_input_r2_extract h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_extract, h_input_r2_extract⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.1

/-- Strengthened `addiw` step: channel-balance via constructed `OpEnvelope.addiw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.addiw`. -/
theorem stepStrong_addiw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_addiw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .addiw .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (d.imm, d.r1, d.rd))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_w_provided
      trace i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := d.h_m32
  have ha0 : (providerInput.aBytes.free_in_a_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.1
  have ha1 : (providerInput.aBytes.free_in_a_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.1
  have ha2 : (providerInput.aBytes.free_in_a_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.1
  have ha3 : (providerInput.aBytes.free_in_a_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.1
  have h_input_r1_extract :
      (Sail.BitVec.extractLsb d.addiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowA32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a32_row
        m providerInput i.val (regidx_to_fin d.r1) d.addiw_input.r1_val
        ha0 ha1 ha2 ha3 h_m32_one d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.addiw_input.r1_val d.addiw_input.imm d.addiw_input.rd d.addiw_input.PC
      (PureSpec.execute_ITYPE_addiw_pure d.addiw_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.addiw d.addiw_input d.r1 d.rd d.imm zeroValidBinary bus pins
      d.h_addiw_subset providerTable providerRow h_component h_table_spec h_provider_row
      h_match h_input_r1_extract h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := h_input_r1_extract
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.1

/-! ## Strengthened W-shift arms (SLLW/SRLW/SRAW/SLLIW/SRLIW/SRAIW, channel-balance form)

OpEnvelope route, mirroring the base-shift arms (`stepStrong_sll` etc.) but on the
m32 = 1 register/immediate W-shift route.  Each arm builds `OpEnvelope.<op>` from
the trace's BinaryExtension shift provider row (derived from `trace.channels_balanced`),
invokes `zisk_riscv_compliant_program_bus`, and projects `exec_eq_remaining` (the
12th conjunct).  The promise/provider plumbing is the m32 = 1 variant of the base
shift (`shift_m32_1_*_of_facts`); the conclusion is the `RTYPEW`/`SHIFTIWOP`
W-shift form.  Non-vacuous: `execRow` is a genuine ∀-binder; the provider row is a
real BinaryExtension Spec row from the committed trace. -/

/-- Strengthened `sllw` step: channel-balance via constructed `OpEnvelope.sllw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.sllw`. -/
theorem stepStrong_sllw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sllw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sllw .. => True | _ => False)) :
    execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SLLW)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active (Or.inr (Or.inr (Or.inr (Or.inl d.h_main_op))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.sllw_input.r1_val d.sllw_input.r2_val d.sllw_input.rd d.sllw_input.PC
      (PureSpec.execute_RTYPE_sllw_pure d.sllw_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inl
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op])))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.sllw_input.r1_val
      h_m32_one d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_shift_pin_row_of_facts m _ i.val (regidx_to_fin d.r2) d.sllw_input.r2_val
      d.h_b_lo_t d.h_b_hi_t d.h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sllw d.sllw_input d.r1 d.r2 d.rd providerTable providerRow bus
      d.h_input_r1 d.h_input_r2 d.h_input_rd d.h_input_pc d.h_exec_len d.h_e0_mult
      d.h_e1_mult d.h_nextPC_matches (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) d.h_rd_idx pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `srlw` step: channel-balance via constructed `OpEnvelope.srlw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.srlw`. -/
theorem stepStrong_srlw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_srlw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .srlw .. => True | _ => False)) :
    execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SRLW)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl d.h_main_op)))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.srlw_input.r1_val d.srlw_input.r2_val d.srlw_input.rd d.srlw_input.PC
      (PureSpec.execute_RTYPE_srlw_pure d.srlw_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.srlw_input.r1_val
      h_m32_one d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_shift_pin_row_of_facts m _ i.val (regidx_to_fin d.r2) d.srlw_input.r2_val
      d.h_b_lo_t d.h_b_hi_t d.h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.srlw d.srlw_input d.r1 d.r2 d.rd providerTable providerRow bus
      d.h_input_r1 d.h_input_r2 d.h_input_rd d.h_input_pc d.h_exec_len d.h_e0_mult
      d.h_e1_mult d.h_nextPC_matches (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) d.h_rd_idx pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `sraw` step: channel-balance via constructed `OpEnvelope.sraw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.sraw`. -/
theorem stepStrong_sraw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sraw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sraw .. => True | _ => False)) :
    execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SRAW)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr d.h_main_op)))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.sraw_input.r1_val d.sraw_input.r2_val d.sraw_input.rd d.sraw_input.PC
      (PureSpec.execute_RTYPE_sraw_pure d.sraw_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.sraw_input.r1_val
      h_m32_one d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_shift_pin_row_of_facts m _ i.val (regidx_to_fin d.r2) d.sraw_input.r2_val
      d.h_b_lo_t d.h_b_hi_t d.h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sraw d.sraw_input d.r1 d.r2 d.rd providerTable providerRow bus
      d.h_input_r1 d.h_input_r2 d.h_input_rd d.h_input_pc d.h_exec_len d.h_e0_mult
      d.h_e1_mult d.h_nextPC_matches (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) d.h_rd_idx pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `slliw` step: channel-balance via constructed `OpEnvelope.slliw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.slliw`. -/
theorem stepStrong_slliw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_slliw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .slliw .. => True | _ => False)) :
    execute_instruction
      (instruction.SHIFTIWOP (d.slliw_input.shamt, d.r1, d.rd, sopw.SLLIW)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active (Or.inr (Or.inr (Or.inr (Or.inl d.h_main_op))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
      state d.slliw_input.r1_val d.slliw_input.rd d.slliw_input.PC
      (PureSpec.execute_SHIFTIWOP_slliw_pure d.slliw_input).nextPC
      d.r1 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inl
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op])))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.slliw_input.r1_val
      d.h_m32 d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_imm_shift_pin_row_of_facts m _ i.val d.slliw_input.shamt
      d.h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.slliw d.slliw_input d.r1 d.rd providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `srliw` step: channel-balance via constructed `OpEnvelope.srliw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.srliw`. -/
theorem stepStrong_srliw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_srliw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .srliw .. => True | _ => False)) :
    execute_instruction
      (instruction.SHIFTIWOP (d.srliw_input.shamt, d.r1, d.rd, sopw.SRLIW)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl d.h_main_op)))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
      state d.srliw_input.r1_val d.srliw_input.rd d.srliw_input.PC
      (PureSpec.execute_SHIFTIWOP_srliw_pure d.srliw_input).nextPC
      d.r1 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.srliw_input.r1_val
      d.h_m32 d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_imm_shift_pin_row_of_facts m _ i.val d.srliw_input.shamt
      d.h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.srliw d.srliw_input d.r1 d.rd providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `sraiw` step: channel-balance via constructed `OpEnvelope.sraiw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.sraiw`. -/
theorem stepStrong_sraiw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sraiw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sraiw .. => True | _ => False)) :
    execute_instruction
      (instruction.SHIFTIWOP (d.sraiw_input.shamt, d.r1, d.rd, sopw.SRAIW)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i d.h_main_active
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr d.h_main_op)))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
      state d.sraiw_input.r1_val d.sraiw_input.rd d.sraiw_input.PC
      (PureSpec.execute_SHIFTIWOP_sraiw_pure d.sraiw_input).nextPC
      d.r1 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.sraiw_input.r1_val
      d.h_m32 d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_imm_shift_pin_row_of_facts m _ i.val d.sraiw_input.shamt
      d.h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sraiw d.sraiw_input d.r1 d.rd providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2



/-- Strengthened `add` step: channel-balance via a constructed `OpEnvelope` arm
    (`add_via_binary` on the lookup provider, `add_via_binaryadd` on the
    BinaryAdd provider) + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.add`. -/
theorem stepStrong_add
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_add trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val)
      (fun env => match env with
        | .add_via_binary .. => True | .add_via_binaryadd .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.ADD))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨h_add_subset, h_disj⟩ :=
    main_request_add_provided
      trace i d.h_main_active d.h_main_op
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.add_input.r1_val d.add_input.r2_val d.add_input.rd d.add_input.PC
      (PureSpec.execute_RTYPE_add_pure d.add_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  rcases h_disj with h_lookup | h_binaryadd
  · obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_lookup
    let providerInput :=
      ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
        (providerTable.environment providerRow)
    obtain ⟨h_core, h_facts⟩ :=
      ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
        h_component h_table_spec h_provider_row
    have h_static :
        ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
      ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
        h_component h_table_spec h_provider_row
    have h_emit :
        providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
          (ZiskFv.Airs.Tables.BinaryTable.OP_ADD : FGL) := by
      have h_match_op := h_match
      simp only [ZiskFv.Airs.OperationBus.matches_entry,
        ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
      have h_op_match :
          m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD, ZiskFv.Trusted.OP_ADD] using
        d.h_main_op
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_ADD (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_ADD])
        h_core h_emit
    have h_out :=
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
        providerInput h_facts
        ZiskFv.Airs.Tables.BinaryTable.OP_ADD h_core h_row_m32 h_bop
    have h_matches :
        ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
          providerInput ZiskFv.Airs.Tables.BinaryTable.OP_ADD :=
      allByteMatchesOfStaticOut64_local h_out
    have h_input_r1_row :
        d.add_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
        ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
          m providerInput i.val (regidx_to_fin d.r1) d.add_input.r1_val
          h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
    have h_input_r2_row :
        d.add_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
        ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
          m providerInput i.val (regidx_to_fin d.r2) d.add_input.r2_val
          h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
    let env : OpEnvelope state m i.val :=
      OpEnvelope.add_via_binary d.add_input d.r1 d.r2 d.rd bus pins
        providerTable providerRow h_component h_table_spec h_provider_row h_match
        h_input_r1_row h_input_r2_row h_lane_rd promises
    have h_bridge : env.aeneasBridgeTrust := by
      show _ ∧ _
      exact ⟨h_input_r1_row, h_input_r2_row⟩
    have h_mem : env.memoryTimelineConstructionEvidence := by trivial
    have h_known : Defects.NoKnownDefect env :=
      h_known_arm env trivial
    exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.1
  · obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_binaryadd
    let env : OpEnvelope state m i.val :=
      OpEnvelope.add_via_binaryadd d.add_input d.r1 d.r2 d.rd bus pins
        providerTable providerRow h_component h_table_spec h_provider_row h_match
        h_add_subset d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t h_m32_zero
        h_lane_rd promises
    have h_bridge : env.aeneasBridgeTrust := by
      show _ ∧ _ ∧ _ ∧ _ ∧ _
      exact ⟨d.h_a_lo_t, d.h_a_hi_t, d.h_b_lo_t, d.h_b_hi_t, h_m32_zero⟩
    have h_mem : env.memoryTimelineConstructionEvidence := by trivial
    have h_known : Defects.NoKnownDefect env :=
      h_known_arm env trivial
    exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.1

/-- Strengthened `addi` step: channel-balance via a constructed `OpEnvelope` arm
    (`addi_via_binary` / `addi_via_binaryadd`) + `zisk_riscv_compliant_program_bus`.
    Dominates `StepCompliance.addi`. -/
theorem stepStrong_addi
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_addi trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val)
      (fun env => match env with
        | .addi_via_binary .. => True | .addi_via_binaryadd .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ADDI))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨h_add_subset, h_disj⟩ :=
    main_request_add_provided
      trace i d.h_main_active d.h_main_op
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.addi_input.r1_val d.addi_input.imm d.addi_input.rd d.addi_input.PC
      (PureSpec.execute_ITYPE_addi_pure d.addi_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_set_pc_zero : m.set_pc i.val = 0 := d.h_set_pc
  rcases h_disj with h_lookup | h_binaryadd
  · obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_lookup
    let providerInput :=
      ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
        (providerTable.environment providerRow)
    obtain ⟨h_core, h_facts⟩ :=
      ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
        h_component h_table_spec h_provider_row
    have h_static :
        ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
      ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
        h_component h_table_spec h_provider_row
    have h_emit :
        providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
          (ZiskFv.Airs.Tables.BinaryTable.OP_ADD : FGL) := by
      have h_match_op := h_match
      simp only [ZiskFv.Airs.OperationBus.matches_entry,
        ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
      have h_op_match :
          m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD, ZiskFv.Trusted.OP_ADD] using
        d.h_main_op
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_ADD (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_ADD])
        h_core h_emit
    have h_out :=
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
        providerInput h_facts
        ZiskFv.Airs.Tables.BinaryTable.OP_ADD h_core h_row_m32 h_bop
    have h_matches :
        ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
          providerInput ZiskFv.Airs.Tables.BinaryTable.OP_ADD :=
      allByteMatchesOfStaticOut64_local h_out
    have h_input_r1_row :
        d.addi_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
        ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
          m providerInput i.val (regidx_to_fin d.r1) d.addi_input.r1_val
          h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
    have h_input_imm_row :
        BitVec.signExtend 64 d.addi_input.imm
          = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
        ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
          m providerInput i.val d.addi_input.imm h_matches h_m32_zero h_match
          d.h_addi_subset
    let env : OpEnvelope state m i.val :=
      OpEnvelope.addi_via_binary d.addi_input d.r1 d.rd d.imm bus pins
        providerTable providerRow h_component h_table_spec h_provider_row h_match
        d.h_addi_subset h_input_r1_row h_input_imm_row h_lane_rd promises
    have h_bridge : env.aeneasBridgeTrust := by
      show _ ∧ _
      exact ⟨h_input_r1_row, h_input_imm_row⟩
    have h_mem : env.memoryTimelineConstructionEvidence := by trivial
    have h_known : Defects.NoKnownDefect env :=
      h_known_arm env trivial
    exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.1
  · obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_binaryadd
    let env : OpEnvelope state m i.val :=
      OpEnvelope.addi_via_binaryadd d.addi_input d.r1 d.rd d.imm bus pins
        providerTable providerRow h_component h_table_spec h_provider_row h_match
        h_add_subset d.h_addi_subset d.h_a_lo_t d.h_a_hi_t h_m32_zero h_set_pc_zero
        h_lane_rd promises
    have h_bridge : env.aeneasBridgeTrust := by
      show _ ∧ _ ∧ _ ∧ _
      exact ⟨d.h_a_lo_t, d.h_a_hi_t, h_m32_zero, h_set_pc_zero⟩
    have h_mem : env.memoryTimelineConstructionEvidence := by trivial
    have h_known : Defects.NoKnownDefect env :=
      h_known_arm env trivial
    exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.1



end ZiskFv.Compliance
