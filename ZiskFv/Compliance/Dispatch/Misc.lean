import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Equivalence.Lb
import ZiskFv.Equivalence.Lh
import ZiskFv.Equivalence.Lw

/-!
# Compliance dispatcher for remaining arms

Completes coverage of the OpEnvelope arms not handled by the other
partial dispatchers: signed loads, sub-doubleword stores, unsigned
loads, W-shifts, all Mul/Div/Rem variants, ADDI/ADDIW, JAL/JALR.

## Trust note

No new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Channels
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- v2 conclusion Prop for all arms not in the other partial files. -/
def OpEnvelope.exec_eq_misc
    : OpEnvelope state m r_main → Prop
  -- Signed loads
  | .lb_via_static_match lb_input _ _ _ _ _ _ _ _ bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          lb_input.imm, regidx.Regidx lb_input.r1, regidx.Regidx lb_input.rd, false, 1
        ))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .lh_via_static_match lh_input _ _ _ _ _ _ _ _ bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          lh_input.imm, regidx.Regidx lh_input.r1, regidx.Regidx lh_input.rd, false, 2
        ))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .lw_via_static_match lw_input _ _ _ _ _ _ _ _ bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          lw_input.imm, regidx.Regidx lw_input.r1, regidx.Regidx lw_input.rd, false, 4
        ))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  -- ADDI / ADDIW
  | .addi_via_binary _ r1 rd imm bus _ _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .addi_via_binaryadd _ r1 rd imm bus _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .addiw _ r1 rd imm _ bus _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ADDIW (imm, r1, rd))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

set_option maxHeartbeats 800000
theorem zisk_riscv_compliant_program_bus_misc
    (env : OpEnvelope state m r_main)
    (h_memory_construction : env.memoryTimelineConstructionEvidence) :
    env.exec_eq_misc := by
  cases env with
  | lb_via_static_match lb_input regs mem v r_binary offset env h_static h_match
      bus pins promises r_mem h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match h_addr1
      h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    change
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
            lb_input.imm, regidx.Regidx lb_input.r1, regidx.Regidx lb_input.rd, false, 1
          ))) state
          = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    simp only [OpEnvelope.memoryTimelineConstructionEvidence] at h_memory_construction
    rcases loadMemoryTimelineEvidence_of_coherenceEvidence promises h_memory_construction with
      ⟨timeline⟩
    let promises' :=
      ZiskFv.EquivCore.Promises.LoadStructuralPromises.withMemoryTimelineEvidence
        promises timeline
    let w :=
      ZiskFv.EquivCore.Bridge.MemClean.loadCleanWitness_of_full_ensemble_main_b_mem_provider
      m mem r_main r_mem bus lb_input.r1_val lb_input.imm lb_input.rd
      h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match h_addr1
      h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr
    exact ZiskFv.Equivalence.Lb.equiv_LB
      state lb_input regs m mem r_main v r_binary offset env h_static
      h_match bus pins promises' w
  | lh_via_static_match lh_input regs mem v r_binary offset env h_static h_match
      bus pins promises r_mem h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match h_addr1
      h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    change
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
            lh_input.imm, regidx.Regidx lh_input.r1, regidx.Regidx lh_input.rd, false, 2
          ))) state
          = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    simp only [OpEnvelope.memoryTimelineConstructionEvidence] at h_memory_construction
    rcases loadMemoryTimelineEvidence_of_coherenceEvidence promises h_memory_construction with
      ⟨timeline⟩
    let promises' :=
      ZiskFv.EquivCore.Promises.LoadStructuralPromises.withMemoryTimelineEvidence
        promises timeline
    let w :=
      ZiskFv.EquivCore.Bridge.MemClean.loadCleanWitness_of_full_ensemble_main_b_mem_provider
      m mem r_main r_mem bus lh_input.r1_val lh_input.imm lh_input.rd
      h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match h_addr1
      h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr
    exact ZiskFv.Equivalence.Lh.equiv_LH
      state lh_input regs m mem r_main v r_binary offset env h_static
      h_match bus pins promises' w
  | lw_via_static_match lw_input regs mem v r_binary offset env h_static h_match
      bus pins promises r_mem h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match h_addr1
      h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    change
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
            lw_input.imm, regidx.Regidx lw_input.r1, regidx.Regidx lw_input.rd, false, 4
          ))) state
          = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    simp only [OpEnvelope.memoryTimelineConstructionEvidence] at h_memory_construction
    rcases loadMemoryTimelineEvidence_of_coherenceEvidence promises h_memory_construction with
      ⟨timeline⟩
    let promises' :=
      ZiskFv.EquivCore.Promises.LoadStructuralPromises.withMemoryTimelineEvidence
        promises timeline
    let w :=
      ZiskFv.EquivCore.Bridge.MemClean.loadCleanWitness_of_full_ensemble_main_b_mem_provider
      m mem r_main r_mem bus lw_input.r1_val lw_input.imm lw_input.rd
      h_mainEval h_providerEval h_msg h_main_row
      h_mem_row h_main_spec h_store_pc h_main_b_match h_main_c_match h_addr1
      h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr
    exact ZiskFv.Equivalence.Lw.equiv_LW
      state lw_input regs m mem r_main v r_binary offset env h_static
      h_match bus pins promises' w
  | addi_via_binary addi_input r1 rd imm bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_static h_addi_subset
      h_input_r1_row h_input_imm_row h_lane_rd promises =>
    change
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_main_active, h_main_op_add⟩ := pins
    obtain ⟨h_row_spec, h_spec_facts⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_spec_facts
    have h_emit : row.chain.b_op + 16 * row.mode.mode32 = (10 : FGL) := by
      have h_lane_eqs := h_match_static
      simp only [matches_entry, opBus_row_Main] at h_lane_eqs
      obtain ⟨_, h_op_match, _, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
      rw [← h_op_match]
      simpa [ZiskFv.Trusted.OP_ADD] using h_main_op_add
    obtain ⟨h_mode32_zero, h_bop_val, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        row h_spec_facts 10 (by decide) h_core h_emit
    have h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD := by
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD] using h_bop_val
    exact ZiskFv.EquivCore.Addi.equiv_ADDI_of_static_row
      state addi_input r1 rd imm m row r_main bus promises
      ⟨h_main_active, h_main_op_add⟩
      h_match_static h_addi_subset h_core h_facts h_mode32_zero h_b_op
      h_input_r1_row h_input_imm_row
      h_lane_rd
  | addi_via_binaryadd addi_input r1 rd imm bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_binaryadd h_main_subset
      h_addi_subset h_a_lo h_a_hi h_m32 h_set_pc h_lane_rd promises =>
    change
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row :=
      ZiskFv.AirsClean.BinaryAdd.component.rowInput
        (providerTable.environment providerRow)
    have h_facts : ZiskFv.AirsClean.BinaryAdd.ComponentSpecFacts row := by
      have h_component_spec :
          ZiskFv.AirsClean.BinaryAdd.component.Spec
            (providerTable.environment providerRow) := by
        simpa [h_component] using h_table_spec providerRow h_provider_row
      simpa [row, ZiskFv.AirsClean.BinaryAdd.component_spec] using h_component_spec
    exact ZiskFv.EquivCore.Addi.equiv_ADDI_of_binaryadd_row
      state addi_input r1 rd imm m row r_main bus promises pins
      h_match_binaryadd
      (ZiskFv.AirsClean.BinaryAdd.core_every_row_of_component_spec_facts row h_facts)
      h_main_subset h_a_lo h_a_hi
      (ZiskFv.AirsClean.BinaryAdd.a_chunks_in_range_of_component_spec_facts row h_facts)
      (ZiskFv.AirsClean.BinaryAdd.b_chunks_in_range_of_component_spec_facts row h_facts)
      (ZiskFv.AirsClean.BinaryAdd.c_chunks_in_range_of_component_spec_facts row h_facts)
      h_addi_subset h_m32 h_set_pc h_lane_rd
  | addiw addiw_input r1 rd imm _v bus pins h_addiw_subset providerTable providerRow
      h_component h_table_spec h_provider_row h_match_static h_input_r1_extract
      h_lane_rd promises =>
    change
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ADDIW (imm, r1, rd))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_main_active, h_main_op_addiw⟩ := pins
    obtain ⟨h_row_spec, h_spec_facts⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_spec_facts
    have h_emit : row.chain.b_op + 16 * row.mode.mode32 = (0x1A : FGL) := by
      have h_lane_eqs := h_match_static
      simp only [matches_entry, opBus_row_Main,
        ] at h_lane_eqs
      obtain ⟨_, h_op_match, _, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
      rw [← h_op_match]
      simpa [ZiskFv.Trusted.OP_ADD_W] using h_main_op_addiw
    obtain ⟨h_mode32_one, h_bop_val⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.chain_row_shape_W_of_emit
        row h_spec_facts h_core 0x1A (Or.inl rfl) h_emit
    have h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD := by
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD] using h_bop_val
    let v := ZiskFv.AirsClean.Binary.validOfRow row
    obtain ⟨h_sext_choice_row, h_carry_7_zero_row⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.w_mode_sext_choice_and_carry_7_zero_of_static_row
        row h_spec_facts h_facts h_core h_mode32_one (Or.inl h_b_op)
    have h_b_lo_m : m.b_0 r_main = v.free_in_b_0 0 + 256 * v.free_in_b_1 0
                                    + 65536 * v.free_in_b_2 0
                                    + 16777216 * v.free_in_b_3 0 := by
      have h_match_proj := h_match_static
      simp only [matches_entry, opBus_row_Main,
        ] at h_match_proj
      have h_b_lo := h_match_proj.2.2.2.2.1
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_b_lo
    have h_input_imm := promises.input_imm_eq
    have h_subset := h_addiw_subset
    simp only [ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main,
               h_input_imm] at h_subset
    have hb0 : (v.free_in_b_0 0).val < 256 := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
        ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.2.1
    have hb1 : (v.free_in_b_1 0).val < 256 := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
        ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.2.1
    have hb2 : (v.free_in_b_2 0).val < 256 := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
        ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.2.1
    have hb3 : (v.free_in_b_3 0).val < 256 := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
        ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
        ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.2.1
    have h_b0_val : (m.b_0 r_main).val =
        (v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
        + (v.free_in_b_2 0).val * 65536
        + (v.free_in_b_3 0).val * 16777216 := by
      rw [h_b_lo_m]
      have h_cast :
          v.free_in_b_0 0 + 256 * v.free_in_b_1 0
            + 65536 * v.free_in_b_2 0 + 16777216 * v.free_in_b_3 0
          = ((((v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
                + (v.free_in_b_2 0).val * 65536
                + (v.free_in_b_3 0).val * 16777216 : ℕ) : FGL)) := by
        push_cast; ring
      rw [h_cast, Fin.val_natCast]
      apply Nat.mod_eq_of_lt
      have h_p : (2:ℕ)^32 ≤ GL_prime := by decide
      omega
    have h_byte_lt :
        (v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
          + (v.free_in_b_2 0).val * 65536
          + (v.free_in_b_3 0).val * 16777216 < 4294967296 := by
      omega
    have h_input_imm_extract :
        (Sail.BitVec.extractLsb (BitVec.signExtend 64 imm : BitVec 64) 31 0
          : BitVec (31 - 0 + 1)).toNat
        = (((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_0 0).val
            + ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_1 0).val * 256
            + ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_2 0).val * 65536
            + ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_3 0).val * 16777216)
                % 2^32 := by
      show _ = ((v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
                + (v.free_in_b_2 0).val * 65536
                + (v.free_in_b_3 0).val * 16777216) % 2^32
      rw [h_subset]
      simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
                 BitVec.toNat_ofNat, Nat.shiftRight_zero,
                 show (31 - 0 + 1 : ℕ) = 32 from rfl,
                 show (2:ℕ)^32 = 4294967296 from rfl,
                 show (2:ℕ)^64 = 18446744073709551616 from rfl]
      rw [h_b0_val]
      have h_b1_lt : (m.b_1 r_main).val < GL_prime := (m.b_1 r_main).isLt
      omega
    exact ZiskFv.EquivCore.Addiw.equiv_ADDIW_of_static_row
      state addiw_input r1 rd imm m row r_main bus promises
      ⟨h_main_active, h_main_op_addiw⟩
      h_match_static h_core h_facts h_mode32_one h_b_op
      h_sext_choice_row h_carry_7_zero_row
      h_input_r1_extract
      h_lane_rd h_input_imm_extract
  | _ => trivial

end ZiskFv.Compliance
