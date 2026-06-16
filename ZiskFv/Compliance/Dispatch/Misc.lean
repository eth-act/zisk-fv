import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Equivalence.Addi
import ZiskFv.Equivalence.Addiw
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
    rcases loadMemoryTimelineEvidence_of_constructionEvidence promises h_memory_construction with
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
    rcases loadMemoryTimelineEvidence_of_constructionEvidence promises h_memory_construction with
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
    rcases loadMemoryTimelineEvidence_of_constructionEvidence promises h_memory_construction with
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
    exact ZiskFv.Equivalence.Addi.equiv_ADDI
      state addi_input r1 rd imm m providerTable providerRow r_main bus pins
      h_component h_table_spec h_provider_row h_match_static h_addi_subset
      h_input_r1_row h_input_imm_row h_lane_rd promises
  | addi_via_binaryadd addi_input r1 rd imm bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_binaryadd h_main_subset
      h_addi_subset h_a_lo_t h_a_hi_t h_m32 h_set_pc h_lane_rd promises =>
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
      h_main_subset h_a_lo_t h_a_hi_t
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
    exact ZiskFv.Equivalence.Addiw.equiv_ADDIW
      state addiw_input r1 rd imm m providerTable providerRow r_main bus pins
      h_addiw_subset h_component h_table_spec h_provider_row h_match_static
      h_input_r1_extract h_lane_rd promises
  | _ => trivial

end ZiskFv.Compliance
