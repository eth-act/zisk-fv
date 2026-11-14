import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Channels.StateEffect

/-!
# Compliance dispatcher (Shift arms)

Extends to the 6 shift arms (SLL, SRL, SRA, SLLI, SRLI, SRAI) which
pair with the BinaryExtension AIR.

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

def OpEnvelope.exec_eq_shift
    : OpEnvelope state m r_main → Prop
  | .sll sll_input r1 r2 rd providerTable providerRow bus .. =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srl srl_input r1 r2 rd providerTable providerRow bus .. =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sra sra_input r1 r2 rd providerTable providerRow bus .. =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .slli slli_input r1 rd shamt providerTable providerRow bus .. =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srli srli_input r1 rd shamt providerTable providerRow bus .. =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srai srai_input r1 rd shamt providerTable providerRow bus .. =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_shift
    (env : OpEnvelope state m r_main) :
    env.exec_eq_shift := by
  cases env with
  | sll sll_input r1 r2 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd =>
    change execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    have h_facts := ZiskFv.AirsClean.BinaryExtension.static_table_wf_facts_of_spec_facts row
      (h_table_spec providerRow h_provider_row).2.1
    have h_b0_range := (h_table_spec providerRow h_provider_row).2.2
    exact ZiskFv.EquivCore.Sll.equiv_SLL_of_static_row state sll_input r1 r2 rd
      m row r_main bus promises pins h_match h_facts
      h_input_r1_row h_shift_pin_row h_b0_range h_lane_rd
  | srl srl_input r1 r2 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd =>
    change execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    have h_facts := ZiskFv.AirsClean.BinaryExtension.static_table_wf_facts_of_spec_facts row
      (h_table_spec providerRow h_provider_row).2.1
    have h_b0_range := (h_table_spec providerRow h_provider_row).2.2
    exact ZiskFv.EquivCore.Srl.equiv_SRL_of_static_row state srl_input r1 r2 rd
      m row r_main bus promises pins h_match h_facts
      h_input_r1_row h_shift_pin_row h_b0_range h_lane_rd
  | sra sra_input r1 r2 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd =>
    change execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    have h_facts := ZiskFv.AirsClean.BinaryExtension.static_table_wf_facts_of_spec_facts row
      (h_table_spec providerRow h_provider_row).2.1
    have h_b0_range := (h_table_spec providerRow h_provider_row).2.2
    exact ZiskFv.EquivCore.Sra.equiv_SRA_of_static_row state sra_input r1 r2 rd
      m row r_main bus promises pins h_match h_facts
      h_input_r1_row h_shift_pin_row h_b0_range h_lane_rd
  | slli slli_input r1 rd shamt providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd =>
    change execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    have h_facts := ZiskFv.AirsClean.BinaryExtension.static_table_wf_facts_of_spec_facts row
      (h_table_spec providerRow h_provider_row).2.1
    have h_b0_range := (h_table_spec providerRow h_provider_row).2.2
    exact ZiskFv.EquivCore.Slli.equiv_SLLI_of_static_row state slli_input r1 rd shamt
      m row r_main bus promises pins h_match h_facts h_b0_range
      h_input_r1_row h_shift_pin_row h_lane_rd
  | srli srli_input r1 rd shamt providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd =>
    change execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    have h_facts := ZiskFv.AirsClean.BinaryExtension.static_table_wf_facts_of_spec_facts row
      (h_table_spec providerRow h_provider_row).2.1
    have h_b0_range := (h_table_spec providerRow h_provider_row).2.2
    exact ZiskFv.EquivCore.Srli.equiv_SRLI_of_static_row state srli_input r1 rd shamt
      m row r_main bus promises pins h_match h_facts h_b0_range
      h_input_r1_row h_shift_pin_row h_lane_rd
  | srai srai_input r1 rd shamt providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd =>
    change execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.BinaryExtension.shiftTableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    have h_facts := ZiskFv.AirsClean.BinaryExtension.static_table_wf_facts_of_spec_facts row
      (h_table_spec providerRow h_provider_row).2.1
    have h_b0_range := (h_table_spec providerRow h_provider_row).2.2
    exact ZiskFv.EquivCore.Srai.equiv_SRAI_of_static_row state srai_input r1 rd shamt
      m row r_main bus promises pins h_match h_facts h_b0_range
      h_input_r1_row h_shift_pin_row h_lane_rd
  | _ => trivial

end ZiskFv.Compliance
