import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Channels.StateEffect

/-!
# Compliance dispatcher (ADD + RTYPEW arms)

ADD through actual Binary or BinaryAdd rows, plus ADDW and SUBW through
actual Binary rows. The explicit full semantic facts retained by the
envelope feed the existing row-native equivalence proofs directly.

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

def OpEnvelope.exec_eq_add_rtypew
    : OpEnvelope state m r_main → Prop
  | .add_via_binary _ r1 r2 rd bus _ _ _ _ _ _ _ _ _ _ _ =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .add_via_binaryadd _ r1 r2 rd bus _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .addw _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .subw _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_add_rtypew
    (env : OpEnvelope state m r_main) :
    env.exec_eq_add_rtypew := by
  cases env with
  | add_via_binary add_input r1 r2 rd bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises =>
    change execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
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
    exact ZiskFv.EquivCore.Add.equiv_ADD_of_static_row
      state add_input r1 r2 rd m row r_main bus promises
      ⟨h_main_active, h_main_op_add⟩
      h_match_static h_core h_facts h_mode32_zero h_b_op
      h_input_r1_row h_input_r2_row
      h_lane_rd
  | add_via_binaryadd add_input r1 r2 rd bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_binaryadd h_main_subset
      h_a_lo h_a_hi h_b_lo h_b_hi h_m32 h_lane_rd promises =>
    change execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
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
    exact ZiskFv.EquivCore.Add.equiv_ADD_of_binaryadd_row
      state add_input r1 r2 rd m row r_main bus promises pins
      h_match_binaryadd
      (ZiskFv.AirsClean.BinaryAdd.core_every_row_of_component_spec_facts row h_facts)
      h_main_subset h_a_lo h_a_hi h_b_lo h_b_hi h_m32
      (ZiskFv.AirsClean.BinaryAdd.a_chunks_in_range_of_component_spec_facts row h_facts)
      (ZiskFv.AirsClean.BinaryAdd.b_chunks_in_range_of_component_spec_facts row h_facts)
      (ZiskFv.AirsClean.BinaryAdd.c_chunks_in_range_of_component_spec_facts row h_facts)
      h_lane_rd
  | addw addw_input r1 r2 rd _v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static
      h_input_r1_extract h_input_r2_extract h_lane_rd promises =>
    change
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_main_active, h_main_op_addw⟩ := pins
    obtain ⟨h_row_spec, h_spec_facts⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_spec_facts
    have h_emit : row.chain.b_op + 16 * row.mode.mode32 = (0x1A : FGL) := by
      have h_lane_eqs := h_match_static
      simp only [matches_entry, opBus_row_Main,
        ] at h_lane_eqs
      obtain ⟨_, h_op_match, _, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
      rw [← h_op_match]
      simpa [ZiskFv.Trusted.OP_ADD_W] using h_main_op_addw
    obtain ⟨h_mode32_one, h_bop_val⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.chain_row_shape_W_of_emit
        row h_spec_facts h_core 0x1A (Or.inl rfl) h_emit
    have h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD := by
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD] using h_bop_val
    obtain ⟨h_sext_choice_row, h_carry_7_zero_row⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.w_mode_sext_choice_and_carry_7_zero_of_static_row
        row h_spec_facts h_facts h_core h_mode32_one (Or.inl h_b_op)
    exact ZiskFv.EquivCore.Addw.equiv_ADDW_of_static_row
      state addw_input r1 r2 rd m row r_main bus promises
      ⟨h_main_active, h_main_op_addw⟩
      h_match_static h_core h_facts h_mode32_one h_b_op
      h_sext_choice_row h_carry_7_zero_row
      h_input_r1_extract h_input_r2_extract
      h_lane_rd
  | subw subw_input r1 r2 rd _v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static
      h_input_r1_extract h_input_r2_extract h_lane_rd promises =>
    change
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_main_active, h_main_op_subw⟩ := pins
    obtain ⟨h_row_spec, h_spec_facts⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_spec_facts
    have h_emit : row.chain.b_op + 16 * row.mode.mode32 = (0x1B : FGL) := by
      have h_lane_eqs := h_match_static
      simp only [matches_entry, opBus_row_Main,
        ] at h_lane_eqs
      obtain ⟨_, h_op_match, _, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
      rw [← h_op_match]
      simpa [ZiskFv.Trusted.OP_SUB_W] using h_main_op_subw
    obtain ⟨h_mode32_one, h_bop_val⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.chain_row_shape_W_of_emit
        row h_spec_facts h_core 0x1B (Or.inr rfl) h_emit
    have h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB := by
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_SUB] using h_bop_val
    obtain ⟨h_sext_choice_row, h_carry_7_zero_row⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.w_mode_sext_choice_and_carry_7_zero_of_static_row
        row h_spec_facts h_facts h_core h_mode32_one (Or.inr h_b_op)
    exact ZiskFv.EquivCore.Subw.equiv_SUBW_of_static_row
        state subw_input r1 r2 rd m row r_main bus promises
        ⟨h_main_active, h_main_op_subw⟩
        h_match_static h_core h_facts h_mode32_one h_b_op
        h_sext_choice_row h_carry_7_zero_row
        h_input_r1_extract h_input_r2_extract
        h_lane_rd
  | _ => trivial

end ZiskFv.Compliance
