import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Channels.StateEffect

/-!
# Compliance dispatcher (ITYPE+Binary arms)

Extends to ITYPE+Binary: ANDI, ORI, XORI, SLTI, SLTIU.

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

def OpEnvelope.exec_eq_itype_binary
    : OpEnvelope state m r_main → Prop
  | .andi _ r1 rd imm _ bus _ _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .ori _ r1 rd imm _ bus _ _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .xori _ r1 rd imm _ bus _ _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .slti _ r1 rd imm _ bus _ _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sltiu _ r1 rd imm _ bus _ _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_itype_binary
    (env : OpEnvelope state m r_main) :
    env.exec_eq_itype_binary := by
  cases env with
  | andi andi_input r1 rd imm v bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_imm_row h_andi_subset
      h_lane_rd promises =>
    change
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_static_specs⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static_specs
    exact ZiskFv.EquivCore.Andi.equiv_ANDI_of_static_row
      state andi_input r1 rd imm m row r_main bus promises pins
      h_match_static h_row_spec h_core h_static_specs h_facts
      h_input_r1_row h_input_imm_row
      h_lane_rd h_andi_subset
  | ori ori_input r1 rd imm v bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_imm_row h_ori_subset
      h_lane_rd promises =>
    change
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_static_specs⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static_specs
    exact ZiskFv.EquivCore.Ori.equiv_ORI_of_static_row
      state ori_input r1 rd imm m row r_main bus promises pins
      h_match_static h_row_spec h_core h_static_specs h_facts
      h_input_r1_row h_input_imm_row
      h_lane_rd h_ori_subset
  | xori xori_input r1 rd imm v bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_imm_row h_xori_subset
      h_lane_rd promises =>
    change
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_static_specs⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static_specs
    exact ZiskFv.EquivCore.Xori.equiv_XORI_of_static_row
      state xori_input r1 rd imm m row r_main bus promises pins
      h_match_static h_row_spec h_core h_static_specs h_facts
      h_input_r1_row h_input_imm_row
      h_lane_rd h_xori_subset
  | slti slti_input r1 rd imm v bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_static
      h_main_m32 h_input_r1_row h_slti_subset h_lane_rd promises =>
    change
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_spec_facts⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_spec_facts
    obtain ⟨h_main_active, h_main_op_slti⟩ := pins
    have h_emit : row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
      have h_match_op := h_match_static
      simp only [matches_entry, opBus_row_Main] at h_match_op
      have h_op_match :
          m.op r_main = row.chain.b_op + 16 * row.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
        h_main_op_slti
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        row h_spec_facts ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
        h_core h_emit
    let v := ZiskFv.AirsClean.Binary.validOfRow row
    have h_match_v : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v 0) := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
        ZiskFv.AirsClean.Binary.opBusMessage,
        ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
        opBus_row_Binary] using h_match_static
    have h_row_m32_v : v.mode32 0 = 0 := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_row_m32
    have h_bop_v : (v.b_op 0).val = ZiskFv.Airs.Tables.BinaryTable.OP_LT := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_bop
    have h_bop_or_sext : row.chain.b_op_or_sext.val =
        ZiskFv.Airs.Tables.BinaryTable.OP_LT := by
      have h :=
        ZiskFv.EquivCore.Bridge.Binary.b_op_or_sext_val_eq_of_mode32_zero
          v 0 ZiskFv.Airs.Tables.BinaryTable.OP_LT h_core h_row_m32_v h_bop_v
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h
    have h_matches :=
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
        row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_LT h_bop h_bop_or_sext
    have h_input_imm_v :=
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m row r_main slti_input.imm h_matches h_main_m32 h_match_static h_slti_subset
    have h_input_imm_row : BitVec.signExtend 64 slti_input.imm
        = BitVec.ofNat 64
            ((row.bBytes.free_in_b_0).val
              + (row.bBytes.free_in_b_1).val * 256
              + (row.bBytes.free_in_b_2).val * 65536
              + (row.bBytes.free_in_b_3).val * 16777216
              + (row.bBytes.free_in_b_4).val * 4294967296
              + (row.bBytes.free_in_b_5).val * 1099511627776
              + (row.bBytes.free_in_b_6).val * 281474976710656
              + (row.bBytes.free_in_b_7).val * 72057594037927936) := by
      exact h_input_imm_v
    exact ZiskFv.EquivCore.Slti.equiv_SLTI_of_static_row
      state slti_input r1 rd imm m row r_main bus promises
      ⟨h_main_active, h_main_op_slti⟩
      h_match_static h_core h_facts h_row_m32 h_bop
      h_input_r1_row
      h_lane_rd h_input_imm_row
  | sltiu sltiu_input r1 rd imm v bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_static
      h_main_m32 h_input_r1_row h_sltiu_subset h_lane_rd promises =>
    change
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_spec_facts⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_spec_facts
    obtain ⟨h_main_active, h_main_op_sltiu⟩ := pins
    have h_emit : row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
      have h_match_op := h_match_static
      simp only [matches_entry, opBus_row_Main] at h_match_op
      have h_op_match :
          m.op r_main = row.chain.b_op + 16 * row.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU, ZiskFv.Trusted.OP_LTU] using
        h_main_op_sltiu
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        row h_spec_facts ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
        h_core h_emit
    let v := ZiskFv.AirsClean.Binary.validOfRow row
    have h_match_v : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v 0) := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
        ZiskFv.AirsClean.Binary.opBusMessage,
        ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
        opBus_row_Binary] using h_match_static
    have h_row_m32_v : v.mode32 0 = 0 := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_row_m32
    have h_bop_v : (v.b_op 0).val = ZiskFv.Airs.Tables.BinaryTable.OP_LTU := by
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_bop
    have h_bop_or_sext : row.chain.b_op_or_sext.val =
        ZiskFv.Airs.Tables.BinaryTable.OP_LTU := by
      have h :=
        ZiskFv.EquivCore.Bridge.Binary.b_op_or_sext_val_eq_of_mode32_zero
          v 0 ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_row_m32_v h_bop_v
      simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h
    have h_matches :=
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
        row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_bop h_bop_or_sext
    have h_input_imm_v :=
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m row r_main sltiu_input.imm h_matches h_main_m32 h_match_static h_sltiu_subset
    have h_input_imm_row : BitVec.signExtend 64 sltiu_input.imm
        = BitVec.ofNat 64
            ((row.bBytes.free_in_b_0).val
              + (row.bBytes.free_in_b_1).val * 256
              + (row.bBytes.free_in_b_2).val * 65536
              + (row.bBytes.free_in_b_3).val * 16777216
              + (row.bBytes.free_in_b_4).val * 4294967296
              + (row.bBytes.free_in_b_5).val * 1099511627776
              + (row.bBytes.free_in_b_6).val * 281474976710656
              + (row.bBytes.free_in_b_7).val * 72057594037927936) := by
      exact h_input_imm_v
    exact ZiskFv.EquivCore.Sltiu.equiv_SLTIU_of_static_row
      state sltiu_input r1 rd imm m row r_main bus promises
      ⟨h_main_active, h_main_op_sltiu⟩
      h_match_static h_core h_facts h_row_m32 h_bop
      h_input_r1_row
      h_lane_rd h_input_imm_row
  | _ => trivial

end ZiskFv.Compliance
