import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Channels.StateEffect

/-!
# Compliance dispatcher (RTYPE+Binary arms)

Extends the dispatcher pattern to the RTYPE+Binary family: SUB, AND,
OR, XOR, SLT, SLTU. The actual consumer row and its retained full semantic
facts feed the existing row-native proofs without a detached provider bundle.

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

/-- The per-arm v2 conclusion Prop for RTYPE+Binary arms.
    Falls through to `True` for non-RTYPE-Binary arms. -/
def OpEnvelope.exec_eq_rtype_binary
    : OpEnvelope state m r_main → Prop
  | .sub _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .and _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.AND))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .or _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.OR))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .xor _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.XOR))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .slt _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sltu _ r1 r2 rd _ bus _ _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

/-- Shared C7 static BinaryTable lookup obligation for RTYPE Binary arms. -/
def OpEnvelope.rtype_binary_logic_static_lookup_soundness
    : OpEnvelope state m r_main → Prop
  | .sub _ _ _ _ v _ _ _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | .and _ _ _ _ v _ _ _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | .or _ _ _ _ v _ _ _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | .xor _ _ _ _ v _ _ _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | .slt _ _ _ _ v _ _ _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | .sltu _ _ _ _ v _ _ _ _ _ _ _ _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
  | _ => True

/-- C7 table-row route for RTYPE bitwise Binary arms.

Unlike `rtype_binary_logic_static_lookup_soundness`, this does not quantify
over a legacy `Valid_Binary` row plus offset. The provider evidence is the
actual Clean Binary consumer row whose explicit full semantic predicate
supplies both the Binary core constraints and all eight BinaryTable facts. -/
def OpEnvelope.rtype_bitwise_static_table_row_route
    : OpEnvelope state m r_main → Prop
  | .sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .and _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .or _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .xor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .slt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .sltu _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | _ => True

/-- Partial v2 dispatcher for RTYPE+Binary arms. -/
theorem zisk_riscv_compliant_program_bus_rtype_binary
    (env : OpEnvelope state m r_main) :
    env.exec_eq_rtype_binary := by
  cases env with
  | sub sub_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_spec_facts⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_spec_facts
    obtain ⟨h_main_active, h_main_op_sub⟩ := pins
    have h_emit : row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_SUB : FGL) := by
      have h_match_op := h_match_static
      simp only [matches_entry, opBus_row_Main] at h_match_op
      have h_op_match :
          m.op r_main = row.chain.b_op + 16 * row.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_SUB, ZiskFv.Trusted.OP_SUB] using
        h_main_op_sub
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        row h_spec_facts ZiskFv.Airs.Tables.BinaryTable.OP_SUB (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_SUB])
        h_core h_emit
    exact ZiskFv.EquivCore.Sub.equiv_SUB_of_static_row
      state sub_input r1 r2 rd m row r_main bus promises
      ⟨h_main_active, h_main_op_sub⟩
      h_match_static h_core h_facts h_row_m32 h_bop
      h_input_r1_row h_input_r2_row h_lane_rd
  | and and_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_input_r1_row h_input_r2_row
      h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_static_specs⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static_specs
    exact ZiskFv.EquivCore.And.equiv_AND_of_static_row
      state and_input r1 r2 rd m row r_main bus promises pins
      h_match_static h_row_spec h_core h_static_specs h_facts
      h_input_r1_row h_input_r2_row h_lane_rd
  | or or_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_input_r1_row h_input_r2_row
      h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_static_specs⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static_specs
    exact ZiskFv.EquivCore.Or.equiv_OR_of_static_row
      state or_input r1 r2 rd m row r_main bus promises pins
      h_match_static h_row_spec h_core h_static_specs h_facts
      h_input_r1_row h_input_r2_row h_lane_rd
  | xor xor_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_input_r1_row h_input_r2_row
      h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_static_specs⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static_specs
    exact ZiskFv.EquivCore.Xor.equiv_XOR_of_static_row
      state xor_input r1 r2 rd m row r_main bus promises pins
      h_match_static h_row_spec h_core h_static_specs h_facts
      h_input_r1_row h_input_r2_row h_lane_rd
  | slt slt_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_input_r1_row h_input_r2_row
      h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_spec_facts⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_spec_facts
    obtain ⟨h_main_active, h_main_op_slt⟩ := pins
    have h_emit : row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
      have h_match_op := h_match_static
      simp only [matches_entry, opBus_row_Main] at h_match_op
      have h_op_match :
          m.op r_main = row.chain.b_op + 16 * row.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
        h_main_op_slt
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        row h_spec_facts ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
        h_core h_emit
    exact ZiskFv.EquivCore.Slt.equiv_SLT_of_static_row
      state slt_input r1 r2 rd m row r_main bus promises
      ⟨h_main_active, h_main_op_slt⟩
      h_match_static h_core h_facts h_row_m32 h_bop
      h_input_r1_row h_input_r2_row h_lane_rd
  | sltu sltu_input r1 r2 rd v bus pins providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static h_input_r1_row h_input_r2_row
      h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_rtype_binary]
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    let row := ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
      (providerTable.environment providerRow)
    obtain ⟨h_row_spec, h_spec_facts⟩ := h_table_spec providerRow h_provider_row
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec row h_row_spec
    have h_facts := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_spec_facts
    obtain ⟨h_main_active, h_main_op_sltu⟩ := pins
    have h_emit : row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
      have h_match_op := h_match_static
      simp only [matches_entry, opBus_row_Main] at h_match_op
      have h_op_match :
          m.op r_main = row.chain.b_op + 16 * row.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU, ZiskFv.Trusted.OP_LTU] using
        h_main_op_sltu
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        row h_spec_facts ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
        h_core h_emit
    exact ZiskFv.EquivCore.Sltu.equiv_SLTU_of_static_row
      state sltu_input r1 r2 rd m row r_main bus promises
      ⟨h_main_active, h_main_op_sltu⟩
      h_match_static h_core h_facts h_row_m32 h_bop
      h_input_r1_row h_input_r2_row h_lane_rd
  | _ => trivial

end ZiskFv.Compliance
