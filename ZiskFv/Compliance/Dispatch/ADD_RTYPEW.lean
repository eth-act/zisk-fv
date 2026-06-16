import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Equivalence.Add
import ZiskFv.Equivalence.Addw
import ZiskFv.Equivalence.Subw

/-!
# Compliance dispatcher (ADD + RTYPEW arms)

ADD (RTYPE via Binary lookup) plus ADDW, SUBW (RTYPEW+Binary).
Post-T4-purge: `.add` constructor is the Binary-arm one (legacy
BinaryAdd-arm retired).

## Trust note

No new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Channels
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
    exact ZiskFv.Equivalence.Add.equiv_ADD
      state add_input r1 r2 rd m providerTable providerRow r_main bus pins
      h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises
  | add_via_binaryadd add_input r1 r2 rd bus pins providerTable providerRow
      h_component h_table_spec h_provider_row h_match_binaryadd h_main_subset
      h_a_lo_t h_a_hi_t h_b_lo_t h_b_hi_t h_m32 h_lane_rd promises =>
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
      h_main_subset h_a_lo_t h_a_hi_t h_b_lo_t h_b_hi_t h_m32
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
    exact ZiskFv.Equivalence.Addw.equiv_ADDW
      state addw_input r1 r2 rd m providerTable providerRow r_main bus pins
      h_component h_table_spec h_provider_row h_match_static
      h_input_r1_extract h_input_r2_extract h_lane_rd promises
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
    exact ZiskFv.Equivalence.Subw.equiv_SUBW
      state subw_input r1 r2 rd m providerTable providerRow r_main bus pins
      h_component h_table_spec h_provider_row h_match_static
      h_input_r1_extract h_input_r2_extract h_lane_rd promises
  | _ => trivial

end ZiskFv.Compliance
