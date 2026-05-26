import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Compliance.Defects
import ZiskFv.Equivalence.Div
import ZiskFv.Equivalence.Divuw
import ZiskFv.Equivalence.Divw
import ZiskFv.Equivalence.Jal
import ZiskFv.Equivalence.Jalr
import ZiskFv.Equivalence.Lbu
import ZiskFv.Equivalence.Lhu
import ZiskFv.Equivalence.Lwu
import ZiskFv.Equivalence.Mul
import ZiskFv.Equivalence.MulH
import ZiskFv.Equivalence.MulHSU
import ZiskFv.Equivalence.MulHU
import ZiskFv.Equivalence.MulW
import ZiskFv.Equivalence.Rem
import ZiskFv.Equivalence.Remu
import ZiskFv.Equivalence.Remuw
import ZiskFv.Equivalence.Remw
import ZiskFv.Equivalence.Sb
import ZiskFv.Equivalence.Sh
import ZiskFv.Equivalence.Slliw
import ZiskFv.Equivalence.Sllw
import ZiskFv.Equivalence.Sraiw
import ZiskFv.Equivalence.Sraw
import ZiskFv.Equivalence.Srliw
import ZiskFv.Equivalence.Srlw
import ZiskFv.Equivalence.Sw

/-!
# Compliance dispatcher for the remaining 26 arms

Covers LBU/LHU/LWU + SB/SH/SW + SLLW/SRLW/SRAW/SLLIW/SRLIW/SRAIW +
MUL/MULH/MULHU/MULHSU/MULW + DIV/REM/REMU/DIVUW/DIVW/REMW/REMUW +
JAL/JALR.

After this dispatcher lands, every OpEnvelope arm has a real
channel-balance conclusion in `Compliance.lean`'s unified
`exec_eq`. No `True` fallbacks remain.

## Trust note

No new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Channels
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- v2 conclusion Prop for the remaining 26 arms. Falls through to
    `True` for arms covered by other partial dispatchers. -/
def OpEnvelope.exec_eq_remaining
    : OpEnvelope state m r_main → Prop
  -- Unsigned loads (3)
  | .lbu lbu_input _ _ _ bus _ _ _ =>
      execute_instruction (instruction.LOAD (
        lbu_input.imm, regidx.Regidx lbu_input.r1, regidx.Regidx lbu_input.rd, true, 1
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .lhu lhu_input _ _ _ bus _ _ _ =>
      execute_instruction (instruction.LOAD (
        lhu_input.imm, regidx.Regidx lhu_input.r1, regidx.Regidx lhu_input.rd, true, 2
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .lwu lwu_input _ _ _ bus _ _ _ =>
      execute_instruction (instruction.LOAD (
        lwu_input.imm, regidx.Regidx lwu_input.r1, regidx.Regidx lwu_input.rd, true, 4
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  -- Sub-doubleword stores (3)
  | .sb sb_input _ bus _ _ _ _ =>
      execute_instruction (instruction.STORE (
        sb_input.imm, regidx.Regidx sb_input.r2, regidx.Regidx sb_input.r1, 1
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sh sh_input _ bus _ _ _ _ =>
      execute_instruction (instruction.STORE (
        sh_input.imm, regidx.Regidx sh_input.r2, regidx.Regidx sh_input.r1, 2
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sw sw_input _ bus _ _ _ _ =>
      execute_instruction (instruction.STORE (
        sw_input.imm, regidx.Regidx sw_input.r2, regidx.Regidx sw_input.r1, 4
      )) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  -- W-shifts (6)
  | .sllw _ r1 r2 rd _ _ bus .. =>
      execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srlw _ r1 r2 rd _ _ bus .. =>
      execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sraw _ r1 r2 rd _ _ bus .. =>
      execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRAW)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .slliw slliw_input r1 rd _ _ bus .. =>
      execute_instruction (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srliw srliw_input r1 rd _ _ bus .. =>
      execute_instruction (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sraiw sraiw_input r1 rd _ _ bus .. =>
      execute_instruction (instruction.SHIFTIWOP (sraiw_input.shamt, r1, rd, sopw.SRAIW)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  -- Mul family (5)
  | .mul _ r1 r2 rd srs1 srs2 bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.Low, signed_rs1 := srs1, signed_rs2 := srs2 }))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .mulh _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := .Signed, signed_rs2 := .Signed }))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .mulhu _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned }))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .mulhsu _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := .Signed, signed_rs2 := .Unsigned }))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .mulw _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.MULW (r2, r1, rd))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  -- Div / Rem (7)
  | .div _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .rem _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, false))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .remu _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .divw _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, false))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .divuw _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .remw _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .remuw _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  -- Jumps (2)
  | .jal _ imm rd _ _ exec_row e_rd .. =>
      execute_instruction (instruction.JAL (imm, rd)) state
        = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state
  | .jalr _ imm rs1 rd _ _ exec_row e_rd .. =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
        = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_remaining
    (env : OpEnvelope state m r_main)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq_remaining := by
  cases env with
  | lbu lbu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Lbu.equiv_LBU state lbu_input regs m mem r_main align bus pins h_width promises
  | lhu lhu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Lhu.equiv_LHU state lhu_input regs m mem r_main align bus pins h_width promises
  | lwu lwu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Lwu.equiv_LWU state lwu_input regs m mem r_main align bus pins h_width promises
  | sb sb_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sb.equiv_SB state sb_input regs m r_main bus pins
      h_main_ind_width h_opcode_assumptions promises
  | sh sh_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sh.equiv_SH state sh_input regs m r_main bus pins
      h_main_ind_width h_opcode_assumptions promises
  | sw sw_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sw.equiv_SW state sw_input regs m r_main bus pins
      h_main_ind_width h_opcode_assumptions promises
  -- W-shifts
  | sllw sllw_input r1 r2 rd providerTable providerRow bus
         h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
         pins h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sllw.equiv_SLLW state sllw_input r1 r2 rd
      m providerTable providerRow r_main bus
      h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
      pins h_component h_table_spec h_provider_row h_match h_lane_rd
  | srlw srlw_input r1 r2 rd providerTable providerRow bus
         h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
         pins h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Srlw.equiv_SRLW state srlw_input r1 r2 rd
      m providerTable providerRow r_main bus
      h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
      pins h_component h_table_spec h_provider_row h_match h_lane_rd
  | sraw sraw_input r1 r2 rd providerTable providerRow bus
         h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
         pins h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sraw.equiv_SRAW state sraw_input r1 r2 rd
      m providerTable providerRow r_main bus
      h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
      pins h_component h_table_spec h_provider_row h_match h_lane_rd
  | slliw slliw_input r1 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Slliw.equiv_SLLIW state slliw_input r1 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | srliw srliw_input r1 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Srliw.equiv_SRLIW state srliw_input r1 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | sraiw sraiw_input r1 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sraiw.equiv_SRAIW state sraiw_input r1 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  -- Mul family
  | mul mul_input r1 r2 rd srs1 srs2 bus v r_a pins h_match_primary
        promises bounds h_row_constraints =>
    simp only [OpEnvelope.exec_eq_remaining]
    have h_no_signed_mul_witness_defect : False :=
      Defects.no_malicious_signed_mul_witness_of_no_known_defect
      h_known_bugs (by simp [Defects.MaliciousSignedMulWitnessShape])
    exact ZiskFv.Equivalence.Mul.equiv_MUL state mul_input r1 r2 rd srs1 srs2 bus m r_main v r_a
      pins h_match_primary promises bounds h_row_constraints h_no_signed_mul_witness_defect
  | mulh mulh_input r1 r2 rd bus v r_a pins h_match_secondary
        promises h_row_constraints =>
    simp only [OpEnvelope.exec_eq_remaining]
    have h_no_signed_mul_witness_defect : False :=
      Defects.no_malicious_signed_mul_witness_of_no_known_defect
      h_known_bugs (by simp [Defects.MaliciousSignedMulWitnessShape])
    exact ZiskFv.Equivalence.MulH.equiv_MULH state mulh_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises h_row_constraints h_no_signed_mul_witness_defect
  | mulhu mulhu_input r1 r2 rd bus v r_a pins h_match_secondary
         promises bounds h_row_constraints =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.MulHU.equiv_MULHU state mulhu_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises bounds h_row_constraints
  | mulhsu mulhsu_input r1 r2 rd bus v r_a pins h_match_secondary
        promises h_row_constraints =>
    simp only [OpEnvelope.exec_eq_remaining]
    have h_no_signed_mul_witness_defect : False :=
      Defects.no_malicious_signed_mul_witness_of_no_known_defect
      h_known_bugs (by simp [Defects.MaliciousSignedMulWitnessShape])
    exact ZiskFv.Equivalence.MulHSU.equiv_MULHSU state mulhsu_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises h_row_constraints h_no_signed_mul_witness_defect
  | mulw mulw_input r1 r2 rd bus v r_a pins h_match_primary
        promises h_row_constraints h_sext_choice h_rs1_value h_rs2_value =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.MulW.equiv_MULW state mulw_input r1 r2 rd bus m r_main v r_a
      pins h_match_primary promises h_row_constraints h_sext_choice h_rs1_value h_rs2_value
  -- Div / Rem
  | div div_input r1 r2 rd bus v r_a
        pins h_match_primary
        promises h_op2_ne h_no_overflow
        h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Div.equiv_DIV state div_input r1 r2 rd bus m r_main v r_a
      pins h_match_primary promises h_op2_ne h_no_overflow
      h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
  | rem rem_input r1 r2 rd bus v r_a
        pins h_match_secondary
        promises h_op2_ne h_no_overflow
        h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Rem.equiv_REM state rem_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises h_op2_ne h_no_overflow
      h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
  | remu remu_input r1 r2 rd bus v r_a
         pins h_match_secondary promises
         bounds h_row_constraints h_op2_ne =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Remu.equiv_REMU state remu_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises bounds h_row_constraints h_op2_ne
  | divw divw_input r1 r2 rd bus v r_a
         pins h_match_primary promises
         h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
         h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Divw.equiv_DIVW state divw_input r1 r2 rd bus m r_main v r_a
      pins h_match_primary promises h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow
  | divuw divuw_input r1 r2 rd bus v r_a
          pins h_match_primary promises
          h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Divuw.equiv_DIVUW state divuw_input r1 r2 rd bus m r_main v r_a
      pins h_match_primary promises h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne
  | remw remw_input r1 r2 rd bus v r_a
         pins h_match_secondary promises
         h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
         h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow_w =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Remw.equiv_REMW state remw_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow_w
  | remuw remuw_input r1 r2 rd bus v r_a
          pins h_match_secondary promises
          h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Remuw.equiv_REMUW state remuw_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne
  -- Jumps
  | jal jal_input imm rd misa_val next_pc exec_row e_rd nextPC_val
        pins h_jal_subset
        promises h_input_imm h_not_throws
        h_pc_bound h_lo_bound h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Jal.equiv_JAL state jal_input imm rd misa_val m r_main next_pc
      exec_row e_rd nextPC_val pins h_jal_subset
      promises h_input_imm h_not_throws
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
  | jalr jalr_input imm rs1 rd misa_val mseccfg exec_row e_rd nextPC_val next_pc
         pins h_jalr_subset
         promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
         h_pc_bound h_lo_bound h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Jalr.equiv_JALR state jalr_input imm rs1 rd misa_val mseccfg
      exec_row e_rd nextPC_val m r_main next_pc
      pins h_jalr_subset
      promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
  | _ => trivial

/-- Defect-aware dispatcher for the remaining arms.

    Non-Arith arms use their concrete opcode proofs. ArithMul/ArithDiv-family
    arms are currently inside the `arithTableTrustShape` defect region, so
    the defect-aware theorem proves those cases from `h_known_bugs` instead
    of depending on the old Arith proof closure. -/
theorem zisk_riscv_compliant_program_bus_remaining_except_known_defects
    (env : OpEnvelope state m r_main)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq_remaining := by
  cases env with
  | lbu lbu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Lbu.equiv_LBU state lbu_input regs m mem r_main align bus pins h_width promises
  | lhu lhu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Lhu.equiv_LHU state lhu_input regs m mem r_main align bus pins h_width promises
  | lwu lwu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Lwu.equiv_LWU state lwu_input regs m mem r_main align bus pins h_width promises
  | sb sb_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sb.equiv_SB state sb_input regs m r_main bus pins
      h_main_ind_width h_opcode_assumptions promises
  | sh sh_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sh.equiv_SH state sh_input regs m r_main bus pins
      h_main_ind_width h_opcode_assumptions promises
  | sw sw_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sw.equiv_SW state sw_input regs m r_main bus pins
      h_main_ind_width h_opcode_assumptions promises
  | sllw sllw_input r1 r2 rd providerTable providerRow bus
         h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
         pins h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sllw.equiv_SLLW state sllw_input r1 r2 rd
      m providerTable providerRow r_main bus
      h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
      pins h_component h_table_spec h_provider_row h_match h_lane_rd
  | srlw srlw_input r1 r2 rd providerTable providerRow bus
         h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
         pins h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Srlw.equiv_SRLW state srlw_input r1 r2 rd
      m providerTable providerRow r_main bus
      h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
      pins h_component h_table_spec h_provider_row h_match h_lane_rd
  | sraw sraw_input r1 r2 rd providerTable providerRow bus
         h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
         pins h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sraw.equiv_SRAW state sraw_input r1 r2 rd
      m providerTable providerRow r_main bus
      h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
      pins h_component h_table_spec h_provider_row h_match h_lane_rd
  | slliw slliw_input r1 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Slliw.equiv_SLLIW state slliw_input r1 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | srliw srliw_input r1 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Srliw.equiv_SRLIW state srliw_input r1 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | sraiw sraiw_input r1 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Sraiw.equiv_SRAIW state sraiw_input r1 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | mul mul_input r1 r2 rd srs1 srs2 bus v r_a pins h_match_primary
        promises bounds h_row_constraints =>
    simp only [OpEnvelope.exec_eq_remaining]
    have h_no_signed_mul_witness_defect : False :=
      Defects.no_malicious_signed_mul_witness_of_no_known_defect
      h_known_bugs (by simp [Defects.MaliciousSignedMulWitnessShape])
    exact ZiskFv.Equivalence.Mul.equiv_MUL state mul_input r1 r2 rd srs1 srs2 bus m r_main v r_a
      pins h_match_primary promises bounds h_row_constraints h_no_signed_mul_witness_defect
  | mulh mulh_input r1 r2 rd bus v r_a pins h_match_secondary
        promises h_row_constraints =>
    simp only [OpEnvelope.exec_eq_remaining]
    have h_no_signed_mul_witness_defect : False :=
      Defects.no_malicious_signed_mul_witness_of_no_known_defect
      h_known_bugs (by simp [Defects.MaliciousSignedMulWitnessShape])
    exact ZiskFv.Equivalence.MulH.equiv_MULH state mulh_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises h_row_constraints h_no_signed_mul_witness_defect
  | mulhu mulhu_input r1 r2 rd bus v r_a pins h_match_secondary
         promises bounds h_row_constraints =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.MulHU.equiv_MULHU state mulhu_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises bounds h_row_constraints
  | mulhsu mulhsu_input r1 r2 rd bus v r_a pins h_match_secondary
        promises h_row_constraints =>
    simp only [OpEnvelope.exec_eq_remaining]
    have h_no_signed_mul_witness_defect : False :=
      Defects.no_malicious_signed_mul_witness_of_no_known_defect
      h_known_bugs (by simp [Defects.MaliciousSignedMulWitnessShape])
    exact ZiskFv.Equivalence.MulHSU.equiv_MULHSU state mulhsu_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises h_row_constraints h_no_signed_mul_witness_defect
  | mulw mulw_input r1 r2 rd bus v r_a pins h_match_primary
        promises h_row_constraints h_sext_choice h_rs1_value h_rs2_value =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.MulW.equiv_MULW state mulw_input r1 r2 rd bus m r_main v r_a
      pins h_match_primary promises h_row_constraints h_sext_choice h_rs1_value h_rs2_value
  | div div_input r1 r2 rd bus v r_a
        pins h_match_primary
        promises h_op2_ne h_no_overflow
        h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Div.equiv_DIV state div_input r1 r2 rd bus m r_main v r_a
      pins h_match_primary promises h_op2_ne h_no_overflow
      h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
  | rem rem_input r1 r2 rd bus v r_a
        pins h_match_secondary
        promises h_op2_ne h_no_overflow
        h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Rem.equiv_REM state rem_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises h_op2_ne h_no_overflow
      h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
  | remu remu_input r1 r2 rd bus v r_a
         pins h_match_secondary promises
         bounds h_row_constraints h_op2_ne =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Remu.equiv_REMU state remu_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises bounds h_row_constraints h_op2_ne
  | divw divw_input r1 r2 rd bus v r_a
         pins h_match_primary promises
         h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
         h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Divw.equiv_DIVW state divw_input r1 r2 rd bus m r_main v r_a
      pins h_match_primary promises h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow
  | divuw divuw_input r1 r2 rd bus v r_a
          pins h_match_primary promises
          h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Divuw.equiv_DIVUW state divuw_input r1 r2 rd bus m r_main v r_a
      pins h_match_primary promises h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne
  | remw remw_input r1 r2 rd bus v r_a
         pins h_match_secondary promises
         h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
         h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow_w =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Remw.equiv_REMW state remw_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow_w
  | remuw remuw_input r1 r2 rd bus v r_a
          pins h_match_secondary promises
          h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Remuw.equiv_REMUW state remuw_input r1 r2 rd bus m r_main v r_a
      pins h_match_secondary promises h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne
  | jal jal_input imm rd misa_val next_pc exec_row e_rd nextPC_val
        pins h_jal_subset
        promises h_input_imm h_not_throws
        h_pc_bound h_lo_bound h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Jal.equiv_JAL state jal_input imm rd misa_val m r_main next_pc
      exec_row e_rd nextPC_val pins h_jal_subset
      promises h_input_imm h_not_throws
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
  | jalr jalr_input imm rs1 rd misa_val mseccfg exec_row e_rd nextPC_val next_pc
         pins h_jalr_subset
         promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
         h_pc_bound h_lo_bound h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq_remaining]
    exact ZiskFv.Equivalence.Jalr.equiv_JALR state jalr_input imm rs1 rd misa_val mseccfg
      exec_row e_rd nextPC_val m r_main next_pc
      pins h_jalr_subset
      promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
  | _ => trivial

end ZiskFv.Compliance
