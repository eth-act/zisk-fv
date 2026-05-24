import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Equivalence.Andi
import ZiskFv.Equivalence.Ori
import ZiskFv.Equivalence.Slti
import ZiskFv.Equivalence.Sltiu
import ZiskFv.Equivalence.Xori

/-!
# Compliance dispatcher (ITYPE+Binary arms)

Extends to ITYPE+Binary: ANDI, ORI, XORI, SLTI, SLTIU.

## Trust note

No new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Channels
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

def OpEnvelope.exec_eq_itype_binary
    : OpEnvelope state m r_main → Prop
  | .andi _ r1 rd imm _ bus _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .ori _ r1 rd imm _ bus _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .xori _ r1 rd imm _ bus _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .slti _ r1 rd imm _ bus _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sltiu _ r1 rd imm _ bus _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
        = state_effect_via_channels
            ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

/-- Shared C7 static BinaryTable lookup obligation for ITYPE Binary arms.
    Bitwise rows need static lookup + Binary core facts. Compare rows also
    expose the remaining 64-bit row-shape pin explicitly. -/
def OpEnvelope.itype_binary_logic_static_lookup_soundness
    : OpEnvelope state m r_main → Prop
  | .andi _ _ _ _ v _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
        ∧ ∀ r, ZiskFv.Airs.Binary.core_every_row v r
  | .ori _ _ _ _ v _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
        ∧ ∀ r, ZiskFv.Airs.Binary.core_every_row v r
  | .xori _ _ _ _ v _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
        ∧ ∀ r, ZiskFv.Airs.Binary.core_every_row v r
  | .slti _ _ _ _ v _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
        ∧ ∀ r, ZiskFv.Airs.Binary.core_every_row v r
          ∧ v.mode32 r = 0
          ∧ (v.b_op r).val = ZiskFv.Airs.Tables.BinaryTable.OP_LT
  | .sltiu _ _ _ _ v _ _ _ _ _ =>
      ZiskFv.AirsClean.Binary.StaticLookupSoundness v
        ∧ ∀ r, ZiskFv.Airs.Binary.core_every_row v r
          ∧ v.mode32 r = 0
          ∧ (v.b_op r).val = ZiskFv.Airs.Tables.BinaryTable.OP_LTU
  | _ => True

theorem zisk_riscv_compliant_program_bus_itype_binary
    (env : OpEnvelope state m r_main) :
    env.exec_eq_itype_binary := by
  cases env with
  | andi andi_input r1 rd imm v bus pins h_andi_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_itype_binary]
    exact ZiskFv.Equivalence.Andi.equiv_ANDI state andi_input r1 rd imm m v r_main bus pins
      h_andi_subset h_lane_rd promises
  | ori ori_input r1 rd imm v bus pins h_ori_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_itype_binary]
    exact ZiskFv.Equivalence.Ori.equiv_ORI state ori_input r1 rd imm m v r_main bus pins
      h_ori_subset h_lane_rd promises
  | xori xori_input r1 rd imm v bus pins h_xori_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_itype_binary]
    exact ZiskFv.Equivalence.Xori.equiv_XORI state xori_input r1 rd imm m v r_main bus pins
      h_xori_subset h_lane_rd promises
  | slti slti_input r1 rd imm v bus pins h_slti_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_itype_binary]
    exact ZiskFv.Equivalence.Slti.equiv_SLTI state slti_input r1 rd imm m v r_main bus pins
      h_slti_subset h_lane_rd promises
  | sltiu sltiu_input r1 rd imm v bus pins h_sltiu_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_itype_binary]
    exact ZiskFv.Equivalence.Sltiu.equiv_SLTIU state sltiu_input r1 rd imm m v r_main bus pins
      h_sltiu_subset h_lane_rd promises
  | _ => trivial

/-- Noncanonical C7 static BinaryTable route for the ITYPE Binary arms. -/
theorem zisk_riscv_compliant_program_bus_itype_binary_logic_of_static_lookup
    (env : OpEnvelope state m r_main)
    (offset : ℕ) (cleanEnv : Environment FGL)
    (h_static : env.itype_binary_logic_static_lookup_soundness) :
    env.exec_eq_itype_binary := by
  cases env with
  | andi andi_input r1 rd imm v bus pins h_andi_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_itype_binary, OpEnvelope.itype_binary_logic_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Andi.equiv_ANDI_of_static_lookup
      state andi_input r1 rd imm m v r_main offset cleanEnv h_static.1 h_static.2
      bus pins h_andi_subset h_lane_rd promises
  | ori ori_input r1 rd imm v bus pins h_ori_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_itype_binary, OpEnvelope.itype_binary_logic_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Ori.equiv_ORI_of_static_lookup
      state ori_input r1 rd imm m v r_main offset cleanEnv h_static.1 h_static.2
      bus pins h_ori_subset h_lane_rd promises
  | xori xori_input r1 rd imm v bus pins h_xori_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_itype_binary, OpEnvelope.itype_binary_logic_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Xori.equiv_XORI_of_static_lookup
      state xori_input r1 rd imm m v r_main offset cleanEnv h_static.1 h_static.2
      bus pins h_xori_subset h_lane_rd promises
  | slti slti_input r1 rd imm v bus pins h_slti_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_itype_binary, OpEnvelope.itype_binary_logic_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Compliance.equiv_SLTI_of_static_lookup
      state slti_input r1 rd imm m v r_main offset cleanEnv h_static.1 h_static.2
      bus pins h_slti_subset h_lane_rd promises
  | sltiu sltiu_input r1 rd imm v bus pins h_sltiu_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_itype_binary, OpEnvelope.itype_binary_logic_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Compliance.equiv_SLTIU_of_static_lookup
      state sltiu_input r1 rd imm m v r_main offset cleanEnv h_static.1 h_static.2
      bus pins h_sltiu_subset h_lane_rd promises
  | _ => trivial

end ZiskFv.Compliance
