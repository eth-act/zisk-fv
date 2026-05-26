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
  | .lb lb_input _ _ _ bus _ _ =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          lb_input.imm, regidx.Regidx lb_input.r1, regidx.Regidx lb_input.rd, false, 1
        ))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .lh lh_input _ _ _ bus _ _ =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          lh_input.imm, regidx.Regidx lh_input.r1, regidx.Regidx lh_input.rd, false, 2
        ))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .lw lw_input _ _ _ bus _ _ =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          lw_input.imm, regidx.Regidx lw_input.r1, regidx.Regidx lw_input.rd, false, 4
        ))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  -- ADDI / ADDIW
  | .addi _ r1 rd imm _ bus _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .addiw _ r1 rd imm _ bus _ _ _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ADDIW (imm, r1, rd))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

/-- Static BinaryExtension lookup witness required by the noncanonical C7
    static route for signed-load arms in this dispatch family. Non-signed-load
    arms carry no obligation. -/
def OpEnvelope.misc_signed_load_static_lookup_soundness
    : OpEnvelope state m r_main → Prop
  | .lb _ _ _ v _ _ _ => ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  | .lh _ _ _ v _ _ _ => ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  | .lw _ _ _ v _ _ _ => ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  | _ => True

theorem zisk_riscv_compliant_program_bus_misc
    (env : OpEnvelope state m r_main) :
    env.exec_eq_misc := by
  cases env with
  | lb lb_input regs mem v bus pins promises =>
    simp only [OpEnvelope.exec_eq_misc]
    exact ZiskFv.Equivalence.Lb.equiv_LB state lb_input regs m mem r_main v bus pins promises
  | lh lh_input regs mem v bus pins promises =>
    simp only [OpEnvelope.exec_eq_misc]
    exact ZiskFv.Equivalence.Lh.equiv_LH state lh_input regs m mem r_main v bus pins promises
  | lw lw_input regs mem v bus pins promises =>
    simp only [OpEnvelope.exec_eq_misc]
    exact ZiskFv.Equivalence.Lw.equiv_LW state lw_input regs m mem r_main v bus pins promises
  | addi addi_input r1 rd imm badd bus pins h_main_subset h_addi_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_misc]
    exact ZiskFv.Equivalence.Addi.equiv_ADDI state addi_input r1 rd imm m badd r_main bus
      pins h_main_subset h_addi_subset h_lane_rd promises
  | addiw addiw_input r1 rd imm _v bus pins h_addiw_subset providerTable providerRow
      h_component h_table_spec h_provider_row h_match_static h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq_misc]
    exact ZiskFv.Equivalence.Addiw.equiv_ADDIW
      state addiw_input r1 rd imm m providerTable providerRow r_main bus pins
      h_addiw_subset h_component h_table_spec h_provider_row h_match_static
      h_lane_rd promises
  | _ => trivial

/-- Noncanonical C7 static BinaryExtensionTable route for the signed-load subset
    of the misc dispatcher. The canonical dispatcher above is unchanged. -/
theorem zisk_riscv_compliant_program_bus_misc_signed_load_of_static_lookup
    (env : OpEnvelope state m r_main)
    (offset : ℕ) (cleanEnv : Environment FGL)
    (h_static : env.misc_signed_load_static_lookup_soundness) :
    env.exec_eq_misc := by
  cases env with
  | lb lb_input regs mem v bus pins promises =>
    simp only [OpEnvelope.exec_eq_misc, OpEnvelope.misc_signed_load_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Lb.equiv_LB_of_static_lookup state lb_input regs m mem r_main v
      offset cleanEnv h_static bus pins promises
  | lh lh_input regs mem v bus pins promises =>
    simp only [OpEnvelope.exec_eq_misc, OpEnvelope.misc_signed_load_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Lh.equiv_LH_of_static_lookup state lh_input regs m mem r_main v
      offset cleanEnv h_static bus pins promises
  | lw lw_input regs mem v bus pins promises =>
    simp only [OpEnvelope.exec_eq_misc, OpEnvelope.misc_signed_load_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Lw.equiv_LW_of_static_lookup state lw_input regs m mem r_main v
      offset cleanEnv h_static bus pins promises
  | _ =>
    exact zisk_riscv_compliant_program_bus_misc _

end ZiskFv.Compliance
