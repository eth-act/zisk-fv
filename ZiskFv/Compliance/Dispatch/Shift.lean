import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Equivalence.Sll
import ZiskFv.Equivalence.Slli
import ZiskFv.Equivalence.Sra
import ZiskFv.Equivalence.Srai
import ZiskFv.Equivalence.Srl
import ZiskFv.Equivalence.Srli

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
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

def OpEnvelope.exec_eq_shift
    : OpEnvelope state m r_main → Prop
  | .sll _ r1 r2 rd _ _ bus _ _ _ _ _ _ _ =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srl _ r1 r2 rd _ _ bus _ _ _ _ _ _ _ =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sra _ r1 r2 rd _ _ bus _ _ _ _ _ _ _ =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .slli _ r1 rd shamt _ _ bus _ _ _ _ _ _ _ =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srli _ r1 rd shamt _ _ bus _ _ _ _ _ _ _ =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .srai _ r1 rd shamt _ _ bus _ _ _ _ _ _ _ =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

/-- Static BinaryExtension lookup witness required by the noncanonical C7
    static route for this dispatch family. Non-shift arms carry no obligation. -/
def OpEnvelope.shift_static_lookup_soundness
    : OpEnvelope state m r_main → Prop
  | .sll _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .srl _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .sra _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .slli _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .srli _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .srai _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True
  | _ => True

theorem zisk_riscv_compliant_program_bus_shift
    (env : OpEnvelope state m r_main) :
    env.exec_eq_shift := by
  cases env with
  | sll sll_input r1 r2 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift]
    exact ZiskFv.Equivalence.Sll.equiv_SLL state sll_input r1 r2 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | srl srl_input r1 r2 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift]
    exact ZiskFv.Equivalence.Srl.equiv_SRL state srl_input r1 r2 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | sra sra_input r1 r2 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift]
    exact ZiskFv.Equivalence.Sra.equiv_SRA state sra_input r1 r2 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | slli slli_input r1 rd shamt providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift]
    exact ZiskFv.Equivalence.Slli.equiv_SLLI state slli_input r1 rd shamt
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | srli srli_input r1 rd shamt providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift]
    exact ZiskFv.Equivalence.Srli.equiv_SRLI state srli_input r1 rd shamt
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | srai srai_input r1 rd shamt providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift]
    exact ZiskFv.Equivalence.Srai.equiv_SRAI state srai_input r1 rd shamt
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | _ => trivial

/-- Noncanonical C7 static BinaryExtensionTable route for the shift dispatcher.
    The canonical dispatcher above is unchanged; this theorem is the terminal
    wiring target for retiring the legacy BinaryExtension table-consumer axiom
    from the shift family. -/
theorem zisk_riscv_compliant_program_bus_shift_of_static_lookup
    (env : OpEnvelope state m r_main)
    (_offset : ℕ) (_cleanEnv : Environment FGL)
    (h_static : env.shift_static_lookup_soundness) :
    env.exec_eq_shift := by
  cases env with
  | sll sll_input r1 r2 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift, OpEnvelope.shift_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Sll.equiv_SLL state sll_input r1 r2 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | srl srl_input r1 r2 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift, OpEnvelope.shift_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Srl.equiv_SRL state srl_input r1 r2 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | sra sra_input r1 r2 rd providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift, OpEnvelope.shift_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Sra.equiv_SRA state sra_input r1 r2 rd
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | slli slli_input r1 rd shamt providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift, OpEnvelope.shift_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Slli.equiv_SLLI state slli_input r1 rd shamt
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | srli srli_input r1 rd shamt providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift, OpEnvelope.shift_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Srli.equiv_SRLI state srli_input r1 rd shamt
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | srai srai_input r1 rd shamt providerTable providerRow bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd =>
    simp only [OpEnvelope.exec_eq_shift, OpEnvelope.shift_static_lookup_soundness] at h_static ⊢
    exact ZiskFv.Equivalence.Srai.equiv_SRAI state srai_input r1 rd shamt
      m providerTable providerRow r_main bus promises pins
      h_component h_table_spec h_provider_row h_match h_lane_rd
  | _ =>
    simp only [OpEnvelope.exec_eq_shift]

end ZiskFv.Compliance
