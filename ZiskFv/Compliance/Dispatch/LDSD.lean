import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Equivalence.Ld
import ZiskFv.Equivalence.Sd

/-!
# Compliance dispatcher (LD + SD arms)

Two memory-bus arms: LD (load doubleword) and SD (store doubleword).
The other 6 loads (LB/LH/LW/LBU/LHU/LWU) and 3 stores (SB/SH/SW)
follow the same pattern with sign/zero extension or partial-width
variants — each is a mechanical addition.

## Trust note

No new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Channels
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

def OpEnvelope.exec_eq_ldsd
    : OpEnvelope state m r_main → Prop
  | .ld ld_input _ _ bus .. =>
      execute_instruction (instruction.LOAD (
        ld_input.imm,
        regidx.Regidx ld_input.r1,
        regidx.Regidx ld_input.rd,
        false,
        8
      )) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sd sd_input _ bus .. =>
      execute_instruction (instruction.STORE (
        sd_input.imm,
        regidx.Regidx sd_input.r2,
        regidx.Regidx sd_input.r1,
        8
      )) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_ldsd
    (env : OpEnvelope state m r_main)
    (h_memory_timeline : env.memoryTimelineEvidence) :
    env.exec_eq_ldsd := by
  cases env with
  | ld ld_input regs mem bus pins promises r_mem h_mainEval h_providerEval
      h_msg h_main_row h_mem_row h_main_spec h_store_pc h_main_b_match
      h_main_c_match h_addr1 h_addr2_zero_iff h_addr2_idx h_mem_sel h_mem_wr =>
    simp only [OpEnvelope.exec_eq_ldsd]
    simp only [OpEnvelope.memoryTimelineEvidence] at h_memory_timeline
    rcases h_memory_timeline with ⟨timeline⟩
    let promises' :=
      ZiskFv.EquivCore.Promises.LoadStructuralPromises.withMemoryTimelineEvidence
        promises timeline
    let w :=
      ZiskFv.EquivCore.Bridge.MemClean.ldCleanWitness_of_full_ensemble_main_b_mem_provider
      m mem r_main r_mem bus ld_input
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
      h_addr2_idx h_mem_sel h_mem_wr
    exact ZiskFv.Equivalence.Ld.equiv_LD
      state ld_input regs m mem r_main bus pins promises' w
  | sd sd_input regs bus pins h_opcode_assumptions promises h_main_row
      h_main_spec h_store_pc h_main_c_match h_addr2 h_b0_value h_b1_value =>
    simp only [OpEnvelope.exec_eq_ldsd]
    let w :=
      ZiskFv.EquivCore.Bridge.MemClean.sdCleanWitness_of_full_ensemble_main_c
      m r_main bus sd_input h_main_row h_main_spec h_store_pc
      h_main_c_match h_addr2 h_b0_value h_b1_value
    exact ZiskFv.Equivalence.Sd.equiv_SD
      state sd_input regs m r_main bus pins h_opcode_assumptions promises w
  | _ => simp only [OpEnvelope.exec_eq_ldsd]

end ZiskFv.Compliance
