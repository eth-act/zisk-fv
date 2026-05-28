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
  | .ld ld_input _ _ bus _ _ _ =>
      execute_instruction (instruction.LOAD (
        ld_input.imm,
        regidx.Regidx ld_input.r1,
        regidx.Regidx ld_input.rd,
        false,
        8
      )) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | .sd sd_input _ bus _ _ _ _ =>
      execute_instruction (instruction.STORE (
        sd_input.imm,
        regidx.Regidx sd_input.r2,
        regidx.Regidx sd_input.r1,
        8
      )) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_ldsd
    (env : OpEnvelope state m r_main) :
    env.exec_eq_ldsd := by
  cases env with
  | ld ld_input regs mem bus pins promises w =>
    simp only [OpEnvelope.exec_eq_ldsd]
    exact ZiskFv.Equivalence.Ld.equiv_LD state ld_input regs m mem r_main bus pins promises w
  | sd sd_input regs bus pins h_opcode_assumptions promises w =>
    simp only [OpEnvelope.exec_eq_ldsd]
    exact ZiskFv.Equivalence.Sd.equiv_SD state sd_input regs m r_main bus pins h_opcode_assumptions promises w
  | _ => trivial

end ZiskFv.Compliance
