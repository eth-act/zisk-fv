import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Equivalence.Auipc
import ZiskFv.Equivalence.Fence
import ZiskFv.Equivalence.Lui

/-!
# Compliance dispatcher (UTYPE + Fence)

Follows the dispatcher pattern (see
`Compliance/Dispatch/Branch.lean`) to UTYPE (LUI, AUIPC) and FENCE arms.

These three arms share a property convenient for v2: they take no
provider-AIR validator on the OpEnvelope (just exec_row + optional
single mem_row), so the channel-ensemble extraction is direct.

## Trust note

No new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Channels
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- The per-arm v2 conclusion Prop for LUI / AUIPC / FENCE arms.
    Falls through to `True` for unhandled arms. -/
def OpEnvelope.exec_eq_nomem
    : OpEnvelope state m r_main → Prop
  | .lui _ imm rd _ exec_row e_rd _ _ _ _ _ _ _ =>
      execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
        = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state
  | .auipc _ imm rd exec_row e_rd _ _ _ _ _ _ _ _ _ _ _ _ =>
      execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
        = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state
  | .auipc_x0 _ imm rd exec_row _ =>
      execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
        = state_effect_via_channels ⟨exec_row, []⟩ state
  | .fence _ fm pred succ rs rd exec_row _ _ =>
      execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
        = state_effect_via_channels ⟨exec_row, []⟩ state
  | _ => True

/-- Partial v2 dispatcher for LUI / AUIPC / FENCE. -/
theorem zisk_riscv_compliant_program_bus_nomem
    (env : OpEnvelope state m r_main) :
    env.exec_eq_nomem := by
  cases env with
  | lui lui_input imm rd next_pc exec_row e_rd store_pc_mem provenance
      h_inst_op h_lui_subset h_imm_lo_nat h_imm_hi_nat promises =>
    simp only [OpEnvelope.exec_eq_nomem]
    exact ZiskFv.Equivalence.Lui.equiv_LUI state lui_input imm rd m r_main next_pc
      exec_row e_rd store_pc_mem provenance h_inst_op h_lui_subset h_imm_lo_nat
      h_imm_hi_nat promises
  | auipc auipc_input imm rd exec_row e_rd nextPC_val next_pc
          store_pc_mem provenance h_inst_op h_inst_rd_ne_zero h_auipc_subset
          h_offset_bridge h_pc_bridge
          promises h_no_wrap h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq_nomem]
    exact ZiskFv.Equivalence.Auipc.equiv_AUIPC state auipc_input imm rd
      m r_main next_pc
      (ZiskFv.Equivalence.Auipc.AuipcRoute.rdWrite exec_row e_rd nextPC_val
        next_pc store_pc_mem provenance h_inst_op h_inst_rd_ne_zero
        h_auipc_subset h_offset_bridge h_pc_bridge
        promises h_no_wrap h_pc_offset_lt_2_32)
  | auipc_x0 auipc_input imm rd exec_row promises =>
    simp only [OpEnvelope.exec_eq_nomem]
    exact ZiskFv.Equivalence.Auipc.equiv_AUIPC state auipc_input imm rd
      m r_main (0 : FGL)
      (ZiskFv.Equivalence.Auipc.AuipcRoute.x0NoMemory exec_row promises)
  | fence fence_input fm pred succ rs rd exec_row pins promises =>
    simp only [OpEnvelope.exec_eq_nomem]
    exact ZiskFv.Equivalence.Fence.equiv_FENCE state fence_input fm pred succ rs rd m r_main
      exec_row pins promises
  | _ => simp only [OpEnvelope.exec_eq_nomem]

end ZiskFv.Compliance
