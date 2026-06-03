import ZiskFv.Compliance.Wrappers.Auipc
import ZiskFv.Channels.StateEffect

/-!
# `equiv_AUIPC` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for AUIPC. The theorem is
route-parametric because production AUIPC has two bus shapes:
`rd != x0` uses one rd-write memory row, while `rd = x0` uses an empty
memory bus.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Auipc.lean`.

## Trust note

No new axioms. The `rdWrite` route delegates to the static-provenance AUIPC
wrapper, so it does not consume the legacy AUIPC mode-pin axiom. The
`x0NoMemory` route delegates to the empty-memory AUIPC wrapper.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Tactics.UTypeArchetype (lui_subset_holds auipc_subset_holds)
open ZiskFv.Trusted (OP_COPYB OP_FLAG)

namespace ZiskFv.Equivalence.Auipc

/-- The two production AUIPC bus shapes.

    `rdWrite` is the ordinary `rd != x0` shape with one memory-bus register
    write. `x0NoMemory` is the `rd = x0` shape: the static/production
    transpiler emits `storeNone`, so the channel output has an empty memory
    bus. -/
inductive AuipcRoute
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main FGL FGL) (r_main : ℕ) where
  | rdWrite
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    {inst : ZiskFv.Transpiler.Static.Rv64Inst}
    (provenance : ZiskFv.Compliance.MainStaticRowProvenance m r_main inst)
    (h_inst_op : inst.op = ZiskFv.Transpiler.Static.Rv64Op.auipc)
    (h_inst_rd_ne_zero : inst.rd ≠ 0)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    (h_offset_bridge : (m.jmp_offset2 r_main).val
      = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat)
    (h_pc_bridge : (m.pc r_main).val = auipc_input.PC.toNat)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row e_rd nextPC_val)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) :
      AuipcRoute state auipc_input imm rd m r_main
  | x0NoMemory
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (promises : ZiskFv.EquivCore.Promises.UTypeNoMemPromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row) :
      AuipcRoute state auipc_input imm rd m r_main

namespace AuipcRoute

@[simp]
def channels
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {auipc_input : PureSpec.AuipcInput}
    {imm : BitVec 20} {rd : regidx}
    {m : Valid_Main FGL FGL} {r_main : ℕ}
    (route : AuipcRoute state auipc_input imm rd m r_main) :
    ChannelEnsembleOutput :=
  match route with
  | .rdWrite exec_row e_rd .. => ⟨exec_row, [e_rd]⟩
  | .x0NoMemory exec_row _ => ⟨exec_row, []⟩

end AuipcRoute

theorem equiv_AUIPC
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (route : AuipcRoute state auipc_input imm rd m r_main)
    : execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = state_effect_via_channels (AuipcRoute.channels route) state := by
  have _next_pc_anchor : FGL := next_pc
  cases route with
  | rdWrite exec_row e_rd nextPC_val route_next_pc store_pc_mem provenance
      h_inst_rd_ne_zero h_auipc_subset h_offset_bridge h_pc_bridge promises h_no_wrap
      h_pc_offset_lt_2_32 =>
    change execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = state_effect_via_channels ⟨exec_row, [e_rd]⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    exact ZiskFv.Compliance.equiv_AUIPC_of_static_provenance
      state auipc_input imm rd exec_row e_rd nextPC_val m r_main route_next_pc
      store_pc_mem provenance h_inst_op h_inst_rd_ne_zero h_auipc_subset
      h_offset_bridge h_pc_bridge promises h_no_wrap h_pc_offset_lt_2_32
  | x0NoMemory exec_row promises =>
    change execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = state_effect_via_channels ⟨exec_row, []⟩ state
    rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
    exact ZiskFv.Compliance.equiv_AUIPC_x0_no_memory
      state auipc_input imm rd exec_row promises

end ZiskFv.Equivalence.Auipc
