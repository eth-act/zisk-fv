import Mathlib

import ZiskFv.Equivalence.Auipc
import ZiskFv.Equivalence.Promises.UType
import ZiskFv.Equivalence.Promises.UTypeHelpers
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `equiv_AUIPC` Compliance wrapper — ControlFlow non-branch

The wrapper takes the structural `UTypePromises` bundle along with the
upstream activation/opcode pins and the per-row AUIPC subset
constraint, and internally calls `auipc_h_circuit_of_main_constraints`
(which transitively consumes `transpile_AUIPC`) to derive `h_circuit`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_AUIPC`.** Derives `h_circuit` from
    `auipc_h_circuit_of_main_constraints` (consuming `transpile_AUIPC`)
    and delegates to canonical `equiv_AUIPC`. -/
theorem equiv_AUIPC_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    -- Activation / opcode pins on Main + per-row subset constraint.
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_auipc : m.op r_main = OP_FLAG)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    -- Structural `UTypePromises` bundle.
    (promises : ZiskFv.Equivalence.Promises.UTypePromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row e_rd nextPC_val)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [e_rd] state).2 :=
  have h_circuit :=
    ZiskFv.Equivalence.Promises.auipc_h_circuit_of_main_constraints
      m r_main next_pc h_main_active h_main_op_auipc h_auipc_subset
  ZiskFv.Equivalence.Auipc.equiv_AUIPC state auipc_input imm rd
    exec_row e_rd nextPC_val m r_main next_pc
    promises h_circuit h_no_wrap h_lo_bound h_pc_offset_lt_2_32

end ZiskFv.Compliance
