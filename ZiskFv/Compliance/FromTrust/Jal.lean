import Mathlib

import ZiskFv.Equivalence.Jal
import ZiskFv.Equivalence.Promises.Jump
import ZiskFv.Equivalence.Promises.JumpHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `equiv_JAL` Compliance wrapper — ControlFlow non-branch

The wrapper takes the structural `JumpPromises` bundle along with the
upstream activation/opcode pins on Main and the per-row JAL subset
constraint, and internally calls `jal_h_circuit_of_main_constraints`
(which transitively consumes `transpile_JAL`) to derive `h_circuit`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_JAL`.** Derives `h_circuit` from
    `jal_h_circuit_of_main_constraints` (consuming `transpile_JAL`)
    and delegates to canonical `equiv_JAL`. -/
theorem equiv_JAL_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    -- Activation / opcode pins on Main + per-row subset constraint.
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_jal : m.op r_main = OP_FLAG)
    (h_jal_subset :
      ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
    -- Structural `JumpPromises` bundle.
    (promises : ZiskFv.Equivalence.Promises.JumpPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [e_rd] state).2 :=
  have h_circuit :=
    ZiskFv.Equivalence.Promises.jal_h_circuit_of_main_constraints
      m r_main next_pc h_main_active h_main_op_jal h_jal_subset
  ZiskFv.Equivalence.Jal.equiv_JAL state jal_input imm rd misa_val
    exec_row e_rd nextPC_val m r_main next_pc
    promises h_input_imm h_not_throws
    h_circuit h_pc_bound h_lo_bound h_pc_offset_lt_2_32

end ZiskFv.Compliance
