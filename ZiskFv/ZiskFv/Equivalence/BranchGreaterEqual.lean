import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchGreaterEqual
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.bge
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 BGE (Phase 3A B2). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BGE`),
* the compositional BGE spec
  (`ZiskFv.Spec.BranchGreaterEqual.branch_ge_compositional`, a thin
  wrapper over `BranchArchetype.branch_archetype_pc_dispatch` at
  `opcode_lit = OP_LT`),
* the Sail pure-function equivalence
  (`PureSpec.execute_BGE_pure_equiv`, closed via the trusted axiom
  `execute_BGE_pure_equiv_axiom` — see C2 in
  `docs/fv/trusted-base.md`).

**Hypothesis-free bus side.** D3 closed bus-emission for shape (b);
BGE shares shape (b) with BEQ/BNE so the metaplan reuses
`bus_effect_matches_sail_beq`.
-/

namespace ZiskFv.Equivalence.BranchGreaterEqual

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.BranchGreaterEqual

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level BGE theorem.** Given the branch-subset Main
    constraints plus the mode witnesses from `transpile_BGE`, the
    next-pc cell satisfies the same flag-dispatched handshake formula
    as BLT/BNE/BEQ — the polarity flip (flag = 0 taken, flag = 1
    not-taken) emerges only after composing with `transpile_BGE`'s
    `jmp_offset1 = 4, jmp_offset2 = imm` assignment. -/
theorem equiv_BGE
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : branch_ge_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_ge_compositional m r_main next_pc h_circuit

/-- **Sail-level companion.** Wraps
    `PureSpec.execute_BGE_pure_equiv`. -/
theorem equiv_BGE_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bge_input : PureSpec.BgeInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bge_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bge_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bge_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bge_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGE)) state
      = let bge_output := PureSpec.execute_BGE_pure bge_input
        (do
          Sail.writeReg Register.nextPC bge_output.nextPC
          if bge_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !bge_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (bge_input.PC + BitVec.signExtend 64 bge_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BGE_pure_equiv bge_input imm r1 r2 h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem (Phase 3A B2).** Shape (b) bus reuse. -/
theorem equiv_BGE_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bge_input : PureSpec.BgeInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bge_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bge_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bge_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bge_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGE_pure bge_input).nextPC)
    (h_not_throws : (PureSpec.execute_BGE_pure bge_input).throws = false)
    (h_success : (PureSpec.execute_BGE_pure bge_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGE)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BGE_sail state bge_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  symm
  exact ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BGE_pure bge_input).nextPC
    (PureSpec.execute_BGE_pure bge_input).throws
    (PureSpec.execute_BGE_pure bge_input).success
    bge_input.PC bge_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

end ZiskFv.Equivalence.BranchGreaterEqual
