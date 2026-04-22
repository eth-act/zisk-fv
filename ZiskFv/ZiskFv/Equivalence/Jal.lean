import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Jal
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.RV64D.jal
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 JAL. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_JAL`),
* the compositional JAL spec (`ZiskFv.Spec.Jal.jal_pc_advance`),
* the Sail pure-function equivalence
  (`PureSpec.execute_JAL_pure_equiv`, newly closed Phase 2 A2
  thanks to `jump_to_equiv`),

into a metaplan-shaped theorem:

* `equiv_JAL_metaplan` — the metaplan target shape:
  `execute_instruction (.JAL (imm, rd)) state
    = (bus_effect exec_row mem_row state).2`.

As with `equiv_ADD_metaplan` / `equiv_BEQ_metaplan`, the bus-emission
correctness hypothesis `h_bus_execute_matches_sail` is parameterized —
Phase 4 audit derives it from a PIL-level bus-emission spec. For JAL the
operation bus is inactive (`is_external_op = 0`), so that parameter is
strictly simpler than BEQ's (no Binary-SM delegation to model); only
the execution + memory bus entries matter.
-/

namespace ZiskFv.Equivalence.Jal

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Jal

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level JAL theorem.** Given the jump-subset Main
    constraints plus the mode witnesses from `transpile_JAL`, the
    next-pc cell advances by `jmp_offset1 = imm`:
    `next_pc = pc + jmp_offset1`.

    This is the circuit-level companion to `equiv_JAL_sail` below —
    together they form the analogue of `equiv_ADD` + `equiv_ADD_sail`
    from the ADD archetype. Uses the transpile axiom's pinning of
    `jmp_offset1` to relate the field-level offset to the RV64 `imm`. -/
theorem equiv_JAL
    (_rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : jal_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main :=
  jal_pc_advance m r_main next_pc h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 JAL reduces to the pure-function block supplied by
    `PureSpec.execute_JAL_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` (no compressed extension)
    witness.

    Wraps `PureSpec.execute_JAL_pure_equiv` to expose the Sail chain at
    this module's export surface. -/
theorem equiv_JAL_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = let jal_output := PureSpec.execute_JAL_pure jal_input
        (do
          match jal_output.nextPC with
            | .some nextPC => Sail.writeReg Register.nextPC nextPC
            | .none => pure ()
          match jal_output.rd with
            | .some (reg, rd_val) => write_xreg reg rd_val
            | .none => pure ()
          if jal_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !jal_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (jal_input.PC + BitVec.signExtend 64 jal_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_JAL_pure_equiv jal_input imm rd
    h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem.** The shape the original metaplan targets for
    RV64 JAL: Sail's `execute_instruction` on an RV64 JAL equals the
    state computed by applying `bus_effect` to the circuit's execution
    and memory bus rows.

    Composes `equiv_JAL_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_ADD_metaplan` /
    `equiv_BEQ_metaplan`, the bus-emission-correctness obligation is
    parameterized; Phase 4 audit derives it from PIL-level bus emission.

    **Hypotheses.**
    * Sail side (from `equiv_JAL_sail`): register readability
      (`h_input_rd`), PC (`h_input_pc`), misa (`h_input_misa`), and
      ZisK `misa[C] = 0` (`h_misa_c`).
    * Bus side: `h_bus_execute_matches_sail` asserts that the
      execution-bus entries (read PC, write nextPC) together with the
      memory-bus entry for the rd write match the Sail pure-spec
      monadic block in `equiv_JAL_sail`'s conclusion. Unlike BEQ, JAL
      *does* populate a memory-bus entry (the rd write via
      `store_pc`); the operation-bus is inactive because
      `is_external_op = 0`. -/
theorem equiv_JAL_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let jal_output := PureSpec.execute_JAL_pure jal_input
           (do
             match jal_output.nextPC with
               | .some nextPC => Sail.writeReg Register.nextPC nextPC
               | .none => pure ()
             match jal_output.rd with
               | .some (reg, rd_val) => write_xreg reg rd_val
               | .none => pure ()
             if jal_output.throws then
               throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
             else if !jal_output.success then
               pure (
                 ExecutionResult.Memory_Exception (
                   (virtaddr.Virtaddr (jal_input.PC + BitVec.signExtend 64 jal_input.imm)),
                   (ExceptionType.E_Fetch_Addr_Align ())
                 )
               )
             else
               (pure (ExecutionResult.Retire_Success ()))) state)) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_JAL_sail state jal_input imm rd misa_val
        h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.Jal
