import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchEqual
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.RV64D.beq
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 BEQ. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BEQ`),
* the compositional BEQ spec (`ZiskFv.Spec.BranchEqual.branch_eq_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_BEQ_pure_equiv`, newly closed Phase 2 A1
  thanks to `jump_to_equiv`),

into a metaplan-shaped theorem:

* `equiv_BEQ_metaplan` — the metaplan target shape:
  `execute_instruction (.BTYPE (imm, r2, r1, BEQ)) state
    = (bus_effect exec_row mem_row state).2`.

As with `equiv_ADD_metaplan`, the bus-emission correctness hypothesis
`h_bus_execute_matches_sail` is parameterized — Phase 4 audit derives
it from a PIL-level bus-emission spec.
-/

namespace ZiskFv.Equivalence.BranchEqual

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.BranchEqual

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level BEQ theorem.** Given the branch-subset Main
    constraints plus the mode witnesses from `transpile_BEQ`, the
    next-pc cell advances by either `jmp_offset1` (taken) or
    `jmp_offset2` (not-taken), dispatched on `flag`:
    `next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)`.

    This is the circuit-level companion to `equiv_BEQ_sail` below —
    together they form the analogue of `equiv_ADD` + `equiv_ADD_sail`
    from the ADD archetype. -/
theorem equiv_BEQ
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : branch_eq_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_eq_compositional m r_main next_pc h_circuit

/-- **Closed-form circuit-level BEQ theorem.** Phase 2.5 D2 eliminated
    the `next_pc : FGL` parameter by deriving it from the extracted
    closed-form `pc_handshake` (Main constraint 20) via
    `pc_handshake_to_next_pc`. The caller supplies instead:

    * the booleans + disjointness for row `r_main`,
    * the BEQ mode witnesses at `r_main`,
    * the extracted handshake at `r_main + 1` (closed form — no
      `next_pc` quantifier),
    * the non-segment-boundary witness `segment_l1 (r_main + 1) = 0`.

    The next-row `pc` cell (`m.pc (r_main + 1)`) plays the role of
    `next_pc` in the conclusion. -/
theorem equiv_BEQ_closed
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (h_flag_bool : flag_boolean m r_main)
    (h_ext_bool : is_external_op_boolean m r_main)
    (h_disjoint : flag_set_pc_disjoint m r_main)
    (h_mode : main_row_in_beq_mode m r_main)
    (h_seg : m.segment_l1 (r_main + 1) = 0)
    (h_handshake_next : pc_handshake m (r_main + 1)) :
    m.pc (r_main + 1) = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_eq_compositional m r_main (m.pc (r_main + 1))
    ⟨⟨h_flag_bool, h_ext_bool, h_disjoint,
      pc_handshake_to_next_pc m r_main h_seg h_handshake_next⟩,
     h_mode⟩

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 BEQ reduces to the pure-function block supplied by
    `PureSpec.execute_BEQ_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` (no compressed extension)
    witness.

    Wraps `PureSpec.execute_BEQ_pure_equiv` to expose the Sail chain at
    this module's export surface. -/
theorem equiv_BEQ_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = let beq_output := PureSpec.execute_BEQ_pure beq_input
        (do
          Sail.writeReg Register.nextPC beq_output.nextPC
          if beq_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !beq_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (beq_input.PC + BitVec.signExtend 64 beq_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BEQ_pure_equiv beq_input imm h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem.** The shape the original metaplan targets for
    RV64 BEQ: Sail's `execute_instruction` on an RV64 BEQ equals the
    state computed by applying `bus_effect` to the circuit's execution
    and memory bus rows.

    Composes `equiv_BEQ_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_ADD_metaplan`, the
    bus-emission-correctness obligation is parameterized; Phase 4 audit
    derives it from PIL-level bus emission.

    **Hypotheses.**
    * Sail side (from `equiv_BEQ_sail`): register readability
      (`h_input_r1`, `h_input_r2`), PC (`h_input_pc`), misa (`h_input_misa`),
      and ZisK `misa[C] = 0` (`h_misa_c`).
    * Bus side: `h_bus_execute_matches_sail` asserts that the two-entry
      execution bus (read PC, write nextPC) fed through `bus_effect`
      returns the same `EStateM.Result` as the concrete Sail monadic
      block in `equiv_BEQ_sail`'s conclusion. The memory-bus component
      is empty for BEQ (no register write, no memory access). -/
theorem equiv_BEQ_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let beq_output := PureSpec.execute_BEQ_pure beq_input
           (do
             Sail.writeReg Register.nextPC beq_output.nextPC
             if beq_output.throws then
               throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
             else if !beq_output.success then
               pure (
                 ExecutionResult.Memory_Exception (
                   (virtaddr.Virtaddr (beq_input.PC + BitVec.signExtend 64 beq_input.imm)),
                   (ExceptionType.E_Fetch_Addr_Align ())
                 )
               )
             else
               (pure (ExecutionResult.Retire_Success ()))) state)) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_BEQ_sail state beq_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.BranchEqual
