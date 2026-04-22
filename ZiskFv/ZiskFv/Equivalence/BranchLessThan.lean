import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchLessThan
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.blt
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 BLT (Phase 3A B1). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BLT`),
* the compositional BLT spec
  (`ZiskFv.Spec.BranchLessThan.branch_lt_compositional`, a thin
  wrapper over `BranchArchetype.branch_archetype_pc_dispatch` at
  `opcode_lit = OP_LT`),
* the Sail pure-function equivalence
  (`PureSpec.execute_BLT_pure_equiv`, closed via the trusted axiom
  `execute_BLT_pure_equiv_axiom` — see entry C2 in
  `docs/fv/trusted-base.md`),

into three theorems mirroring `Equivalence/BranchEqual.lean` /
`Equivalence/BranchNotEqual.lean`:

* `equiv_BLT` — circuit-level flag-dispatched next-pc formula;
* `equiv_BLT_sail` — Sail reduction to `PureSpec.execute_BLT_pure`;
* `equiv_BLT_metaplan` — the metaplan target:
  `execute_instruction (.BTYPE (imm, r2, r1, BLT)) state
    = (bus_effect exec_row mem_row state).2`.

**Hypothesis-free bus side.** D3 closed bus-emission for shape (b)
(externally-routed branches); BLT shares shape (b) with BEQ/BNE so
the metaplan theorem reuses `bus_effect_matches_sail_beq` directly.
-/

namespace ZiskFv.Equivalence.BranchLessThan

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.BranchLessThan

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level BLT theorem.** Given the branch-subset Main
    constraints plus the mode witnesses from `transpile_BLT`, the
    next-pc cell satisfies the flag-dispatched handshake formula.
    Identical in shape to `equiv_BEQ`/`equiv_BNE` — the opcode literal
    only surfaces at the bus-flag-correctness layer. -/
theorem equiv_BLT
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : branch_lt_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_lt_compositional m r_main next_pc h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 BLT reduces to the pure-function block supplied by
    `PureSpec.execute_BLT_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` witness.

    Wraps `PureSpec.execute_BLT_pure_equiv`. -/
theorem equiv_BLT_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = let blt_output := PureSpec.execute_BLT_pure blt_input
        (do
          Sail.writeReg Register.nextPC blt_output.nextPC
          if blt_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !blt_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (blt_input.PC + BitVec.signExtend 64 blt_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BLT_pure_equiv blt_input imm r1 r2 h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem (Phase 3A B1).**

    `execute_instruction` on an RV64 BLT equals the state computed by
    applying `bus_effect` to the circuit's execution and memory bus rows.
    Reuses `bus_effect_matches_sail_beq` (shape (b), branch-shape). -/
theorem equiv_BLT_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Structural bus hypotheses (Phase 2.5 D3 shape (b)).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLT_pure blt_input).nextPC)
    (h_not_throws : (PureSpec.execute_BLT_pure blt_input).throws = false)
    (h_success : (PureSpec.execute_BLT_pure blt_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BLT_sail state blt_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  -- Discharge bus-side equation via the shape (b) lemma (shared across
  -- shape (b) branch opcodes: BEQ/BNE/BLT/BGE/BLTU/BGEU).
  symm
  exact ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BLT_pure blt_input).nextPC
    (PureSpec.execute_BLT_pure blt_input).throws
    (PureSpec.execute_BLT_pure blt_input).success
    blt_input.PC blt_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

end ZiskFv.Equivalence.BranchLessThan
