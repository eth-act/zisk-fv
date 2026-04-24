import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchNotEqual
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.bne
import ZiskFv.RV64D.BusEffect
import ZiskFv.Airs.BusHypotheses

/-!
End-to-end theorem for RV64 BNE (Phase 2.5 D4a). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BNE`),
* the compositional BNE spec
  (`ZiskFv.Spec.BranchNotEqual.branch_ne_compositional`, which is
  a thin wrapper over the archetype macro
  `BranchArchetype.branch_archetype_pc_dispatch` at `opcode_lit = OP_EQ`),
* the Sail pure-function equivalence
  (`PureSpec.execute_BNE_pure_equiv`, closed in `RV64D/bne.lean`
  alongside the D4a instantiation),

into three theorems mirroring `Equivalence/BranchEqual.lean`:

* `equiv_BNE` — the circuit-level flag-dispatched next-pc formula
  (same shape as `equiv_BEQ`; the polarity flip only shows up after
  composing with `transpile_BNE`'s `jmp_offset1`/`jmp_offset2` swap),
* `equiv_BNE_sail` — the Sail reduction to `PureSpec.execute_BNE_pure`,
* `equiv_BNE_metaplan` — the metaplan's target shape:
  `execute_instruction (.BTYPE (imm, r2, r1, BNE)) state
    = (bus_effect exec_row mem_row state).2`.

**Hypothesis-free bus side.** D3 closed bus-emission for shape (b) —
externally-routed branches (BEQ and BNE share this shape). The metaplan
theorem therefore does **not** require an `h_bus_execute_matches_sail`
hypothesis; it discharges `bus_effect`'s reduction via
`ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq` (reused verbatim
— the shape lemma is opcode-agnostic within shape (b)).
-/

namespace ZiskFv.Equivalence.BranchNotEqual

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.BranchNotEqual

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level BNE theorem.** Given the branch-subset Main
    constraints plus the mode witnesses from `transpile_BNE`, the
    next-pc cell satisfies the same flag-dispatched handshake formula
    as BEQ. The polarity flip (flag = 0 taken, flag = 1 not-taken)
    emerges after composing with `transpile_BNE`'s
    `jmp_offset1 = 4, jmp_offset2 = imm` assignment — at the Main-AIR
    level, the formula is literally the same as BEQ's. -/
theorem equiv_BNE
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : branch_ne_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_ne_compositional m r_main next_pc h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 BNE reduces to the pure-function block supplied by
    `PureSpec.execute_BNE_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` witness.

    Wraps `PureSpec.execute_BNE_pure_equiv`. -/
theorem equiv_BNE_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = let bne_output := PureSpec.execute_BNE_pure bne_input
        (do
          Sail.writeReg Register.nextPC bne_output.nextPC
          if bne_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !bne_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (bne_input.PC + BitVec.signExtend 64 bne_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BNE_pure_equiv bne_input imm r1 r2 h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem (Phase 2.5 D4a, D3 closed).**

    `execute_instruction` on an RV64 BNE equals the state computed by
    applying `bus_effect` to the circuit's execution and memory bus rows.

    **D3 closed the bus-emission obligation for shape (b).** BEQ and
    BNE share shape (b) — two execution-bus entries (pc read, nextpc
    write), empty memory bus — so this theorem reuses
    `bus_effect_matches_sail_beq` directly. No `h_bus_execute_matches_sail`
    hypothesis.

    **Hypotheses.**
    * Sail side (from `equiv_BNE_sail`): register readability
      (`h_input_r1`, `h_input_r2`), PC (`h_input_pc`), misa
      (`h_input_misa`), and ZisK `misa[C] = 0` (`h_misa_c`).
    * Bus structural: `h_exec_len`, multiplicities, pc match, and the
      pure-spec's `throws = false` + `success = true` discharges. All
      derivable from the PIL bus-emission spec; Phase 4 audit will
      fold these into a single derivation. -/
theorem equiv_BNE_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Structural bus hypotheses (Phase 2.5 D3 shape (b)).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure bne_input).nextPC)
    (h_not_throws : (PureSpec.execute_BNE_pure bne_input).throws = false)
    (h_success : (PureSpec.execute_BNE_pure bne_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BNE_sail state bne_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  -- Discharge the bus-side equation via the shape (b) lemma (shared
  -- with BEQ — shape (b) is the externally-routed branch shape).
  symm
  exact ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BNE_pure bne_input).nextPC
    (PureSpec.execute_BNE_pure bne_input).throws
    (PureSpec.execute_BNE_pure bne_input).success
    bne_input.PC bne_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success


/-- **Phase 5 V12 companion for BNE.** Drops `h_input_pc` via
    `chip_bus_hyps_branch_rrw` + `readReg_of_readReg_succ`. Other
    `h_input_*` stay — branch memory bus is empty, so rs1/rs2
    reads go via operation bus (not derivable from `h_bus` here). -/
theorem equiv_BNE_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Phase 5 V12: bus precondition + PC match (replaces h_input_pc).
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : bne_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    -- Structural bus hypotheses (Phase 2.5 D3 shape (b)).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure bne_input).nextPC)
    (h_not_throws : (PureSpec.execute_BNE_pure bne_input).throws = false)
    (h_success : (PureSpec.execute_BNE_pure bne_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = (bus_effect exec_row [] state).2
    := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_branch_rrw
    state exec_row h_exec_len h_e0_mult h_e1_mult h_bus
  have h_input_pc : state.regs.get? Register.PC = .some bne_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_BNE_metaplan state bne_input imm r1 r2 misa_val exec_row h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

end ZiskFv.Equivalence.BranchNotEqual
