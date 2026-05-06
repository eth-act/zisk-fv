import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Sail.fence
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64I FENCE.

FENCE is a memory-ordering hint that, on ZisK's single-threaded
zkVM, reduces to "advance PC by 4." The Sail body
(`execute_FENCE`) is a no-op composition (barrier match arms all
collapse to `pure ()` via `sail_barrier`). The ZisK transpiler
emits a single Internal-op row with all sources zeroed and
`jmp_offset = 4` (`riscv2zisk_context.rs:228 → fn nop`).

Three theorems mirroring the BEQ pattern (shape-(b) — empty memory bus):

* `equiv_FENCE` — circuit-level (degenerate: there's no semantic
  payload, just PC advance via the standard handshake).
* `equiv_FENCE_sail` — Sail-level wrapper for `execute_FENCE_pure_equiv`.
* `equiv_FENCE_metaplan` — the metaplan-target shape combining
  Sail + bus-effect via `bus_effect_matches_sail_beq` (empty memory
  bus → same shape lemma BEQ uses).
-/

namespace ZiskFv.Equivalence.Fence

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main

/-- **Circuit-level FENCE theorem.** Trivial: FENCE has no semantic
    output — its Main row is fully pinned by `transpile_FENCE` (op =
    OP_FLAG, all sources zero, jmp_offset = 4). The "circuit-level
    correctness" is just the trivial proposition `True`, which we
    state explicitly to keep the theorem-shape uniform across
    opcodes. -/
theorem equiv_FENCE
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (state : RV64State)
    (h_isext : m.is_external_op r_main = 0)
    (h_op : m.op r_main = OP_FLAG) :
    m.a_0 r_main = 0 ∧ m.a_1 r_main = 0
    ∧ m.b_0 r_main = 0 ∧ m.b_1 r_main = 0
    ∧ m.jmp_offset1 r_main = 4 ∧ m.jmp_offset2 r_main = 4
    ∧ m.m32 r_main = 0 := by
  obtain ⟨h_m32, _, _, h_j1, h_j2, h_a0, h_a1, h_b0, h_b1⟩ :=
    transpile_FENCE m r_main state h_isext h_op
  exact ⟨h_a0, h_a1, h_b0, h_b1, h_j1, h_j2, h_m32⟩

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 FENCE reduces to `Sail.writeReg Register.nextPC (PC + 4) ;
    pure RETIRE_SUCCESS`. Wraps `PureSpec.execute_FENCE_pure_equiv`.

    The M-mode privilege hypothesis is required to collapse Sail's
    `is_fiom_active` to the constant `false`. ZisK targets RV64IM
    Machine-mode only, so this is part of the trusted scope (see
    `RISC_V_assumptions` A1.1 in `RV64D/Auxiliaries.lean`). -/
theorem equiv_FENCE_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (h_input_pc : state.regs.get? Register.PC = .some fence_input.PC)
    (h_input_priv :
      state.regs.get? Register.cur_privilege = .some Privilege.Machine) :
    execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state =
    let fence_output := PureSpec.execute_FENCE_pure fence_input
    (do
      Sail.writeReg Register.nextPC fence_output.nextPC
      pure (ExecutionResult.Retire_Success ())
    ) state :=
  PureSpec.execute_FENCE_pure_equiv fence_input fm pred succ rs rd
    h_input_pc h_input_priv

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64
    FENCE equals `(bus_effect exec_row [] state).2`. Composes
    `equiv_FENCE_sail` with `bus_effect_matches_sail_beq` (FENCE
    uses the same empty-memory-bus shape as branches). -/
theorem equiv_FENCE_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_pc : state.regs.get? Register.PC = .some fence_input.PC)
    (h_input_priv :
      state.regs.get? Register.cur_privilege = .some Privilege.Machine)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_FENCE_pure fence_input).nextPC) :
    execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_FENCE_sail state fence_input fm pred succ rs rd h_input_pc
        h_input_priv]
  symm
  -- Use bus_effect_matches_sail_beq with throws=false, success=true.
  -- The beq_PC / beq_imm parameters are unused under those flags;
  -- pass dummies.
  have h_bus_eq := ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq
    (imm_width := 1)
    state exec_row
    (PureSpec.execute_FENCE_pure fence_input).nextPC
    false true
    (0#64) (0#1)
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches rfl rfl
  rw [h_bus_eq]
  -- Both inner if-chains reduce to `pure RETIRE_SUCCESS`.
  simp

/-- **V12 companion — bus-derived form.** Drops `h_input_pc` via
    `chip_bus_hyps_branch_rrw` + `readReg_of_readReg_succ`. -/
theorem equiv_FENCE_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_priv :
      state.regs.get? Register.cur_privilege = .some Privilege.Machine)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_FENCE_pure fence_input).nextPC)
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : fence_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val) :
    execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
      = (bus_effect exec_row [] state).2 := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_branch_rrw
    state exec_row h_exec_len h_e0_mult h_e1_mult h_bus
  have h_input_pc : state.regs.get? Register.PC = .some fence_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_FENCE_metaplan state fence_input fm pred succ rs rd
    exec_row h_input_pc h_input_priv h_exec_len h_e0_mult h_e1_mult
    h_nextPC_matches

/-- Constructor: build a `PureSpec.FenceInput` from exec_row PC. -/
def FenceInput_of_bus
    (exec_row : List (Interaction.ExecutionBusEntry FGL)) : PureSpec.FenceInput :=
  { PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for FENCE.** Bus-derived input form. -/
theorem equiv_FENCE_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_priv :
      state.regs.get? Register.cur_privilege = .some Privilege.Machine)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_FENCE_pure (FenceInput_of_bus exec_row)).nextPC)
    (h_bus : (bus_effect exec_row [] state).1) :
    execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
      = (bus_effect exec_row [] state).2 :=
  equiv_FENCE_metaplan_from_bus state (FenceInput_of_bus exec_row)
    fm pred succ rs rd exec_row h_input_priv
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_bus rfl

/-- **Track Q POC for FENCE.** Operation-bus companion to
    `equiv_FENCE_metaplan_from_bus`.

    FENCE has no rs1/rs2 reads at the Sail level (its body is a no-op
    barrier composition) and no operation-bus emission at the Main AIR
    level (`is_external_op = 0`, all `a/b` lanes pinned to zero by
    `transpile_FENCE`). The op-bus precondition is therefore vacuously
    `True`: any caller can supply an empty op-bus list, whose
    `op_bus_effect`-`.1` is `True` by definition.

    We expose the `_op_bus` companion shape uniformly with the branch
    family for caller ergonomics — the Track Q closure becomes
    "every shape-(b) opcode ships an `_op_bus` form" rather than
    "every shape-(b) opcode ships an `_op_bus` form, except FENCE." -/
theorem equiv_FENCE_metaplan_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (op_bus : List (ZiskFv.Airs.OperationBus.OperationBusEntry FGL))
    -- Op-bus precondition (vacuously discharged when `op_bus = []`).
    -- `regidx_to_fin rs` is the natural choice for the rs1 slot of any
    -- entry, but FENCE's lanes are all zero so the equality is trivial.
    (_h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect op_bus state
                    (regidx_to_fin rs) (regidx_to_fin rs)).1)
    (h_input_priv :
      state.regs.get? Register.cur_privilege = .some Privilege.Machine)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_FENCE_pure fence_input).nextPC)
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : fence_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val) :
    execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
      = (bus_effect exec_row [] state).2 :=
  equiv_FENCE_metaplan_from_bus state fence_input fm pred succ rs rd exec_row
    h_input_priv h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_bus h_pc

end ZiskFv.Equivalence.Fence
