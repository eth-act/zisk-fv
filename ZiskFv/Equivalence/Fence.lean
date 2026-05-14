import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Trusted.Transpiler
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

* `equiv_FENCE_circuit` — circuit-level (degenerate: there's no semantic
  payload, just PC advance via the standard handshake).
* `equiv_FENCE_sail` — Sail-level wrapper for `execute_FENCE_pure_equiv`.
* `equiv_FENCE` — the canonical shape combining
  Sail + bus-effect via `bus_effect_matches_sail_beq` (empty memory
  bus → same shape lemma BEQ uses).
-/

namespace ZiskFv.Equivalence.Fence

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 FENCE reduces to `Sail.writeReg Register.nextPC (PC + 4) ;
    pure RETIRE_SUCCESS`. Wraps `PureSpec.execute_FENCE_pure_equiv`.

    The M-mode privilege hypothesis is required to collapse Sail's
    `is_fiom_active` to the constant `false`. ZisK targets RV64IM
    Machine-mode only, so this is part of the trusted scope (see
    `RISC_V_assumptions` A1.1 in `RV64D/Auxiliaries.lean`). -/
lemma equiv_FENCE_sail
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
theorem equiv_FENCE
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

end ZiskFv.Equivalence.Fence
