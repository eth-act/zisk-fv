import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Spec.Addw
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.addw
import ZiskFv.RV64D.BusEffect
import ZiskFv.Tactics.RTypeWArchetype

/-!
End-to-end theorem for RV64 ADDW (Phase 3C T-W). Mirrors the shape
of `Equivalence.Sub` / `Equivalence.MulW` with:

* `transpile_ADDW` (opcode `OP_ADD_W = 26`, `m32 = 1`);
* `PureSpec.execute_RTYPE_addw_pure` / `execute_RTYPE_addw_pure_equiv`
  from Phase 3B;
* `addw_compositional` (the RTypeWArchetype specialization at
  `OP_ADD_W`).

Three metaplan-shaped theorems:

* `equiv_ADDW` — circuit-level: Main's packed `c` equals the bus
  entry's packed `c`.
* `equiv_ADDW_sail` — Sail-level: `execute_instruction` reduces to
  the pure-spec block.
* `equiv_ADDW_metaplan` — metaplan target shape, discharged via
  shape (a) bus-emission (`bus_effect_matches_sail_alu_rrw` —
  register-read + register-read + register-write, same as
  SUB/MUL/MULW).
-/

namespace ZiskFv.Equivalence.Addw

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Addw
open ZiskFv.Tactics.RTypeWArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level ADDW theorem (Phase 3C T-W).** Main's packed `c`
    equals the bus entry's packed `c` lanes. Wraps
    `Spec.Addw.addw_compositional`. -/
theorem equiv_ADDW
    (_rs1 _rs2 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : addw_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  addw_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `execute_instruction` on an RV64 ADDW
    reduces to `PureSpec.execute_RTYPE_addw_pure`. Wraps
    `PureSpec.execute_RTYPE_addw_pure_equiv`. -/
theorem equiv_ADDW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addw_input : PureSpec.AddwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok addw_input.r2_val state)
    (h_input_rd : addw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
      = let addw_output := PureSpec.execute_RTYPE_addw_pure addw_input
        (do
          Sail.writeReg Register.nextPC addw_output.nextPC
          match addw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_addw_pure_equiv
    addw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem (Phase 3C T-W).** Sail's `execute_instruction`
    on an RV64 ADDW equals `(bus_effect exec_row mem_row state).2`.
    Shape (a) — register-read + register-read + register-write. -/
theorem equiv_ADDW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addw_input : PureSpec.AddwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok addw_input.r2_val state)
    (h_input_rd : addw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addw_input.PC)
    -- Phase-4-derivable structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_match :
      (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
        (pure () : SailM Unit)
      else
        let val := U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                                e2.x4, e2.x5, e2.x6, e2.x7]
        let reg_idx : Finset.Icc 1 31 :=
          ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
        write_xreg reg_idx val)
      =
      (match (PureSpec.execute_RTYPE_addw_pure addw_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_ADDW_sail state addw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.execute_RTYPE_addw_pure addw_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.Addw
