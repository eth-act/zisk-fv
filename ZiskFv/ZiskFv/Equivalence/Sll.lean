import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Spec.Sll
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.sll
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 SLL (Phase 3A H1 — 64-bit sibling of SLLW).

Mirrors `Equivalence.Shift` (SLLW), with the direction unchanged but
the width flag flipped: `m32 = 0` here instead of `m32 = 1`. The
Main-AIR compositional lemma is the `ShiftArchetype` **passthrough**
instantiation at `OP_SLL = 33` — the high lanes `a_hi` / `b_hi` flow
verbatim to the `BinaryExtension` SM rather than being zeroed.

Emits three theorems matching the SLLW trio:

* `equiv_SLL` — circuit-level: bus `a_hi = m.a_1` and `b_hi = m.b_1`.
* `equiv_SLL_sail` — Sail-level: `execute_instruction` on a SLL RTYPE
  reduces to the pure spec block.
* `equiv_SLL_metaplan` — metaplan target. Uses shape (a) bus-effect
  (`bus_effect_matches_sail_alu_rrw`, hypothesis-free) from Phase 2.5 D3.
-/

namespace ZiskFv.Equivalence.Sll

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Sll

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SLL theorem.** Given the SLL-mode Main constraints
    (including `m32 = 0`) and the bus-match to a secondary entry, the
    entry's `a_hi` / `b_hi` fields carry the full 64-bit high lanes
    (passthrough). Direct instantiation of `ShiftArchetype`'s m32=0
    macro at `OP_SLL`. -/
theorem equiv_SLL
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : sll_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main :=
  sll_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SLL reduces to the pure-function block. Wraps
    `PureSpec.execute_RTYPE_sll_pure_equiv`. -/
theorem equiv_SLL_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sll_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sll_input.r2_val state)
    (h_input_rd : sll_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sll_input.PC) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
      = let sll_output := PureSpec.execute_RTYPE_sll_pure sll_input
        (do
          Sail.writeReg Register.nextPC sll_output.nextPC
          match sll_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_sll_pure_equiv
    sll_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 SLL
    equals the state computed by applying `bus_effect` to the
    circuit's execution + memory bus rows.

    Shape (a) — register-read + register-read + register-write,
    discharged via `bus_effect_matches_sail_alu_rrw`. No
    `h_bus_execute_matches_sail` parameter remains. -/
theorem equiv_SLL_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sll_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sll_input.r2_val state)
    (h_input_rd : sll_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sll_input.PC)
    -- Phase 2.5 D3 structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC)
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
      (match (PureSpec.execute_RTYPE_sll_pure sll_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SLL_sail state sll_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.execute_RTYPE_sll_pure sll_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.Sll
