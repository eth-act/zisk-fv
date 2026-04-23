import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Spec.Remu
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.remu
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 **REMU** (Phase 3C T-D). REMU is the
**secondary** lane on an unsigned-DIV Arith row. Differs from
`Equivalence.Rem` only in the opcode literal (185 vs 187), the pure
spec (`execute_DIVREM_remu_pure` / `_equiv`), and the Sail instruction
payload (`instruction.REM (r2, r1, rd, true)`).

Three metaplan-shaped theorems: `equiv_REMU`, `equiv_REMU_sail`,
`equiv_REMU_metaplan`. Arith-internal correctness (carry chains →
unsigned 64-bit remainder) is delegated to Phase 4 audit.
-/

namespace ZiskFv.Equivalence.Remu

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Mul
open ZiskFv.Spec.Remu
open ZiskFv.Tactics.ArithSMArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level REMU theorem.** Main's packed `c` equals Arith's
    packed remainder (`d[]`) under the REMU circuit-holds hypothesis.
    Wraps `Spec.Remu.remu_compositional`. -/
theorem equiv_REMU
    (_rs1 _rs2 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ)
    (h_circuit : remu_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_remainder_packed v r_arith :=
  remu_compositional m v r_main r_arith h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 REMU reduces to the pure-function block supplied by
    `PureSpec.execute_DIVREM_remu_pure`. Wraps
    `PureSpec.execute_DIVREM_remu_pure_equiv`. -/
theorem equiv_REMU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remu_input.r2_val state)
    (h_input_rd : remu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remu_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = let remu_output := PureSpec.execute_DIVREM_remu_pure remu_input
        (do
          Sail.writeReg Register.nextPC remu_output.nextPC
          match remu_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_remu_pure_equiv
    remu_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 REMU
    equals `(bus_effect exec_row mem_row state).2`. Composes
    `equiv_REMU_sail` with `bus_effect_matches_sail_alu_rrw` (shape
    (a), RRW). Structural bus hypotheses are parameterized — Phase 4
    audit derives them. -/
theorem equiv_REMU_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remu_input.r2_val state)
    (h_input_rd : remu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remu_input.PC)
    -- Structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC)
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
      (match (PureSpec.execute_DIVREM_remu_pure remu_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_REMU_sail state remu_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.execute_DIVREM_remu_pure remu_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.Remu
