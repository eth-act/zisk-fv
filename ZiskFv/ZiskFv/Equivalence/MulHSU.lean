import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Spec.MulHSU
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.mul
import ZiskFv.RV64D.mulhsu
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 MULHSU (Phase 3A M2). Mirrors
`Equivalence.MulH` with:

* `transpile_MULHSU` (opcode 179) in place of `transpile_MULH` (opcode 181);
* `PureSpec.execute_MULH_mulhsu_pure` / `execute_MULH_mulhsu_pure_equiv`
  in place of their MULH counterparts — MULHSU's Sail-pure output is
  `execute_MUL_pure r1 r2 .MULHSU` (signed × unsigned, high 64 bits);
* `mulhsu_compositional` (MULHSU's instantiation of the archetype
  bus-match) in place of `mulh_compositional`.
-/

namespace ZiskFv.Equivalence.MulHSU

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Mul
open ZiskFv.Spec.MulHSU

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level MULHSU theorem (Phase 3A M2).** Main's packed `c`
    equals Arith's packed result lanes. Wraps
    `Spec.MulHSU.mulhsu_compositional`. -/
theorem equiv_MULHSU
    (_rs1 _rs2 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h_circuit : mulhsu_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_c_packed v r_arith :=
  mulhsu_compositional m v r_main r_arith h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 MULHSU (signed × unsigned, High half) reduces to the pure-
    function block supplied by `PureSpec.execute_MULH_mulhsu_pure`. -/
theorem equiv_MULHSU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhsu_input : PureSpec.MulhsuInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulhsu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulhsu_input.r2_val state)
    (h_input_rd : mulhsu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulhsu_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) state
      = let mulhsu_output := PureSpec.execute_MULH_mulhsu_pure mulhsu_input
        (do
          Sail.writeReg Register.nextPC mulhsu_output.nextPC
          match mulhsu_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_MULH_mulhsu_pure_equiv
    mulhsu_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem (Phase 3A M2).** Sail's `execute_instruction`
    on an RV64 MULHSU equals the state computed by applying
    `bus_effect` to the circuit's execution and memory bus rows.

    Composes `equiv_MULHSU_sail` with shape-(a) bus-matching. -/
theorem equiv_MULHSU_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhsu_input : PureSpec.MulhsuInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulhsu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulhsu_input.r2_val state)
    (h_input_rd : mulhsu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulhsu_input.PC)
    -- Phase 2.5 D3: structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC)
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
      (match (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_MULHSU_sail state mulhsu_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.MulHSU
