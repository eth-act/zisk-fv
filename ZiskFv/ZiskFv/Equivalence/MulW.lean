import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Spec.Mul
import ZiskFv.Spec.MulW
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.mulw
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 MULW (Phase 3A M3). MULW is the 32-bit
word variant of MUL — `m32 = 1` on both Main and Arith — which means
the Main spec must be authored with a MULW-specific mode predicate
(the archetype macro hardcodes `m32 = 0`). See `Spec.MulW` for the
compositional statement.

Three metaplan-shaped theorems:

* `equiv_MULW` — circuit-level. Main's packed `c` equals Arith's
  packed result lanes (same identity as MUL / MULH / MULHU / MULHSU —
  the compositional bus projection is uniform across the MUL family,
  independent of `m32`).
* `equiv_MULW_sail` — Sail-level. `execute_instruction` on an RV64
  MULW reduces to a monadic block writing the sign-extended 32-bit
  product to rd.
* `equiv_MULW_metaplan` — metaplan target shape, discharged via
  `bus_effect_matches_sail_alu_rrw` (shape (a), hypothesis-free —
  MULW uses the same register-read + register-read + register-write
  shape as MUL / MULH / SLLW).

Like the rest of the MUL family, the Arith-internal correctness
(Arith carry chains → `sign_extend_32_to_64 (low32 a * low32 b)`) is
the Phase 4 audit's scope; it enters `equiv_MULW_metaplan` via the
structural bus hypotheses.
-/

namespace ZiskFv.Equivalence.MulW

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Mul
open ZiskFv.Spec.MulW

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level MULW theorem (Phase 3A M3).** Main's packed `c`
    equals Arith's packed result lanes, given the MULW circuit-holds
    hypothesis. Wraps `Spec.MulW.mulw_compositional`. -/
theorem equiv_MULW
    (_rs1 _rs2 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h_circuit : mulw_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_c_packed v r_arith :=
  mulw_compositional m v r_main r_arith h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 MULW reduces to the pure-function block supplied by
    `PureSpec.execute_MULW_pure`, given source-register readability
    and PC knowledge. Wraps `PureSpec.execute_MULW_pure_equiv`. -/
theorem equiv_MULW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulw_input.r2_val state)
    (h_input_rd : mulw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = let mulw_output := PureSpec.execute_MULW_pure mulw_input
        (do
          Sail.writeReg Register.nextPC mulw_output.nextPC
          match mulw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_MULW_pure_equiv
    mulw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem (Phase 3A M3).** Sail's `execute_instruction`
    on an RV64 MULW equals the state computed by applying `bus_effect`
    to the circuit's execution and memory bus rows.

    Composes `equiv_MULW_sail` with shape-(a) bus-matching. Hypothesis-
    free for `h_bus_execute_matches_sail` — MULW reuses MUL/MULH's
    register-read + register-read + register-write bus shape; Phase 2.5
    D3 closed shape (a). -/
theorem equiv_MULW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulw_input.r2_val state)
    (h_input_rd : mulw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulw_input.PC)
    -- Phase 2.5 D3: structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULW_pure mulw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_idx : mulw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = PureSpec.execute_MULW_pure_val mulw_input.r1_val mulw_input.r2_val) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_MULW_sail state mulw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_MULW_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.MulW
