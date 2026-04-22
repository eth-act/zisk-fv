import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus
import ZiskFv.RV64D.mul
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 MUL (archetype A5). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_MUL`),
* the compositional MUL spec (`ZiskFv.Spec.Mul.mul_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_MULH_mul_pure_equiv`, newly closed Phase 2 A5),

into three metaplan-shaped theorems:

* `equiv_MUL` — circuit-level. Main's packed `c` equals Arith's packed
  result lanes, given the bus match.
* `equiv_MUL_sail` — Sail-level. `execute_instruction` on an RV64 MUL
  reduces to a monadic block writing `execute_MUL_pure .MUL` to rd.
* `equiv_MUL_metaplan` — metaplan target shape: Sail's
  `execute_instruction` equals `(bus_effect exec_row mem_row state).2`.

As with `equiv_BEQ_metaplan`, the bus-emission correctness hypothesis
`h_bus_execute_matches_sail` **and** the Arith-correctness hypothesis
(Arith's `c[]` = low 64 bits of `a * b`) are parameterized — Phase 4
audit derives them. A5's charter is the compositional Main+Arith proof
shape; the carry-chain-to-multiplication lift is Phase-4 scope.
-/

namespace ZiskFv.Equivalence.Mul

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Mul

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level MUL theorem (A5).** Given the MUL circuit-holds
    hypothesis (Main ADD-subset + Arith MUL-mode booleans + bus row
    match + mode witnesses on both AIRs), Main's Goldilocks-packed `c`
    lanes equal Arith's packed result lanes:

    `main_c_packed = arith_c_packed = (c[0] + c[1]*2^16) + bus_res1 * 2^32`.

    Wraps `Spec.Mul.mul_compositional`. The lifting from this field
    identity to `BitVec 64` MUL semantics is parameterized in
    `equiv_MUL_metaplan` via the standard `h_bus_execute_matches_sail`
    hypothesis plus an Arith-correctness obligation delegated to Phase 4. -/
theorem equiv_MUL
    (_rs1 _rs2 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h_circuit : mul_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_c_packed v r_arith :=
  mul_compositional m v r_main r_arith h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 MUL reduces to the pure-function block supplied by
    `PureSpec.execute_MULH_mul_pure`, given source-register readability
    and PC knowledge.

    Wraps `PureSpec.execute_MULH_mul_pure_equiv`. -/
theorem equiv_MUL_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mul_input : PureSpec.MulInput)
    (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mul_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mul_input.r2_val state)
    (h_input_rd : mul_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mul_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.Low
             signed_rs1 := srs1
             signed_rs2 := srs2 }))) state
      = let mul_output := PureSpec.execute_MULH_mul_pure mul_input
        (do
          Sail.writeReg Register.nextPC mul_output.nextPC
          match mul_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_MULH_mul_pure_equiv
    mul_input r1 r2 rd srs1 srs2 h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem.** The shape the original metaplan targets for
    RV64 MUL: Sail's `execute_instruction` on an RV64 MUL equals the
    state computed by applying `bus_effect` to the circuit's execution
    and memory bus rows.

    Composes `equiv_MUL_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. As in `equiv_ADD_metaplan`, the
    bus-emission-correctness obligation is parameterized; Phase 4 audit
    derives it from PIL-level bus emission plus the Arith-correctness
    proof (Arith carry chains → multiplication).

    **Hypotheses.**
    * Sail side (from `equiv_MUL_sail`): register readability
      (`h_input_r1`, `h_input_r2`), PC (`h_input_pc`), and the rd
      alias (`h_input_rd`).
    * Bus side: `h_bus_execute_matches_sail` asserts that the
      execution bus + memory bus rows, fed through `bus_effect`,
      match the Sail monadic block computed from
      `execute_MULH_mul_pure`. Combines bus emission correctness
      (PIL → bus) with Arith internal correctness (carry chains →
      `BitVec 64` product). -/
theorem equiv_MUL_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mul_input : PureSpec.MulInput)
    (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mul_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mul_input.r2_val state)
    (h_input_rd : mul_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mul_input.PC)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let mul_output := PureSpec.execute_MULH_mul_pure mul_input
           (do
             Sail.writeReg Register.nextPC mul_output.nextPC
             match mul_output.rd with
               | .some (rd, rd_val) => write_xreg rd rd_val
               | .none => pure ()
             pure (ExecutionResult.Retire_Success ())) state)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.Low
             signed_rs1 := srs1
             signed_rs2 := srs2 }))) state
      = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_MUL_sail state mul_input r1 r2 rd srs1 srs2
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.Mul
