import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Mul
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.mul
import ZiskFv.RV64D.BusEffect
import ZiskFv.Airs.BusHypotheses

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
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mul_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mul_input.r2_val state)
    (h_input_rd : mul_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mul_input.PC)
    -- Phase 2.5 D3: structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mul_pure mul_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses.
    -- `h_rd_idx` ties the circuit rd-pointer to the Sail rd;
    -- `h_rd_val` ties the 8 byte lanes to the pure-spec product.
    -- Both are derivable from the Main+Arith circuit hypotheses
    -- via Bridge 1 (constraint 46), Bridge 2 (field composition),
    -- and Bridge 3 (`Fundamentals/PackedBitVec.lean`) — plus the
    -- scope-honest arith_table permutation witness.
    (h_rd_idx : mul_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_MUL_pure mul_input.r1_val mul_input.r2_val .MUL) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.Low
             signed_rs1 := srs1
             signed_rs2 := srs2 }))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_MUL_sail state mul_input r1 r2 rd srs1 srs2
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_MULH_mul_pure mul_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  -- Discharge the rd-match branch from the decomposed hypotheses.
  -- Unfold the pure spec's dite on `mul_input.rd = 0`, rewrite it
  -- through `h_rd_idx` to a dite on `wrap_to_regidx e2.ptr = 0`
  -- (matching the LHS shape), then split on that condition.
  simp only [PureSpec.execute_MULH_mul_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · -- Zero case: both sides reduce to `pure ()`.
    simp only [bind, pure, EStateM.bind, EStateM.pure]
  · -- Nonzero case: both sides write the same rd with the same value.
    rw [h_rd_val]


/-- **Phase 5 V12 companion.** Drops `h_input_r1` / `h_input_r2` / 
    `h_input_pc` / `h_input_rd` in favor of a single `h_bus :
    (bus_effect ...).1` plus ptr/value match hypotheses.
    Delegates to `equiv_MUL_metaplan` after chip_bus_hyps + match composition.  -/
theorem equiv_MUL_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mul_input : PureSpec.MulInput)
    (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Phase 2.5 D3: structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mul_pure mul_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 5 V12: bus precondition + ptr/value match (replaces h_input_r1/r2/pc/rd).
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r1_val : mul_input.r1_val
      = U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                    e0.x4, e0.x5, e0.x6, e0.x7])
    (h_r2_ptr : regidx_to_fin r2 = Transpiler.wrap_to_regidx e1.ptr)
    (h_r2_val : mul_input.r2_val
      = U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                    e1.x4, e1.x5, e1.x6, e1.x7])
    (h_pc : mul_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses.
    -- `h_rd_idx` ties the circuit rd-pointer to the Sail rd;
    -- `h_rd_val` ties the 8 byte lanes to the pure-spec product.
    -- Both are derivable from the Main+Arith circuit hypotheses
    -- via Bridge 1 (constraint 46), Bridge 2 (field composition),
    -- and Bridge 3 (`Fundamentals/PackedBitVec.lean`) — plus the
    -- scope-honest arith_table permutation witness.
    (h_rd_idx : mul_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_MUL_pure mul_input.r1_val mul_input.r2_val .MUL) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.Low
             signed_rs1 := srs1
             signed_rs2 := srs2 }))) state
      = (bus_effect exec_row [e0, e1, e2] state).2
    := by
  obtain ⟨h_pc_read, h_rs1_read, h_rs2_read⟩ :=
    ZiskFv.Airs.BusHypotheses.chip_bus_hyps_alu_rrw
      state exec_row e0 e1 e2
      h_exec_len h_e0_mult h_e1_mult
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
      h_bus
  have h_input_r1 :
      read_xreg (regidx_to_fin r1) state
        = EStateM.Result.ok mul_input.r1_val state := by
    rw [h_r1_ptr, h_r1_val]; exact h_rs1_read
  have h_input_r2 :
      read_xreg (regidx_to_fin r2) state
        = EStateM.Result.ok mul_input.r2_val state := by
    rw [h_r2_ptr, h_r2_val]; exact h_rs2_read
  have h_input_rd : mul_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some mul_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_MUL_metaplan state mul_input r1 r2 rd srs1 srs2 exec_row e0 e1 e2 h_input_r1 h_input_r2 h_input_rd h_input_pc h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_rd_val

end ZiskFv.Equivalence.Mul
