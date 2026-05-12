import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Mul
import ZiskFv.Circuit.MulHSU
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Sail.mul
import ZiskFv.Sail.mulhsu
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned

/-!
End-to-end theorem for RV64 MULHSU. Mirrors `Equivalence.MulH` with:

* `transpile_MULHSU` (opcode 179) in place of `transpile_MULH` (opcode 181);
* `PureSpec.execute_MULH_mulhsu_pure` / `execute_MULH_mulhsu_pure_equiv`
  in place of their MULH counterparts — MULHSU's Sail-pure output is
  `execute_MUL_pure r1 r2 .MULHSU` (signed × unsigned, high 64 bits);
* `mulhsu_compositional` in place of `mulh_compositional`.
-/

namespace ZiskFv.Equivalence.MulHSU

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Mul
open ZiskFv.Circuit.MulHSU

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    MULHSU equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`execute_MUL_pure ... .MULHSU`) directly;
    that equation is derived internally from circuit witnesses via the
    `RdValDerivation.MulDivRemSigned.h_rd_val_mdrs_mulhsu` discharge
    lemma. -/
theorem equiv_MULHSU
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
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : mulhsu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- CIRCUIT-CONSTRAINT: byte-sum equals operand-form mixed-sign high-half product.
    (h_byte_sum_circuit :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
        + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (BitVec.ofInt 64
          ((mulhsu_input.r1_val.toInt * (mulhsu_input.r2_val.toNat : ℤ)) / 2 ^ 64)).toNat) :
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
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned.h_rd_val_mdrs_mulhsu
      mulhsu_input.r1_val mulhsu_input.r2_val e2
      h_e2_range.1 h_e2_range.2.1 h_e2_range.2.2.1 h_e2_range.2.2.2.1
      h_e2_range.2.2.2.2.1 h_e2_range.2.2.2.2.2.1
      h_e2_range.2.2.2.2.2.2.1 h_e2_range.2.2.2.2.2.2.2
      h_byte_sum_circuit
  rw [equiv_MULHSU_sail state mulhsu_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_MULH_mulhsu_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.MulHSU
