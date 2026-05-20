import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.Bits.PackedBitVec.MulNoWrap
import ZiskFv.ZiskCircuit.Mul
import ZiskFv.ZiskCircuit.MulHSU
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.SailSpec.mul
import ZiskFv.SailSpec.mulhsu
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence_v1.WriteValueProofs.MulDivRemSigned
import ZiskFv.Equivalence_v1.Promises.RType
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 MULHSU. Mirrors `Equivalence.MulH` with:

* `transpile_MULHSU` (opcode 179) in place of `transpile_MULH` (opcode 181);
* `PureSpec.execute_MULH_mulhsu_pure` / `execute_MULH_mulhsu_pure_equiv`
  in place of their MULH counterparts — MULHSU's Sail-pure output is
  `execute_MUL_pure r1 r2 .MULHSU` (signed × unsigned, high 64 bits);
* `mulhsu_compositional` in place of `mulh_compositional`.
-/

namespace ZiskFv.Equivalence_v1.MulHSU

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Mul
open ZiskFv.ZiskCircuit.MulHSU


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 MULHSU (signed × unsigned, High half) reduces to the pure-
    function block supplied by `PureSpec.execute_MULH_mulhsu_pure`. -/
lemma equiv_MULHSU_sail
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
    `WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_mulhsu_chunked`
    discharge lemma. -/
theorem equiv_MULHSU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhsu_input : PureSpec.MulhsuInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence_v1.Promises.RTypePromises
        state mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Structural-unpacking ADDED binders per
    -- `trust/structural-unpacking-exceptions.txt` MULHSU entry.
    -- Note: `h_nb` is a real pin (`= 0`) rather than a placeholder —
    -- the AIR's arith_table pins `nb = 0` for MULHSU rows
    -- (`OP_MULSUH = 179`), since rs2 is interpreted as unsigned.
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    (h_na : v.na r_a = v.na r_a)
    (h_nb : v.nb r_a = 0)
    (h_np : v.np r_a = v.np r_a)
    (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 0)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
                * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_byte_lo :
      bus.e2.x0.val + bus.e2.x1.val * 256 + bus.e2.x2.val * 65536 + bus.e2.x3.val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_byte_hi :
      bus.e2.x4.val + bus.e2.x5.val * 256 + bus.e2.x6.val * 65536 + bus.e2.x7.val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536)
    (h_rs1_value :
      mulhsu_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
            - (v.na r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      (mulhsu_input.r2_val.toNat : ℤ)
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  have h_rd_val :=
    ZiskFv.Equivalence_v1.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_mulhsu_chunked
      mulhsu_input.r1_val mulhsu_input.r2_val e2 v r_a
      h_e2_range.1 h_e2_range.2.1 h_e2_range.2.2.1 h_e2_range.2.2.2.1
      h_e2_range.2.2.2.2.1 h_e2_range.2.2.2.2.2.1
      h_e2_range.2.2.2.2.2.2.1 h_e2_range.2.2.2.2.2.2.2
      h_chain h_na h_nb h_np h_nr h_sext h_m32 h_div
      h_na_bool h_nb_bool h_np_xor h_byte_lo h_byte_hi h_rs1_value h_rs2_value
  rw [equiv_MULHSU_sail state mulhsu_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_MULH_mulhsu_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence_v1.MulHSU
