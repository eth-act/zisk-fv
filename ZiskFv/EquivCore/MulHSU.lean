import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.ZiskCircuit.Mul
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.mul
import ZiskFv.SailSpec.mulhsu
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 MULHSU (signed × unsigned, high half). Mirrors
`EquivCore.MulH`, but:

* uses `PureSpec.execute_MULH_mulhsu_pure` / `execute_MULH_mulhsu_pure_equiv`;
* the second operand is UNSIGNED, so the table pins `nb = 0` and only ONE
  SIGN-RANGE RESIDUAL `h_sign_a` (= `na = MSB(op1)`) is carried;
* derives the rd-write via `h_rd_val_mdrs_mulhsu_chunked`.

The sign-range residual is ASSUMED, not derived in-model (same extraction-scope
gap as MULH; `arith.pil:286/289/303`).  See `trust/trusted-base.md` /
`trust/defects.md`.
-/

namespace ZiskFv.EquivCore.MulHSU

open Goldilocks
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Mul
open ZiskFv.PackedBitVec.MulNoWrap (packed4)


/-- **Sail-level companion.** `execute_instruction` on an RV64 MULHSU reduces to
    the pure-function block `PureSpec.execute_MULH_mulhsu_pure`. -/
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

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64 MULHSU
    equals the state computed by applying `bus_effect` to the circuit's rows.

    Non-OUTPUT-EQ: the spec output is derived internally from circuit witnesses
    plus the explicit SIGN-RANGE RESIDUAL (`h_sign_a` only; op2 is unsigned). -/
lemma equiv_MULHSU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhsu_input : PureSpec.MulhsuInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    (h_nb_zero : v.nb r_a = 0)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_np_bool : v.np r_a = 0 ∨ v.np r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
          - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulChunkRangesAt v r_a)
    (h_carry_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithMulSignedCarryRangesAt v r_a)
    (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0)
    (h_div : v.div r_a = 0)
    (h_byte_lo :
      (byteAt bus.e2 0).val + (byteAt bus.e2 1).val * 256 + (byteAt bus.e2 2).val * 65536 + (byteAt bus.e2 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt bus.e2 4).val + (byteAt bus.e2 5).val * 256 + (byteAt bus.e2 6).val * 65536 + (byteAt bus.e2 7).val * 16777216
        = (v.d_2 r_a).val + (v.d_3 r_a).val * 65536)
    (h_rs1_value : mulhsu_input.r1_val.toNat
      = packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhsu_input.r2_val.toNat
      = packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val)
    -- SIGN-RANGE RESIDUAL on op1 only (op2 unsigned); carried, not derived.
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val
          then 1 else 0) :
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
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  have h_chunk_ranges_arg := h_chunk_ranges
  obtain ⟨h_a0, h_a1, h_a2, h_a3, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    h_chunk_ranges_arg
  -- SIGN-RANGE RESIDUAL → signed op1 bridge; op2 enters in unsigned `toNat` form.
  have h_r1 : mulhsu_input.r1_val.toInt
      = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
          - (v.na r_a).val * (2:ℤ)^64 :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.signed_packed_toInt_eq_of_read_xreg
      h_input_r1 h_rs1_value ⟨h_a0, h_a1, h_a2, h_a3⟩ h_sign_a
  have h_r2 : (mulhsu_input.r2_val.toNat : ℤ)
      = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ) := by
    rw [h_rs2_value]
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_mulhsu_chunked
      mulhsu_input.r1_val mulhsu_input.r2_val e2 v r_a
      h0 h1 h2 h3 h4 h5 h6 h7
      h_chain h_nr h_sext h_m32 h_div h_nb_zero h_na_bool h_np_bool h_np_xor
      h_chunk_ranges h_carry_ranges
      h_byte_lo h_byte_hi h_r1 h_r2
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

end ZiskFv.EquivCore.MulHSU
