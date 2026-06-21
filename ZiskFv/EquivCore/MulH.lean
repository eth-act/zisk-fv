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
import ZiskFv.SailSpec.mulh
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 MULH (signed × signed, high half). Mirrors
`EquivCore.MulHU` (unsigned high half) and `EquivCore.Mul` (low half), but:

* uses `PureSpec.execute_MULH_mulh_pure` / `execute_MULH_mulh_pure_equiv`;
* derives the rd-write via the new high-half signed discharge lemma
  `WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_mulh_chunked`;
* carries the **SIGN-RANGE RESIDUAL** `h_sign_a`/`h_sign_b` — the caller-supplied
  facts `na = MSB(op1)`, `nb = MSB(op2)`.  The real ZisK ArithMul circuit pins
  these via the indexed `range_ab` POS/NEG lookup (`arith.pil:286/289/303`); the
  FV extraction collapses that to the full `rangeTable16`, so the equation is
  ASSUMED here (an honest caller satisfies it for every real trace), not derived.
  See `trust/trusted-base.md` (sign-range residual) and `trust/defects.md`.
-/

namespace ZiskFv.EquivCore.MulH

open Goldilocks
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Mul
open ZiskFv.PackedBitVec.MulNoWrap (packed4)


/-- **Sail-level companion.** `execute_instruction` on an RV64 MULH reduces to
    the pure-function block `PureSpec.execute_MULH_mulh_pure`. -/
lemma equiv_MULH_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulh_input : PureSpec.MulhInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulh_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulh_input.r2_val state)
    (h_input_rd : mulh_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulh_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Signed }))) state
      = let mulh_output := PureSpec.execute_MULH_mulh_pure mulh_input
        (do
          Sail.writeReg Register.nextPC mulh_output.nextPC
          match mulh_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_MULH_mulh_pure_equiv
    mulh_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64 MULH
    equals the state computed by applying `bus_effect` to the circuit's rows.

    Non-OUTPUT-EQ: the spec output is derived internally from circuit witnesses
    plus the explicit SIGN-RANGE RESIDUAL (`h_sign_a`/`h_sign_b`). -/
lemma equiv_MULH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulh_input : PureSpec.MulhInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
        (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
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
    (h_rs1_value : mulh_input.r1_val.toNat
      = packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulh_input.r2_val.toNat
      = packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val)
    -- SIGN-RANGE RESIDUAL: the sign witnesses are the operand MSBs (carried, not
    -- derived; see module docstring).
    (h_sign_a : (v.na r_a).val
      = if 2 ^ 63 ≤ packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val
          then 1 else 0)
    (h_sign_b : (v.nb r_a).val
      = if 2 ^ 63 ≤ packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val
          then 1 else 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Signed }))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- chunk-range bounds for the operand packings.
  have h_chunk_ranges_arg := h_chunk_ranges
  obtain ⟨h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, _, _, _, _, _, _, _, _⟩ :=
    h_chunk_ranges_arg
  -- SIGN-RANGE RESIDUAL → signed operand bridges via the generic Sail-state bridge.
  have h_r1 : mulh_input.r1_val.toInt
      = (packed4 (v.a_0 r_a).val (v.a_1 r_a).val (v.a_2 r_a).val (v.a_3 r_a).val : ℤ)
          - (v.na r_a).val * (2:ℤ)^64 :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.signed_packed_toInt_eq_of_read_xreg
      h_input_r1 h_rs1_value ⟨h_a0, h_a1, h_a2, h_a3⟩ h_sign_a
  have h_r2 : mulh_input.r2_val.toInt
      = (packed4 (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
          - (v.nb r_a).val * (2:ℤ)^64 :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.signed_packed_toInt_eq_of_read_xreg
      h_input_r2 h_rs2_value ⟨h_b0, h_b1, h_b2, h_b3⟩ h_sign_b
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_mulh_chunked
      mulh_input.r1_val mulh_input.r2_val e2 v r_a
      h0 h1 h2 h3 h4 h5 h6 h7
      h_chain h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_bool h_np_xor
      h_chunk_ranges h_carry_ranges
      h_byte_lo h_byte_hi h_r1 h_r2
  rw [equiv_MULH_sail state mulh_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_MULH_mulh_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.EquivCore.MulH
