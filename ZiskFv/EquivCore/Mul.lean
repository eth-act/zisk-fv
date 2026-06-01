import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.Mul
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.mul
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 MUL. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_MUL`),
* the compositional MUL spec (`ZiskFv.ZiskCircuit.Mul.mul_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_MULH_mul_pure_equiv`),

into three canonical theorems:

* `equiv_MUL_sail` — Sail-level. `execute_instruction` on an RV64 MUL
  reduces to a monadic block writing `execute_MUL_pure .MUL` to rd.
* `equiv_MUL` — canonical shape: Sail's
  `execute_instruction` equals `(bus_effect exec_row mem_row state).2`.
-/

namespace ZiskFv.EquivCore.Mul

open Goldilocks
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Mul


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 MUL reduces to the pure-function block supplied by
    `PureSpec.execute_MULH_mul_pure`, given source-register readability
    and PC knowledge.

    Wraps `PureSpec.execute_MULH_mul_pure_equiv`. -/
lemma equiv_MUL_sail
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

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    MUL equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`execute_MUL_pure ...`) directly; that
    equation is derived internally from circuit witnesses via the
    `WriteValueProofs.MulDivRemUnsigned.h_rd_val_mdru_mul` discharge
    lemma. -/
lemma equiv_MUL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mul_input : PureSpec.MulInput)
    (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
        (PureSpec.execute_MULH_mul_pure mul_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    -- The 22 loose (cy, cy-range, hC) caller-burden binders are now
    -- replaced by the row-level carry-chain constraint set + signed
    -- low-half bridge. Low MUL is modulo 2^64, so it does not need
    -- `na = nb = np = 0`; it only needs the XOR branch for the signed
    -- carry-chain identity.
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
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
        = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt bus.e2 4).val + (byteAt bus.e2 5).val * 256 + (byteAt bus.e2 6).val * 65536 + (byteAt bus.e2 7).val * 16777216
        = (v.c_2 r_a).val + (v.c_3 r_a).val * 65536)
    (h_rs1_value : mul_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mul_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.Low
             signed_rs1 := srs1
             signed_rs2 := srs2 }))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_mul_low_chunked
      mul_input.r1_val mul_input.r2_val e2 v r_a
      h0 h1 h2 h3 h4 h5 h6 h7
      h_chain h_nr h_sext h_m32 h_div h_na_bool h_nb_bool h_np_xor
      h_chunk_ranges h_carry_ranges
      h_byte_lo h_byte_hi h_rs1_value h_rs2_value
  rw [equiv_MUL_sail state mul_input r1 r2 rd srs1 srs2
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_MULH_mul_pure mul_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_MULH_mul_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.EquivCore.Mul
