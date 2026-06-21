import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.Bits.PackedBitVec.MulNoWrap
import ZiskFv.Bits.PackedBitVec.SignedChunkLift
import ZiskFv.ZiskCircuit.Div
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.div
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 **DIV**. This legacy core is retained for
imports, but the canonical DIV theorem is now defect-gated by
`ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS` until the dynamic Arith
division witness route is proved. The Sail-level companion still reduces
through `PureSpec.execute_DIVREM_div_pure_equiv`.

* `equiv_DIV_sail` — Sail-level. `execute_instruction` on an RV64 DIV
  reduces to the pure-function block.
* `equiv_DIV` — canonical shape: Sail's
  `execute_instruction` equals `(bus_effect exec_row mem_row state).2`.

Shape (a) (RTYPE RRW — register read + register read + register write)
is reused from MUL, so bus matching uses `bus_effect_matches_sail_alu_rrw`.
-/

namespace ZiskFv.EquivCore.Div

open Goldilocks
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Mul
open ZiskFv.ZiskCircuit.Div
open ZiskFv.Tactics.ArithSMArchetype


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 DIV reduces to the pure-function block supplied by
    `PureSpec.execute_DIVREM_div_pure`. Wraps
    `PureSpec.execute_DIVREM_div_pure_equiv`. -/
lemma equiv_DIV_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok div_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok div_input.r2_val state)
    (h_input_rd : div_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some div_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = let div_output := PureSpec.execute_DIVREM_div_pure div_input
        (do
          Sail.writeReg Register.nextPC div_output.nextPC
          match div_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_div_pure_equiv
    div_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    DIV equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_div` discharge
    lemma. -/
lemma equiv_DIV
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    -- Structural-unpacking ADDED binders per `trust/structural-unpacking-exceptions.txt` DIV entry.
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (chunk_ranges : ZiskFv.AirsClean.ArithDiv.ChunkRangeLookupWitness v r_a)
    (carry_ranges : ZiskFv.AirsClean.ArithDiv.SignedCarryRangeLookupWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
                * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
              ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
              ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 1)
    (h_byte_lo :
      (byteAt bus.e2 0).val + (byteAt bus.e2 1).val * 256 + (byteAt bus.e2 2).val * 65536 + (byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt bus.e2 4).val + (byteAt bus.e2 5).val * 256 + (byteAt bus.e2 6).val * 65536 + (byteAt bus.e2 7).val * 16777216
        = (v.a_2 r_a).val + (v.a_3 r_a).val * 65536)
    (h_rs1_value :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_op2_ne : div_input.r2_val.toInt ≠ 0)
    (_h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_r_abs :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  have h_chunk_ranges :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a chunk_ranges
  have h_carry_ranges :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_signed_carry_ranges_at_holds
      v r_a carry_ranges
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_div_chunked
      div_input.r1_val div_input.r2_val e2 v r_a
      h0 h1 h2 h3 h4 h5 h6 h7
      h_chain h_chunk_ranges h_carry_ranges
      h_sext h_m32 h_div h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
      h_byte_lo h_byte_hi h_rs1_value h_rs2_value
      h_op2_ne h_r_abs h_r_sign
  rw [equiv_DIV_sail state div_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_div_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-- Boundary-aware canonical equivalence for RV64 `DIV`.

    This variant keeps the nonzero-divisor path for `r2.toInt ≠ 0`, but handles
    the architecturally valid divisor-zero branch from the exposed ArithDiv
    boundary constraints instead of requiring a global `h_op2_ne` hypothesis. -/
lemma equiv_DIV_boundary_split
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (h_boundary : ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (chunk_ranges : ZiskFv.AirsClean.ArithDiv.ChunkRangeLookupWitness v r_a)
    (carry_ranges : ZiskFv.AirsClean.ArithDiv.SignedCarryRangeLookupWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
                * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
              ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
              ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0) (h_div : v.div r_a = 1)
    (h_byte_lo :
      (byteAt bus.e2 0).val + (byteAt bus.e2 1).val * 256 + (byteAt bus.e2 2).val * 65536 + (byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt bus.e2 4).val + (byteAt bus.e2 5).val * 256 + (byteAt bus.e2 6).val * 65536 + (byteAt bus.e2 7).val * 16777216
        = (v.a_2 r_a).val + (v.a_3 r_a).val * 65536)
    (h_rs1_value :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (_h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_r_abs_of_ne :
      div_input.r2_val.toInt ≠ 0 →
        ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
          - (v.nr r_a).val * (2:ℤ)^64).natAbs < div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  have h_chunk_ranges :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a chunk_ranges
  have h_carry_ranges :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_signed_carry_ranges_at_holds
      v r_a carry_ranges
  have h_rd_val :
      U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                  ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
        = (execute_DIV_REM_pure div_input.r1_val div_input.r2_val .DRS).1 := by
    by_cases h_r2_zero : div_input.r2_val.toInt = 0
    · exact
        ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_div_by_zero_chunked
          div_input.r1_val div_input.r2_val e2 v r_a
          h0 h1 h2 h3 h4 h5 h6 h7 h_chunk_ranges h_boundary h_m32 h_div
          h_nb_bool h_byte_lo h_byte_hi h_rs2_value h_r2_zero
    · exact
        ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_div_chunked
          div_input.r1_val div_input.r2_val e2 v r_a
          h0 h1 h2 h3 h4 h5 h6 h7
          h_chain h_chunk_ranges h_carry_ranges
          h_sext h_m32 h_div h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
          h_byte_lo h_byte_hi h_rs1_value h_rs2_value
          h_r2_zero (h_r_abs_of_ne h_r2_zero) h_r_sign
  rw [equiv_DIV_sail state div_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_div_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.EquivCore.Div
