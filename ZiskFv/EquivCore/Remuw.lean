import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Airs.BusHypotheses
import ZiskFv.SailSpec.remuw
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64M REMUW (unsigned 32-bit divide).

REMUW is the W-variant sibling of REMU. Both transpile through
`create_register_op` with `m32 = 1` for the 32-bit width. Sail-side,
both call `execute_REMW` with `is_unsigned = true`.

Structural-unpacking refactor (see Divuw.lean for rationale). 17
ADDED binders including the `h_sext_choice` for W-mode sign-extension
over bytes 4..7. The bytes 0..3 pack the remainder lanes
`d_0 + d_1*65536` (not the quotient).

Three canonical theorems mirroring the REMU pattern (shape-(a)).
-/

namespace ZiskFv.EquivCore.Remuw

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv

set_option maxHeartbeats 800000


/-- **Sail-level companion.** Wraps `execute_DIVREM_remuw_pure_equiv`. -/
lemma equiv_REMUW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remuw_input : PureSpec.RemuwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remuw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remuw_input.r2_val state)
    (h_input_rd : remuw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remuw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) state
      = let remuw_output := PureSpec.execute_DIVREM_remuw_pure remuw_input
        (do
          Sail.writeReg Register.nextPC remuw_output.nextPC
          match remuw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_remuw_pure_equiv
    remuw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    REMUW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Structural-unpacking refactor with 17 ADDED binders. -/
theorem equiv_REMUW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remuw_input : PureSpec.RemuwInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remuw_input.r1_val remuw_input.r2_val remuw_input.rd remuw_input.PC
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    -- Structural-unpacking ADDED binders (17 total).
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (chunk_ranges : ZiskFv.AirsClean.ArithDiv.ChunkRangeLookupWitness v r_a)
    (carry_ranges : ZiskFv.AirsClean.ArithDiv.UnsignedCarryRangeLookupWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_na : v.na r_a = 0) (h_nb : v.nb r_a = 0)
    (h_np : v.np r_a = 0) (h_nr : v.nr r_a = 0)
    (h_m32 : v.m32 r_a = 1)
    (h_div : v.div r_a = 1)
    (h_op : v.op r_a = 188 ∨ v.op r_a = 189 ∨ v.op r_a = 190 ∨ v.op r_a = 191)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    -- W-mode byte-pack lane match: bytes 0..3 pack d_0 + d_1*65536 (remainder low).
    (h_byte_lo :
      (byteAt bus.e2 0).val + (byteAt bus.e2 1).val * 256 + (byteAt bus.e2 2).val * 65536 + (byteAt bus.e2 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7 (the 17th ADDED binder).
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a chunk_ranges
  have h_carry_ranges :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_unsigned_carry_ranges_at_holds
      v r_a carry_ranges
  obtain ⟨h_d23, h_d_lt_b_arith⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_remainder_bound_unsigned_w
      remainder_bound
      (ZiskFv.EquivCore.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a chunk_ranges)
      h_nr h_nb h_b23
  have h_d_lt_b :
      (v.d_0 r_a).val + (v.d_1 r_a).val * 65536
        < (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat := by
    rw [h_rs2_value]
    exact h_d_lt_b_arith
  have h_op2_ne : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat ≠ 0 := by
    intro h_zero
    have hlt := h_d_lt_b
    rw [h_zero] at hlt
    omega
  obtain ⟨cy₀, cy₁, cy₂, cy₃, cy₄, cy₅, cy₆,
          h_cy0, h_cy1, h_cy2, h_cy3, h_cy4, h_cy5, h_cy6,
          hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC38⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.div_unsigned_chain_witnesses_of_carry_ranges
      v r_a h_chain h_na h_nb h_np h_nr h_div h_carry_ranges
  have h_packed_nat : ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val
        * ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val
        + ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.d_0 r_a).val (v.d_1 r_a).val
          (v.d_2 r_a).val (v.d_3 r_a).val
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.c_0 r_a).val (v.c_1 r_a).val
          (v.c_2 r_a).val (v.c_3 r_a).val :=
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned.fgl_div_unsigned_chunks_to_nat_identity
      (v.a_0 r_a) (v.a_1 r_a) (v.a_2 r_a) (v.a_3 r_a)
      (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a)
      (v.c_0 r_a) (v.c_1 r_a) (v.c_2 r_a) (v.c_3 r_a)
      (v.d_0 r_a) (v.d_1 r_a) (v.d_2 r_a) (v.d_3 r_a)
      cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
      h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
      h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
      h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
  have h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0 := by
    obtain ⟨hb2, hb3⟩ := h_b23
    obtain ⟨hc2, hc3⟩ := h_c23
    obtain ⟨hd2, hd3⟩ := h_d23
    have h_c32_lt : (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 4294967296 := by
      have : (v.c_1 r_a).val * 65536 ≤ 65535 * 65536 :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have h_b32_pos : 0 < (v.b_0 r_a).val + (v.b_1 r_a).val * 65536 := by
      have h_ne : (v.b_0 r_a).val + (v.b_1 r_a).val * 65536 ≠ 0 := by
        intro h_zero
        apply h_op2_ne
        rw [h_rs2_value, h_zero]
      omega
    have h_a_packed_lt :
        ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val < 4294967296 := by
      unfold ZiskFv.PackedBitVec.MulNoWrap.packed4 at h_packed_nat
      rw [hb2, hb3, hc2, hc3, hd2, hd3] at h_packed_nat
      nlinarith
    unfold ZiskFv.PackedBitVec.MulNoWrap.packed4 at h_a_packed_lt
    constructor <;> omega
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned.h_rd_val_mdru_remuw_chunked
      remuw_input.r1_val remuw_input.r2_val e2
      (v.a_0 r_a) (v.a_1 r_a) (v.a_2 r_a) (v.a_3 r_a)
      (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a)
      (v.c_0 r_a) (v.c_1 r_a) (v.c_2 r_a) (v.c_3 r_a)
      (v.d_0 r_a) (v.d_1 r_a) (v.d_2 r_a) (v.d_3 r_a)
      cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
      h0 h1 h2 h3 h4 h5 h6 h7
      h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
      h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
      h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
      h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
      h_rs1_value h_rs2_value h_op2_ne h_d_lt_b
  rw [equiv_REMUW_sail state remuw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_remuw_pure, h_rd_idx]
  rw [← h_rd_val]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · simp only [bind, pure, EStateM.bind, EStateM.pure]


end ZiskFv.EquivCore.Remuw
