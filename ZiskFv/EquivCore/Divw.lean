import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Airs.BusHypotheses
import ZiskFv.SailSpec.divw
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64M DIVW (signed 32-bit divide).

DIVW is the W-variant sibling of DIV. Both lower through
`create_register_op` with `m32 = 1` for the 32-bit width. Sail-side,
this calls `execute_DIVW` with `is_unsigned = false`.

Structural-unpacking refactor replacing the single
`h_byte_sum_circuit` promise hypothesis with the explicit Tier-3
binders mirroring DIV-signed but specialized for W-mode (`m32 = 1`,
`a_2=a_3=b_2=b_3=d_2=d_3=0` from `arith_table_op_divw_operand_pin`,
`c_2=c_3=0` from the bus W-encoding, and `h_sext_choice` for the
BV32→BV64 sign-extension on bytes 4..7).

Three theorems mirroring the DIV pattern (shape-(a) — ALU/Arith bus):

* `equiv_DIVW_sail` — Sail-level wrapper for
  `execute_DIVREM_divw_pure_equiv`.
* `equiv_DIVW` — canonical shape composing
  Sail + bus-effect via `bus_effect_matches_sail_alu_rrw`.
-/

namespace ZiskFv.EquivCore.Divw

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv


/-- **Sail-level companion.** Wraps `execute_DIVREM_divw_pure_equiv`. -/
lemma equiv_DIVW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divw_input : PureSpec.DivwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divw_input.r2_val state)
    (h_input_rd : divw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, false))) state
      = let divw_output := PureSpec.execute_DIVREM_divw_pure divw_input
        (do
          Sail.writeReg Register.nextPC divw_output.nextPC
          match divw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_divw_pure_equiv
    divw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    DIVW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_divw_chunked`
    discharge lemma.

    Structural-unpacking refactor with the explicit Tier-3 binders
    mirroring DIV-signed but specialized for W-mode (`m32 = 1`,
    operand pins `a_2 = a_3 = b_2 = b_3 = d_2 = d_3 = 0`, bus W-pin
    `c_2 = c_3 = 0`, and `h_sext_choice` for the BV32→BV64
    sign-extension on bytes 4..7).  No longer vacuous: the rd value is
    DERIVED via `WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_divw_chunked`. -/
lemma equiv_DIVW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divw_input : PureSpec.DivwInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    -- Structural-unpacking ADDED binders mirroring DIV-signed
    -- plus h_sext_choice for W-mode sign-extension + W operand pins.
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
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    -- W operand pins (TRANSPILE-PIN): the W operation truncates to low 32 bits.
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    -- Bus c-chunk W-pin (CIRCUIT-CONSTRAINT): dividend in W-mode is the
    -- sign-extended r1_lo32, but the c-chunk packing only consumes the
    -- low 32 bits; the np column carries the sign witness so c_2 = c_3 = 0.
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    -- W-mode byte-pack lane match: bytes 0..3 pack a_0 + a_1*65536 (low quotient).
    (h_byte_lo :
      (byteAt bus.e2 0).val + (byteAt bus.e2 1).val * 256 + (byteAt bus.e2 2).val * 65536 + (byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7.
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    -- Operand TRANSPILE-BRIDGE (W form: 32-bit toInt with sign witness extracted).
    (h_rs1_value : (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
              = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
                  - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value : (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
              = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
                  - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32)
    -- Non-boundary (CIRCUIT-CONSTRAINT — caller excludes div-by-zero / INT_MIN/-1).
    (h_op2_ne : Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb divw_input.r1_val 31 0 = BitVec.ofNat 32 (2^31)
          ∧ Sail.BitVec.extractLsb divw_input.r2_val 31 0 = BitVec.allOnes 32))
    -- Magnitude + sign-correctness (CIRCUIT-CONSTRAINT — strict bound recovered
    -- at the canonical layer from the WEAK bound + the narrowed |r| = |op2| defect).
    (h_r_abs :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          < (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, false))) state
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
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_divw_chunked
      divw_input.r1_val divw_input.r2_val e2 v r_a
      h0 h1 h2 h3 h4 h5 h6 h7
      h_chain h_chunk_ranges h_carry_ranges h_m32 h_div
      h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
      h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
      h_rs1_value h_rs2_value h_op2_ne h_no_overflow h_r_abs h_r_sign
  rw [equiv_DIVW_sail state divw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_divw_pure, h_rd_idx]
  rw [← h_rd_val]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · simp only [bind, pure, EStateM.bind, EStateM.pure]


/- Boundary-aware canonical equivalence for RV64 `DIVW`.

   This keeps the existing non-boundary path for nonzero low-32 divisors, but
   closes the architecturally valid divisor-zero branch from the exposed ArithDiv
   boundary constraints instead of requiring a global `h_op2_ne` hypothesis. -/
lemma equiv_DIVW_boundary_split
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divw_input : PureSpec.DivwInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
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
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (byteAt bus.e2 0).val + (byteAt bus.e2 1).val * 256 + (byteAt bus.e2 2).val * 65536 + (byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
              = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
                  - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value : (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
              = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
                  - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb divw_input.r1_val 31 0 = BitVec.ofNat 32 (2^31)
          ∧ Sail.BitVec.extractLsb divw_input.r2_val 31 0 = BitVec.allOnes 32))
    (h_r_abs_of_ne :
      Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32 →
        (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
            < (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, false))) state
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
        = (let r1_lo32 : BitVec 32 := Sail.BitVec.extractLsb divw_input.r1_val 31 0
           let r2_lo32 : BitVec 32 := Sail.BitVec.extractLsb divw_input.r2_val 31 0
           let q32 : BitVec 32 :=
             if r2_lo32 = 0#32
               then BitVec.allOnes 32
               else if r1_lo32 = (BitVec.ofNat 32 (2^31)) ∧ r2_lo32 = BitVec.allOnes 32
                 then BitVec.ofNat 32 (2^31)
                 else BitVec.ofInt 32 (Int.tdiv r1_lo32.toInt r2_lo32.toInt)
           BitVec.signExtend 64 q32) := by
    by_cases h_r2_zero : Sail.BitVec.extractLsb divw_input.r2_val 31 0 = 0#32
    · exact
        ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_divw_by_zero_chunked
          divw_input.r1_val divw_input.r2_val e2 v r_a
          h0 h1 h2 h3 h4 h5 h6 h7 h_chunk_ranges h_boundary h_m32 h_div
          h_nb_bool h_b23 h_byte_lo h_sext_choice h_rs2_value h_r2_zero
    · exact
        ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_divw_chunked
          divw_input.r1_val divw_input.r2_val e2 v r_a
          h0 h1 h2 h3 h4 h5 h6 h7
          h_chain h_chunk_ranges h_carry_ranges h_m32 h_div
          h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
          h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
          h_rs1_value h_rs2_value h_r2_zero h_no_overflow (h_r_abs_of_ne h_r2_zero) h_r_sign
  rw [equiv_DIVW_sail state divw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_divw_pure, h_rd_idx]
  rw [← h_rd_val]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · simp only [bind, pure, EStateM.bind, EStateM.pure]


end ZiskFv.EquivCore.Divw
