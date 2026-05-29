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

DIVW is the W-variant sibling of DIV. Both transpile through
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

    Structural-unpacking refactor with 18 ADDED binders (DIV
    signed-shape 16 + `h_sext_choice` for W-mode sign-extension +
    `h_c23` for bus W-encoding). -/
theorem equiv_DIVW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divw_input : PureSpec.DivwInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Structural-unpacking ADDED binders (18 total) mirroring DIV-signed
    -- plus h_sext_choice for W-mode sign-extension + h_c23 for bus W-pin.
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
                * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
    -- Op-pin (TRANSPILE-PIN): DIVW is in {188, 189, 190, 191}
    -- (W-DIV family). For the signed sign-pin axiom (op ∈ {190, 191}).
    (h_op : v.op r_a = 188 ∨ v.op r_a = 189 ∨ v.op r_a = 190 ∨ v.op r_a = 191)
    (h_op_signed : v.op r_a = 190 ∨ v.op r_a = 191)
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
    -- Magnitude + sign-correctness (CIRCUIT-CONSTRAINT).
    (h_r_abs :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          < (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt)
    (h_no_arith_div_dynamic_defect : False) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, false))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact False.elim h_no_arith_div_dynamic_defect


end ZiskFv.EquivCore.Divw
