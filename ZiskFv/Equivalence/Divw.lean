import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Equivalence.Bridge.Arith
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Sail.divw
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.WriteValueProofs.MulDivRemSigned

/-!
End-to-end theorem for RV64M DIVW (signed 32-bit divide).

DIVW is the W-variant sibling of DIV. Both transpile through
`create_register_op` with `m32 = 1` for the 32-bit width. Sail-side,
this calls `execute_DIVW` with `is_unsigned = false`.

Phase 4.step4.divw: Structural-unpacking refactor replacing the single
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

namespace ZiskFv.Equivalence.Divw

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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

    Phase 4.step4 structural-unpacking refactor with 18 ADDED
    binders (Phase A DIV signed-shape 16 + `h_sext_choice` for W-mode
    sign-extension + `h_c23` for bus W-encoding). -/
theorem equiv_DIVW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divw_input : PureSpec.DivwInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divw_input.r2_val state)
    (h_input_rd : divw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : divw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
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
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 1)
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
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7.
    (h_sext_choice :
      ((e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      ((e2.x4.val = 255 ∧ e2.x5.val = 255 ∧ e2.x6.val = 255 ∧ e2.x7.val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    -- Operand TRANSPILE-BRIDGE (W form: 32-bit toInt with sign witness extracted).
    (h_op1 : (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
              = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
                  - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_op2 : (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
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
          * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- Step 1: byte-range bounds.
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  -- Step 2: W-mode operand chunk pin (a_2=a_3=b_2=b_3=d_2=d_3=0).
  have h_w_pin :=
    ZiskFv.Airs.Arith.arith_table_op_divw_operand_pin v r_a h_sext h_m32 h_div h_op
  obtain ⟨h_a2_eq, h_a3_eq, h_b2_eq, h_b3_eq, h_d2_eq, h_d3_eq⟩ := h_w_pin
  -- Step 3: signed-W sign-of-D pin.
  have h_nr_pin_fgl :=
    ZiskFv.Airs.Arith.arith_table_op_div_rem_signed_w_d_sign_pin
      v r_a h_sext h_m32 h_div h_op_signed
  -- Step 4: convert h_nr_pin_fgl to the toIntZ form used by the discharge.
  have h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0) := by
    rcases h_nr_pin_fgl with h_eq | ⟨hd0, hd1, _hd2, _hd3⟩
    · left; rw [h_eq]
    · right; exact ⟨hd0, hd1⟩
  -- Step 5: chunked rd-val discharge.
  have h_rd_val :=
    ZiskFv.Equivalence.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_divw_chunked
      divw_input.r1_val divw_input.r2_val e2 v r_a
      h_e2_range.1 h_e2_range.2.1 h_e2_range.2.2.1 h_e2_range.2.2.2.1
      h_e2_range.2.2.2.2.1 h_e2_range.2.2.2.2.2.1
      h_e2_range.2.2.2.2.2.2.1 h_e2_range.2.2.2.2.2.2.2
      h_chain h_sext h_m32 h_div h_na_bool h_nb_bool h_nr_bool h_np_xor
      ⟨h_a2_eq, h_a3_eq⟩ ⟨h_b2_eq, h_b3_eq⟩ ⟨h_d2_eq, h_d3_eq⟩ h_c23
      h_nr_pin h_byte_lo h_sext_choice h_op1 h_op2 h_op2_ne h_no_overflow
      h_r_abs h_r_sign
  rw [equiv_DIVW_sail state divw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_divw_pure, h_rd_idx]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp [h_rd_zero, bind, pure, EStateM.bind, EStateM.pure]
  · simp only [h_rd_zero, dite_false]
    rw [h_rd_val]

end ZiskFv.Equivalence.Divw
