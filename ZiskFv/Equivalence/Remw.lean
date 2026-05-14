import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Equivalence.Bridge.Arith
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Sail.remw
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.WriteValueProofs.MulDivRemSigned

/-!
End-to-end theorem for RV64M REMW (signed 32-bit remainder).

REMW is the W-variant sibling of REM. Both transpile through
`create_register_op` with `m32 = 1` for the 32-bit width. Sail-side,
both call `execute_REMW` with `is_unsigned = false`.

Phase 4 step4-remw: Structural-unpacking refactor replacing the single
`h_byte_sum_circuit` promise hypothesis with the explicit Tier-3
binders mirroring REMUW but specialized for signed-W (general
`na, nb, nr, np` sign witnesses with booleanity + XOR + remainder-sign
pin from `arith_table_op_div_rem_signed_w_d_sign_pin`).

Three theorems mirroring the REM pattern (shape-(a) — ALU/Arith bus):

* `equiv_REMW_circuit` — circuit-level (defined in terms of m.a/b lanes via
  `transpile_REMW`).
* `equiv_REMW_sail` — Sail-level wrapper for
  `execute_DIVREM_remw_pure_equiv`.
* `equiv_REMW` — canonical shape composing
  Sail + bus-effect via `bus_effect_matches_sail_alu_rrw`.

Plus V12 companion `equiv_REMW_from_bus`.
-/

namespace ZiskFv.Equivalence.Remw

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** Wraps `execute_DIVREM_remw_pure_equiv`. -/
lemma equiv_REMW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remw_input : PureSpec.RemwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remw_input.r2_val state)
    (h_input_rd : remw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
      = let remw_output := PureSpec.execute_DIVREM_remw_pure remw_input
        (do
          Sail.writeReg Register.nextPC remw_output.nextPC
          match remw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_remw_pure_equiv
    remw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    REMW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_remw_chunked`
    discharge lemma.

    Phase step4-remw structural-unpacking refactor with the standard
    Tier-3 binders: validator (`v`/`r_a`), W chain-holds, mode pins,
    op pin, sign-witness booleanity + XOR + signed-W remainder-sign
    pin, c_2=c_3=0 bus-W pin, byte-pack + sign-extension witnesses,
    operand toInt-form bridges, and non-boundary CIRCUIT-CONSTRAINTs
    (`h_op2_ne`, `h_no_overflow_w`, `h_r_abs`, `h_r_sign`). -/
theorem equiv_REMW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remw_input : PureSpec.RemwInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remw_input.r2_val state)
    (h_input_rd : remw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : remw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Structural-unpacking ADDED binders for REMW (W-mode signed).
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    -- Mode pins (TRANSPILE-PIN).
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 1)
    (h_div : v.div r_a = 1)
    -- Op-pin (TRANSPILE-PIN): REMW = 191, in {190, 191} signed-W family.
    (h_op : v.op r_a = 190 ∨ v.op r_a = 191)
    -- Sign-witness booleanity + XOR (CIRCUIT-CONSTRAINT).
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
                * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    -- Bus c-chunk W-pin (CIRCUIT-CONSTRAINT).
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    -- W-mode byte-pack lane match: bytes 0..3 pack d_0 + d_1*65536 (remainder low 32).
    (h_byte_lo :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7.
    (h_sext_choice :
      ((e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      ((e2.x4.val = 255 ∧ e2.x5.val = 255 ∧ e2.x6.val = 255 ∧ e2.x7.val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    -- Operand TRANSPILE-BRIDGE (W toInt-form).
    (h_op1 :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - (v.np r_a).val * (2:ℤ)^32)
    (h_op2 :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32)
    -- Non-boundary (CIRCUIT-CONSTRAINT).
    (h_op2_ne : Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow_w :
      ¬ (Sail.BitVec.extractLsb remw_input.r1_val 31 0 = (BitVec.ofNat 32 (2^31))
          ∧ Sail.BitVec.extractLsb remw_input.r2_val 31 0 = BitVec.allOnes 32))
    -- Magnitude bound + sign-correctness (CIRCUIT-CONSTRAINT).
    (h_r_abs :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - (v.nr r_a).val * (2:ℤ)^32).natAbs
        < (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - (v.nr r_a).val * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  -- Op-full for invoking the W operand pin (REMW ∈ {190, 191} ⊆ {188, 189, 190, 191}).
  have h_op_full : v.op r_a = 188 ∨ v.op r_a = 189
                    ∨ v.op r_a = 190 ∨ v.op r_a = 191 := by
    rcases h_op with h | h
    · right; right; left; exact h
    · right; right; right; exact h
  have h_rd_val :=
    ZiskFv.Equivalence.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_remw_chunked
      remw_input.r1_val remw_input.r2_val e2 v r_a
      h_e2_range.1 h_e2_range.2.1 h_e2_range.2.2.1 h_e2_range.2.2.2.1
      h_e2_range.2.2.2.2.1 h_e2_range.2.2.2.2.2.1
      h_e2_range.2.2.2.2.2.2.1 h_e2_range.2.2.2.2.2.2.2
      h_chain h_sext h_m32 h_div h_op h_op_full
      h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_c23 h_byte_lo h_sext_choice h_op1 h_op2
      h_op2_ne h_no_overflow_w h_r_abs h_r_sign
  rw [equiv_REMW_sail state remw_input r1 r2 rd
        h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_remw_pure, h_rd_idx]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp [h_rd_zero, bind, pure, EStateM.bind, EStateM.pure]
  · simp only [h_rd_zero, dite_false]
    rw [h_rd_val]

end ZiskFv.Equivalence.Remw
