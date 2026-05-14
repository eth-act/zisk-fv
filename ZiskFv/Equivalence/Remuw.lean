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
import ZiskFv.Sail.remuw
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.WriteValueProofs.MulDivRemUnsigned

/-!
End-to-end theorem for RV64M REMUW (unsigned 32-bit divide).

REMUW is the W-variant sibling of REMU. Both transpile through
`create_register_op` with `m32 = 1` for the 32-bit width. Sail-side,
both call `execute_REMW` with `is_unsigned = true`.

Phase 4.alpha.B.uw2: Structural-unpacking refactor (see Divuw.lean for
rationale). 17 ADDED binders including the new `h_sext_choice` for
W-mode sign-extension over bytes 4..7. The bytes 0..3 pack the
remainder lanes `d_0 + d_1*65536` (not the quotient).

Three canonical theorems mirroring the REMU pattern (shape-(a)).
-/

namespace ZiskFv.Equivalence.Remuw

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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

    Phase 4.alpha.B.uw2 structural-unpacking refactor with 17 ADDED
    binders. -/
theorem equiv_REMUW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remuw_input : PureSpec.RemuwInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remuw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remuw_input.r2_val state)
    (h_input_rd : remuw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remuw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : remuw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Structural-unpacking ADDED binders (17 total).
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (h_na : v.na r_a = 0) (h_nb : v.nb r_a = 0)
    (h_np : v.np r_a = 0) (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 1)
    (h_div : v.div r_a = 1)
    (h_op : v.op r_a = 188 ∨ v.op r_a = 189 ∨ v.op r_a = 190 ∨ v.op r_a = 191)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    -- W-mode byte-pack lane match: bytes 0..3 pack d_0 + d_1*65536 (remainder low).
    (h_byte_lo :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7 (the 17th ADDED binder).
    (h_sext_choice :
      ((e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      ((e2.x4.val = 255 ∧ e2.x5.val = 255 ∧ e2.x6.val = 255 ∧ e2.x7.val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_op1 : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_op2 : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    (h_op2_ne : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat ≠ 0)
    (h_d_lt_b : (v.d_0 r_a).val + (v.d_1 r_a).val * 65536
                  < (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.Equivalence.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a
  obtain ⟨cy₀, cy₁, cy₂, cy₃, cy₄, cy₅, cy₆,
          h_cy0, h_cy1, h_cy2, h_cy3, h_cy4, h_cy5, h_cy6,
          hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC38⟩ :=
    ZiskFv.Equivalence.Bridge.Arith.div_w_unsigned_chain_witnesses v r_a h_chain
      h_na h_nb h_np h_nr h_sext h_m32 h_div
  obtain ⟨h_a2_eq, h_a3_eq, h_b2_eq, h_b3_eq, h_d2_eq, h_d3_eq⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_divw_operand_pin v r_a h_sext h_m32 h_div h_op
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  have h_rd_val :=
    ZiskFv.Equivalence.WriteValueProofs.MulDivRemUnsigned.h_rd_val_mdru_remuw_chunked
      remuw_input.r1_val remuw_input.r2_val e2
      (v.a_0 r_a) (v.a_1 r_a) (v.a_2 r_a) (v.a_3 r_a)
      (v.b_0 r_a) (v.b_1 r_a) (v.b_2 r_a) (v.b_3 r_a)
      (v.c_0 r_a) (v.c_1 r_a) (v.c_2 r_a) (v.c_3 r_a)
      (v.d_0 r_a) (v.d_1 r_a) (v.d_2 r_a) (v.d_3 r_a)
      cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
      h_e2_range.1 h_e2_range.2.1 h_e2_range.2.2.1 h_e2_range.2.2.2.1
      h_e2_range.2.2.2.2.1 h_e2_range.2.2.2.2.2.1
      h_e2_range.2.2.2.2.2.2.1 h_e2_range.2.2.2.2.2.2.2
      h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
      h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
      h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
      ⟨h_a2_eq, h_a3_eq⟩ ⟨h_b2_eq, h_b3_eq⟩ ⟨h_d2_eq, h_d3_eq⟩ h_c23
      h_byte_lo h_sext_choice
      h_op1 h_op2 h_op2_ne h_d_lt_b
  rw [equiv_REMUW_sail state remuw_input r1 r2 rd
        h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_remuw_pure, h_rd_idx]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp [h_rd_zero, bind, pure, EStateM.bind, EStateM.pure]
  · simp only [h_rd_zero, dite_false]
    rw [h_rd_val]

end ZiskFv.Equivalence.Remuw
