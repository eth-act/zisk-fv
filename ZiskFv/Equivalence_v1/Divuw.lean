import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Equivalence_v1.Bridge.Arith
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.SailSpec.divuw
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence_v1.WriteValueProofs.MulDivRemUnsigned
import ZiskFv.Equivalence_v1.Promises.RType
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64M DIVUW (unsigned 32-bit divide).

DIVUW is the W-variant sibling of DIVU. Both transpile through
`create_register_op` with `m32 = 1` for the 32-bit width. Sail-side,
both call `execute_DIVW` with `is_unsigned = true`.

Structural-unpacking refactor replacing the single
`h_byte_sum_circuit` promise hypothesis with the explicit Tier-3
binders mirroring DIVU but specialized for W-mode (`m32 = 1`,
`a_2=a_3=b_2=b_3=d_2=d_3=0` from `arith_table_op_divw_operand_pin`).
The 17th ADDED binder `h_sext_choice` is the disjunctive sign-extension
witness over bytes 4..7 (SEXT_00 if quotient top bit clear, SEXT_FF
otherwise) — same trust class as ADDW's `h_sext_choice`.

Three theorems mirroring the DIVU pattern (shape-(a) — ALU/Arith bus):

* `equiv_DIVUW_sail` — Sail-level wrapper for
  `execute_DIVREM_divuw_pure_equiv`.
* `equiv_DIVUW` — canonical shape composing
  Sail + bus-effect via `bus_effect_matches_sail_alu_rrw`.

Plus bus-driven companion `equiv_DIVUW_from_bus`.
-/

namespace ZiskFv.Equivalence_v1.Divuw

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv


/-- **Sail-level companion.** Wraps `execute_DIVREM_divuw_pure_equiv`. -/
lemma equiv_DIVUW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divuw_input : PureSpec.DivuwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divuw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divuw_input.r2_val state)
    (h_input_rd : divuw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divuw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))) state
      = let divuw_output := PureSpec.execute_DIVREM_divuw_pure divuw_input
        (do
          Sail.writeReg Register.nextPC divuw_output.nextPC
          match divuw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_divuw_pure_equiv
    divuw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    DIVUW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.MulDivRemUnsigned.h_rd_val_mdru_divuw_chunked`
    discharge lemma.

    Structural-unpacking refactor with 17 ADDED binders (16 standard
    DIVU-shape + `h_sext_choice` for W-mode sign-extension on bytes
    4..7). -/
theorem equiv_DIVUW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divuw_input : PureSpec.DivuwInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence_v1.Promises.RTypePromises
        state divuw_input.r1_val divuw_input.r2_val divuw_input.rd divuw_input.PC
        (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Structural-unpacking ADDED binders (17 total) mirroring DIVU
    -- plus h_sext_choice for W-mode sign-extension.
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (h_na : v.na r_a = 0) (h_nb : v.nb r_a = 0)
    (h_np : v.np r_a = 0) (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 1)
    (h_div : v.div r_a = 1)
    -- Op-pin (TRANSPILE-PIN): DIVUW = op 188.
    (h_op : v.op r_a = 188 ∨ v.op r_a = 189 ∨ v.op r_a = 190 ∨ v.op r_a = 191)
    -- Bus c-chunk W-pin (CIRCUIT-CONSTRAINT): dividend in W-mode is the
    -- zero-extended r1_lo32, so c_2 = c_3 = 0 by bus encoding.
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    -- W-mode byte-pack lane match: bytes 0..3 pack a_0 + a_1*65536 (low quotient).
    (h_byte_lo :
      bus.e2.x0.val + bus.e2.x1.val * 256 + bus.e2.x2.val * 65536 + bus.e2.x3.val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7 (the 17th ADDED binder).
    (h_sext_choice :
      ((bus.e2.x4.val = 0 ∧ bus.e2.x5.val = 0 ∧ bus.e2.x6.val = 0 ∧ bus.e2.x7.val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      ((bus.e2.x4.val = 255 ∧ bus.e2.x5.val = 255 ∧ bus.e2.x6.val = 255 ∧ bus.e2.x7.val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    -- Operand TRANSPILE-BRIDGE (W form: low 32 bits).
    (h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    -- Divisor non-zero (CIRCUIT-CONSTRAINT).
    (h_op2_ne : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat ≠ 0)
    -- Remainder strictly less than divisor (CIRCUIT-CONSTRAINT).
    (h_d_lt_b : (v.d_0 r_a).val + (v.d_1 r_a).val * 65536
                  < (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- chunk-range bounds.
  obtain ⟨h_a0, h_a1, h_a2, h_a3,
          h_b0, h_b1, h_b2, h_b3,
          h_c0, h_c1, h_c2, h_c3,
          h_d0, h_d1, h_d2, h_d3⟩ :=
    ZiskFv.Equivalence_v1.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a
  -- W-unsigned chain witnesses.
  obtain ⟨cy₀, cy₁, cy₂, cy₃, cy₄, cy₅, cy₆,
          h_cy0, h_cy1, h_cy2, h_cy3, h_cy4, h_cy5, h_cy6,
          hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC38⟩ :=
    ZiskFv.Equivalence_v1.Bridge.Arith.div_w_unsigned_chain_witnesses v r_a h_chain
      h_na h_nb h_np h_nr h_sext h_m32 h_div
  -- W-mode operand chunk pin (a_2=a_3=b_2=b_3=d_2=d_3=0).
  obtain ⟨h_a2_eq, h_a3_eq, h_b2_eq, h_b3_eq, h_d2_eq, h_d3_eq⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_divw_operand_pin v r_a h_sext h_m32 h_div h_op
  -- byte-range bounds.
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  -- chunked rd-val discharge.
  have h_rd_val :=
    ZiskFv.Equivalence_v1.WriteValueProofs.MulDivRemUnsigned.h_rd_val_mdru_divuw_chunked
      divuw_input.r1_val divuw_input.r2_val e2
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
      h_rs1_value h_rs2_value h_op2_ne h_d_lt_b
  rw [equiv_DIVUW_sail state divuw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_divuw_pure, h_rd_idx]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp [h_rd_zero, bind, pure, EStateM.bind, EStateM.pure]
  · simp only [h_rd_zero, dite_false]
    rw [h_rd_val]

end ZiskFv.Equivalence_v1.Divuw
