import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.Mul
import ZiskFv.ZiskCircuit.Divu
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.divu
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 **DIVU**. Differs from
`Equivalence.Div` only in the opcode literal (184 vs 186), the pure
spec (`execute_DIVREM_divu_pure` / `_equiv`), and the Sail instruction
payload (`instruction.DIV (r2, r1, rd, true)` — the boolean selector
picks unsigned).

Two canonical theorems:
* `equiv_DIVU_sail` — Sail-level, wraps
  `PureSpec.execute_DIVREM_divu_pure_equiv`.
* `equiv_DIVU` — canonical shape, discharged via shape-
  (a) `bus_effect_matches_sail_alu_rrw` (RRW).
-/

namespace ZiskFv.EquivCore.Divu

open Goldilocks
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Mul
open ZiskFv.ZiskCircuit.Divu
open ZiskFv.Tactics.ArithSMArchetype


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 DIVU reduces to the pure-function block supplied by
    `PureSpec.execute_DIVREM_divu_pure`. Wraps
    `PureSpec.execute_DIVREM_divu_pure_equiv`. -/
lemma equiv_DIVU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divu_input : PureSpec.DivuInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divu_input.r2_val state)
    (h_input_rd : divu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divu_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, true))) state
      = let divu_output := PureSpec.execute_DIVREM_divu_pure divu_input
        (do
          Sail.writeReg Register.nextPC divu_output.nextPC
          match divu_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_divu_pure_equiv
    divu_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    DIVU equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.MulDivRemUnsigned.h_rd_val_mdru_divu` discharge
    lemma. -/
theorem equiv_DIVU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divu_input : PureSpec.DivuInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divu_input.r1_val divu_input.r2_val divu_input.rd divu_input.PC
        (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    -- The 22 loose (cy, cy-range, hC) caller-burden binders are now
    -- replaced by the row-level carry-chain constraint set + unsigned
    -- mode pins, discharged via `Bridge.Arith.div_unsigned_chain_witnesses`.
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (chunk_ranges : ZiskFv.AirsClean.ArithDiv.ChunkRangeLookupWitness v r_a)
    (carry_ranges : ZiskFv.AirsClean.ArithDiv.UnsignedCarryRangeLookupWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_na : v.na r_a = 0) (h_nb : v.nb r_a = 0)
    (h_np : v.np r_a = 0) (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 0)
    (h_div : v.div r_a = 1)
    (h_byte_lo :
      (byteAt bus.e2 0).val + (byteAt bus.e2 1).val * 256 + (byteAt bus.e2 2).val * 65536 + (byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_byte_hi :
      (byteAt bus.e2 4).val + (byteAt bus.e2 5).val * 256 + (byteAt bus.e2 6).val * 65536 + (byteAt bus.e2 7).val * 16777216
        = (v.a_2 r_a).val + (v.a_3 r_a).val * 65536)
    (h_rs1_value : divu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.c_0 r_a).val (v.c_1 r_a).val
          (v.c_2 r_a).val (v.c_3 r_a).val)
    (h_rs2_value : divu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, true))) state
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
  have h_d_lt_b_arith :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_remainder_bound_unsigned
      remainder_bound
      (ZiskFv.EquivCore.Bridge.Arith.arith_div_chunk_ranges_at_holds v r_a chunk_ranges)
      h_nr h_nb
  have h_d_lt_b :
      ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.d_0 r_a).val (v.d_1 r_a).val
          (v.d_2 r_a).val (v.d_3 r_a).val
        < divu_input.r2_val.toNat := by
    simpa [h_rs2_value] using h_d_lt_b_arith
  have h_op2_ne : divu_input.r2_val.toNat ≠ 0 := by
    intro h_zero
    have : ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.d_0 r_a).val (v.d_1 r_a).val
          (v.d_2 r_a).val (v.d_3 r_a).val < 0 := by
      simpa [h_zero] using h_d_lt_b
    omega
  obtain ⟨cy₀, cy₁, cy₂, cy₃, cy₄, cy₅, cy₆,
          h_cy0, h_cy1, h_cy2, h_cy3, h_cy4, h_cy5, h_cy6,
          hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC38⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.div_unsigned_chain_witnesses_of_carry_ranges
      v r_a h_chain h_na h_nb h_np h_nr h_div h_carry_ranges
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned.h_rd_val_mdru_divu
      divu_input.r1_val divu_input.r2_val e2
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
      h_byte_lo h_byte_hi h_rs1_value h_rs2_value h_op2_ne h_d_lt_b
  rw [equiv_DIVU_sail state divu_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_divu_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.EquivCore.Divu
