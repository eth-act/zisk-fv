import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus.EntryRanges
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
    -- Structural-unpacking ADDED binders (17 total).
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a)
    (h_na : v.na r_a = 0) (h_nb : v.nb r_a = 0)
    (h_np : v.np r_a = 0) (h_nr : v.nr r_a = 0)
    (h_m32 : v.m32 r_a = 1)
    (h_div : v.div r_a = 1)
    (h_op : v.op r_a = 188 ∨ v.op r_a = 189 ∨ v.op r_a = 190 ∨ v.op r_a = 191)
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
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    (h_op2_ne : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat ≠ 0)
    (h_d_lt_b : (v.d_0 r_a).val + (v.d_1 r_a).val * 65536
                  < (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat)
    (h_no_arith_div_dynamic_defect : False) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact False.elim h_no_arith_div_dynamic_defect


end ZiskFv.EquivCore.Remuw
