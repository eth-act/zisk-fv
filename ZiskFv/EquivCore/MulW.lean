import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.Execution
import ZiskFv.ZiskCircuit.Mul
import ZiskFv.ZiskCircuit.MulW
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.SailSpec.mulw
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 MULW. MULW is the 32-bit word variant of
MUL — `m32 = 1` on both Main and Arith — which means the Main spec
must be authored with a MULW-specific mode predicate (the archetype
macro hardcodes `m32 = 0`). See `Circuit.MulW` for the compositional
statement.

The single `h_byte_mulw` promise hypothesis is replaced with the
explicit Tier-3 binders mirroring MULH but specialized for W-mode
(`m32 = 1`), adding `h_sext_choice` for the W sign-extension on
bytes 4..7 (same trust class as ADDW's `h_sext_choice` and
DIVUW/REMUW's W-mode sign extension).
-/

namespace ZiskFv.EquivCore.MulW

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Mul
open ZiskFv.ZiskCircuit.MulW
open ZiskFv.PackedBitVec.SignedChunkLift


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 MULW reduces to the pure-function block supplied by
    `PureSpec.execute_MULW_pure`, given source-register readability
    and PC knowledge. Wraps `PureSpec.execute_MULW_pure_equiv`. -/
lemma equiv_MULW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulw_input.r2_val state)
    (h_input_rd : mulw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = let mulw_output := PureSpec.execute_MULW_pure mulw_input
        (do
          Sail.writeReg Register.nextPC mulw_output.nextPC
          match mulw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_MULW_pure_equiv
    mulw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    MULW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`PureSpec.execute_MULW_pure_val ...`)
    directly; that equation is derived internally from circuit
    witnesses via the
    `WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_mulw_chunked`
    discharge lemma.

    structural-unpacking refactor with 17 ADDED binders (16 MUL
    base shape + `h_sext_choice` for W-mode sign-extension on bytes
    4..7). -/
theorem equiv_MULW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput)
    (r1 r2 rd : regidx)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulw_input.r1_val mulw_input.r2_val mulw_input.rd mulw_input.PC
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Structural-unpacking ADDED binders (17 total) mirroring MULH
    -- plus h_sext_choice for W-mode sign-extension on bytes 4..7.
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r_a)
    (h_nr : v.nr r_a = 0)
    (h_sext : v.sext r_a = 0) (h_m32 : v.m32 r_a = 1) (h_div : v.div r_a = 0)
    -- Op-pin for MULW: op = 182.
    (h_op : v.op r_a = 182)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    -- Byte-pack lane match (LANE-MATCH): bytes 0..3 pack c-chunks low 32 (MULW product low half).
    (h_byte_lo :
      bus.e2.x0.val + bus.e2.x1.val * 256 + bus.e2.x2.val * 65536 + bus.e2.x3.val * 16777216
        = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    -- Sign-extension choice on bytes 4..7 (SEXT_00 / SEXT_FF case-disjunction)
    (h_sext_choice :
      ((bus.e2.x4.val = 0 ∧ bus.e2.x5.val = 0 ∧ bus.e2.x6.val = 0 ∧ bus.e2.x7.val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      ((bus.e2.x4.val = 255 ∧ bus.e2.x5.val = 255 ∧ bus.e2.x6.val = 255 ∧ bus.e2.x7.val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    -- Operand TRANSPILE-BRIDGE (W form: low 32 bits, signed toInt).
    (h_rs1_value :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_mulw_chunked
      mulw_input.r1_val mulw_input.r2_val e2 v r_a
      h_e2_range.1 h_e2_range.2.1 h_e2_range.2.2.1 h_e2_range.2.2.2.1
      h_e2_range.2.2.2.2.1 h_e2_range.2.2.2.2.2.1
      h_e2_range.2.2.2.2.2.2.1 h_e2_range.2.2.2.2.2.2.2
      h_chain h_nr h_sext h_m32 h_div h_op
      h_na_bool h_nb_bool h_np_xor h_byte_lo h_sext_choice h_rs1_value h_rs2_value
  rw [equiv_MULW_sail state mulw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_MULW_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.EquivCore.MulW
