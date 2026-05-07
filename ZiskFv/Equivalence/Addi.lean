import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Addi
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.addi
import ZiskFv.Sail.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.RdValDerivation.Arith

/-!
End-to-end theorem for RV64 ADDI.

Mirrors `Equivalence.Sub` / `Equivalence.And` shape with
`rop.<OP> → iop.ADDI` on the Sail side and `OP_SUB/AND → OP_ADD`
on the circuit side. ADDI shares `OP_ADD` with ADD — the piggyback
is transpiler-internal; the Main-AIR row carries the sign-extended
12-bit immediate through `(b_lo, b_hi)` rather than from `xreg(rs2)`.

**Bus-shape note (inherited from SLLI precedent).** The equivalence
hypotheses still take three memory-bus entries `[e0, e1, e2]` even
though an ITYPE microinstruction reads only one register, to keep
the `bus_effect_matches_sail_alu_rrw` interface uniform for all
register-write ALU ops.
-/

namespace ZiskFv.Equivalence.Addi

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Addi
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.Airs.BinaryAdd

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `execute_instruction` on an RV64 ADDI
    reduces to `PureSpec.execute_ITYPE_addi_pure`. Wraps
    `PureSpec.execute_ITYPE_addi_pure_equiv`. -/
theorem equiv_ADDI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addi_input.r1_val state)
    (h_input_imm : addi_input.imm = imm)
    (h_input_rd : addi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addi_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = let addi_output := PureSpec.execute_ITYPE_addi_pure addi_input
        (do
          Sail.writeReg Register.nextPC addi_output.nextPC
          match addi_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_ITYPE_addi_pure_equiv
    addi_input r1 rd h_input_r1 h_input_imm h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    ADDI equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`r1_val + sext(imm)`) directly; that
    equation is derived internally from circuit witnesses via the
    `RdValDerivation.Arith.h_rd_val_arith_addi` discharge lemma. -/
theorem equiv_ADDI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Sail-state input bridges
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addi_input.r1_val state)
    (h_input_imm : addi_input.imm = imm)
    (h_input_rd : addi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addi_input.PC)
    -- Bus-protocol structural hypotheses
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addi_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Discharge parameters
    (h_circuit : ZiskFv.Circuit.Addi.addi_circuit_holds_with_binaryadd m b r_main r_binary)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_a_range : ZiskFv.Airs.BinaryAdd.a_chunks_in_range b r_binary)
    (h_b_range : ZiskFv.Airs.BinaryAdd.b_chunks_in_range b r_binary)
    (h_c_range : ZiskFv.Airs.BinaryAdd.c_chunks_in_range b r_binary)
    (h_input_r1_circuit : addi_input.r1_val
      = BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296))
    (h_input_imm_circuit : BitVec.signExtend 64 addi_input.imm
      = BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.Arith.h_rd_val_arith_addi
      m b r_main r_binary e2 addi_input.r1_val addi_input.imm
      h_circuit h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_a_range h_b_range h_c_range
      h_input_r1_circuit h_input_imm_circuit
  rw [equiv_ADDI_sail state addi_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_addi_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Addi
