import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Circuit.Srli
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.srli
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.Equivalence.RdValDerivation.BinaryShift
import ZiskFv.Equivalence.RdValDerivation.SailBridge

/-!
End-to-end theorem for RV64 SRLI (immediate sibling of SRL).

Mirrors `Equivalence.Slli` structurally, swapping `sop.SLLI` for
`sop.SRLI`.
-/

namespace ZiskFv.Equivalence.Srli

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Srli

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** -/
theorem equiv_SRLI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srli_input : PureSpec.SrliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srli_input.r1_val state)
    (h_input_shamt : srli_input.shamt = shamt)
    (h_input_rd : srli_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srli_input.PC) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) state
      = let srli_output := PureSpec.execute_SHIFTIOP_srli_pure srli_input
        (do
          Sail.writeReg Register.nextPC srli_output.nextPC
          match srli_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_SHIFTIOP_srli_pure_equiv
    srli_input r1 rd shamt h_input_r1 h_input_shamt h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    SRLI equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `RdValDerivation.BinaryShift.h_rd_val_shift_srli` discharge lemma. -/
theorem equiv_SRLI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srli_input : PureSpec.SrliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main C FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srli_input.r1_val state)
    (h_input_shamt : srli_input.shamt = shamt)
    (h_input_rd : srli_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srli_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : srli_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_op : (v.op r_binary).val = ZiskFv.Airs.BinaryExtensionTable.OP_SRL)
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1_circuit : srli_input.r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936))
    (h_shift_pin : srli_input.shamt.toNat = (v.free_in_b r_binary).val % 64) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- Derive the 8 a-byte ranges + 16 c-byte 32-bit ranges from
  -- `binary_extension_columns_in_range` (BinaryExtension AIR's
  -- range-check soundness axiom on the trust ledger). This discharges
  -- the 17 per-byte *promise hypotheses* without any caller obligation.
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, _hb,
          hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
          hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, _, _⟩ :=
    ZiskFv.Airs.BinaryExtension.binary_extension_columns_in_range v r_binary
  have h_a_range : ZiskFv.Airs.BinaryExtension.a_bytes_in_range v r_binary :=
    ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩
  set shift : ℕ := srli_input.shamt.toNat with h_shift_def
  have h_discharge :=
    ZiskFv.Equivalence.RdValDerivation.BinaryShift.h_rd_val_shift_srli
      m v r_main r_binary e2 srli_input.r1_val shift h_op h_bytes h_a_range
      hc0 hc2 hc4 hc6 hc8 hc10 hc12 hc14
      hc1 hc3 hc5 hc7 hc9 hc11 hc13 hc15
      hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit
      (by rw [h_shift_def]; exact h_shift_pin)
  have h_bridge :=
    ZiskFv.Equivalence.RdValDerivation.SailBridge.sail_srli_bridge
      srli_input.r1_val srli_input.shamt shift h_shift_def
  have h_rd_val : U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                              e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_SHIFTIOP_pure srli_input.r1_val srli_input.shamt sop.SRLI := by
    rw [h_discharge, h_bridge]
  rw [equiv_SRLI_sail state srli_input r1 rd shamt
        h_input_r1 h_input_shamt h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_SHIFTIOP_srli_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Srli
