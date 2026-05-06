import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Circuit.Mul
import ZiskFv.Circuit.MulW
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.mulw
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned

/-!
End-to-end theorem for RV64 MULW. MULW is the 32-bit word variant of
MUL — `m32 = 1` on both Main and Arith — which means the Main spec
must be authored with a MULW-specific mode predicate (the archetype
macro hardcodes `m32 = 0`). See `Circuit.MulW` for the compositional
statement.
-/

namespace ZiskFv.Equivalence.MulW

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Mul
open ZiskFv.Circuit.MulW

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level MULW theorem.** Main's packed `c` equals Arith's
    packed result lanes, given the MULW circuit-holds hypothesis.
    Wraps `Circuit.MulW.mulw_compositional`. -/
theorem equiv_MULW_circuit
    (_rs1 _rs2 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h_circuit : mulw_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_c_packed v r_arith :=
  mulw_compositional m v r_main r_arith h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 MULW reduces to the pure-function block supplied by
    `PureSpec.execute_MULW_pure`, given source-register readability
    and PC knowledge. Wraps `PureSpec.execute_MULW_pure_equiv`. -/
theorem equiv_MULW_sail
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
    `RdValDerivation.MulDivRemUnsigned.h_rd_val_mdru_mulw` discharge
    lemma. -/
theorem equiv_MULW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulw_input.r2_val state)
    (h_input_rd : mulw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULW_pure mulw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : mulw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Discharge parameters
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_byte_mulw :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
        + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (PureSpec.execute_MULW_pure_val mulw_input.r1_val mulw_input.r2_val).toNat) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned.h_rd_val_mdru_mulw
      mulw_input.r1_val mulw_input.r2_val e2
      h0 h1 h2 h3 h4 h5 h6 h7 h_byte_mulw
  rw [equiv_MULW_sail state mulw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_MULW_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]


/-- **Bus-precondition companion.** Drops `h_input_r1` / `h_input_r2` /
    `h_input_pc` / `h_input_rd` in favor of a single `h_bus :
    (bus_effect ...).1` plus ptr/value match hypotheses.
    Delegates to `equiv_MULW` after chip_bus_hyps + match composition. -/
theorem equiv_MULW_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULW_pure mulw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r1_val : mulw_input.r1_val
      = U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                    e0.x4, e0.x5, e0.x6, e0.x7])
    (h_r2_ptr : regidx_to_fin r2 = Transpiler.wrap_to_regidx e1.ptr)
    (h_r2_val : mulw_input.r2_val
      = U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                    e1.x4, e1.x5, e1.x6, e1.x7])
    (h_pc : mulw_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_idx : mulw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Discharge parameters (replacing h_rd_val).
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_byte_mulw :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
        + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (PureSpec.execute_MULW_pure_val mulw_input.r1_val mulw_input.r2_val).toNat) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = (bus_effect exec_row [e0, e1, e2] state).2
    := by
  obtain ⟨h_pc_read, h_rs1_read, h_rs2_read⟩ :=
    ZiskFv.Airs.BusHypotheses.chip_bus_hyps_alu_rrw
      state exec_row e0 e1 e2
      h_exec_len h_e0_mult h_e1_mult
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
      h_bus
  have h_input_r1 :
      read_xreg (regidx_to_fin r1) state
        = EStateM.Result.ok mulw_input.r1_val state := by
    rw [h_r1_ptr, h_r1_val]; exact h_rs1_read
  have h_input_r2 :
      read_xreg (regidx_to_fin r2) state
        = EStateM.Result.ok mulw_input.r2_val state := by
    rw [h_r2_ptr, h_r2_val]; exact h_rs2_read
  have h_input_rd : mulw_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some mulw_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_MULW state mulw_input r1 r2 rd exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_rd_idx
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_mulw


/-- Constructor: build a `PureSpec.MulwInput` from bus entries. -/
def MulwInput_of_bus
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL)) :
    PureSpec.MulwInput :=
  { r1_val := U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                          e0.x4, e0.x5, e0.x6, e0.x7]
    r2_val := U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                          e1.x4, e1.x5, e1.x6, e1.x7]
    rd := Transpiler.wrap_to_regidx e2.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- Bus-derived input form, eliminating value-level match hyps via `MulwInput_of_bus`. -/
theorem equiv_MULW_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULW_pure (MulwInput_of_bus e0 e1 e2 exec_row)).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r2_ptr : regidx_to_fin r2 = Transpiler.wrap_to_regidx e1.ptr)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Discharge parameters (replacing h_rd_val).
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_byte_mulw :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
        + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (PureSpec.execute_MULW_pure_val
          (MulwInput_of_bus e0 e1 e2 exec_row).r1_val
          (MulwInput_of_bus e0 e1 e2 exec_row).r2_val).toNat) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = (bus_effect exec_row [e0, e1, e2] state).2

    := by
  exact equiv_MULW_from_bus state
    (MulwInput_of_bus e0 e1 e2 exec_row) r1 r2 rd
    exec_row e0 e1 e2
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_bus h_r1_ptr rfl h_r2_ptr rfl rfl h_rd_ptr
    rfl
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_mulw

/-- **Op-bus companion to `equiv_MULW`.** Drops `h_input_r1` /
    `h_input_r2` in favour of an op-bus precondition. Mirrors
    `equiv_ADD_op_bus`. -/
theorem equiv_MULW_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (op_entry : OperationBusEntry FGL)
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin r1) (regidx_to_fin r2)).1)
    (h_a_match :
      mulw_input.r1_val = Goldilocks.lanes_to_bv64 op_entry.a_lo op_entry.a_hi)
    (h_b_match :
      mulw_input.r2_val = Goldilocks.lanes_to_bv64 op_entry.b_lo op_entry.b_hi)
    (h_input_rd : mulw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULW_pure mulw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : mulw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Discharge parameters (replacing h_rd_val).
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_byte_mulw :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
        + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (PureSpec.execute_MULW_pure_val mulw_input.r1_val mulw_input.r2_val).toNat) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨h_r1_read, h_r2_read⟩ :=
    ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_alu
      state op_entry (regidx_to_fin r1) (regidx_to_fin r2) h_op_mult h_op_bus
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulw_input.r1_val state := by
    rw [h_a_match]; exact h_r1_read
  have h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulw_input.r2_val state := by
    rw [h_b_match]; exact h_r2_read
  exact equiv_MULW state mulw_input r1 r2 rd exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_rd_idx
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_mulw

end ZiskFv.Equivalence.MulW
