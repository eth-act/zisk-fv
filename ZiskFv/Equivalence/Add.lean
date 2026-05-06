import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.GoldilocksBridge
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Add
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.add
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.RdValDerivation.Arith

/-!
End-to-end theorem for RV64 ADD. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_ADD`),
* the compositional ADD spec (`ZiskFv.Circuit.Add.add_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_RTYPE_add_pure_equiv`),

into two companion theorems:

* `equiv_ADD_circuit` — circuit-level. States the Goldilocks `c`-packed value
  equals the field sum of source-register lanes (mod carry-out).
* `equiv_ADD_sail` — Sail-level. States `LeanRV64D.execute_instruction`
  on an RV64 ADD reduces to a concrete monadic block writing
  `r1_val + r2_val` (BitVec 64, wraps mod 2^64) to `rd` and
  advancing `nextPC`. Discharged via `execute_RTYPE_add_pure_equiv`.
-/

namespace ZiskFv.Equivalence.Add

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Add

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an RV64
    ADD (`.RTYPE (r2, r1, rd, rop.ADD)`) reduces to the pure function
    block supplied by `PureSpec.execute_RTYPE_add_pure`, given that the
    source registers are readable and the PC is known. Wraps
    `PureSpec.execute_RTYPE_add_pure_equiv` to expose the Sail chain at
    this module's export surface — pairs with `equiv_ADD_circuit` above to
    connect circuit constraints to Sail semantics. -/
theorem equiv_ADD_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok add_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok add_input.r2_val state)
    (h_input_rd : add_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some add_input.PC) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = let add_output := PureSpec.execute_RTYPE_add_pure add_input
        (do
          Sail.writeReg Register.nextPC add_output.nextPC
          match add_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_add_pure_equiv
    add_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    ADD equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`r1_val + r2_val`) directly; that
    equation is derived internally from circuit witnesses via the
    `RdValDerivation.Arith.h_rd_val_arith_add` discharge lemma. -/
theorem equiv_ADD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Sail-state Sail-input bridges (TRANSPILE-BRIDGE class)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok add_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok add_input.r2_val state)
    (h_input_rd : add_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some add_input.PC)
    -- Bus-protocol structural hypotheses (CIRCUIT-CONSTRAINT class)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_add_pure add_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : add_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Discharge parameters
    (h_circuit : add_circuit_holds m b r_main r_binary)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_a_range : a_chunks_in_range b r_binary)
    (h_b_range : b_chunks_in_range b r_binary)
    (h_c_range : c_chunks_in_range b r_binary)
    (h_input_r1_circuit : add_input.r1_val
      = BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296))
    (h_input_r2_circuit : add_input.r2_val
      = BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296)) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.Arith.h_rd_val_arith_add
      m b r_main r_binary e2 add_input
      h_circuit h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_a_range h_b_range h_c_range
      h_input_r1_circuit h_input_r2_circuit
  rw [equiv_ADD_sail state add_input r1 r2 rd
        h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_add_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Add
