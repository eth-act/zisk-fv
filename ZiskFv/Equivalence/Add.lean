import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Field.GoldilocksBridge
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.Add
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Equivalence.Bridge.BinaryAdd
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.add
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.WriteValueProofs.Arith
import ZiskFv.Equivalence.Promises.RType

/-!
End-to-end theorem for RV64 ADD. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_ADD`),
* the compositional ADD spec (`ZiskFv.ZiskCircuit.Add.add_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_RTYPE_add_pure_equiv`),

into two companion theorems:

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
open ZiskFv.ZiskCircuit.Add

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an RV64
    ADD (`.RTYPE (r2, r1, rd, rop.ADD)`) reduces to the pure function
    block supplied by `PureSpec.execute_RTYPE_add_pure`, given that the
    source registers are readable and the PC is known. Wraps
    `PureSpec.execute_RTYPE_add_pure_equiv` to expose the Sail chain at
    this module's export surface, consumed by `equiv_ADD` below. -/
lemma equiv_ADD_sail
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

/-- **Canonical equivalence.**
    Sail's `execute_instruction` on an RV64 ADD equals the state
    computed by applying `bus_effect` to the circuit's execution and
    memory bus rows.

    The cross-AIR matching (`matches_entry`), per-chunk byte ranges
    on BinaryAdd, and the per-chunk-form input bridges that pre-pilot
    `equiv_ADD` accepted as caller obligations are now derived inside
    the proof body via
    `ZiskFv.Equivalence.Bridge.BinaryAdd.add_discharge`, which
    consumes `op_bus_perm_sound_BinaryAdd` (PLONK soundness on
    `OPERATION_BUS_ID = 5000`) and `binary_add_columns_in_range`
    (range-check bus soundness on BinaryAdd's `bits(N)` columns) —
    both in the *trust ledger*.

    Net reduction in the *anti-laundering metric* vs. origin/main
    pre-discharge: −2 binders. (Further reductions possible by
    deriving `h_input_r{1,2}_main` from `transpile_ADD` + a state-
    bridge, or by universalizing `h_main_subset` / `h_main_mode`
    from `Valid_Main` constraints.) -/
theorem equiv_ADD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Structural promise bundle (15 fields, see Promises/RType.lean).
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd exec_row e0 e1 e2)
    (h_main_subset : add_subset_holds m r_main)
    (h_main_mode : main_row_in_add_mode m r_main)
    (h_b_core : ∀ r, ZiskFv.Airs.BinaryAdd.core_every_row b r)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨h_input_r1_sail, h_input_r2_sail, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- *Promise discharge* via the BinaryAdd bridge (with SailStateBridge
  -- deriving the input bridges from the Sail-form `read_xreg` facts
  -- that `equiv_ADD_sail` consumes).
  obtain ⟨r_binary, h_circuit, h_a_range, h_b_range, h_c_range,
          h_input_r1_circuit, h_input_r2_circuit⟩ :=
    ZiskFv.Equivalence.Bridge.BinaryAdd.add_discharge
      m b r_main h_main_subset h_main_mode h_b_core
      state (regidx_to_fin r1) (regidx_to_fin r2)
      add_input.r1_val add_input.r2_val
      h_input_r1_sail h_input_r2_sail
  have h_rd_val :=
    ZiskFv.Equivalence.WriteValueProofs.Arith.h_rd_val_arith_add
      m b r_main r_binary e2 add_input
      h_circuit h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_a_range h_b_range h_c_range
      h_input_r1_circuit h_input_r2_circuit
  rw [equiv_ADD_sail state add_input r1 r2 rd
        h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_add_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Add
