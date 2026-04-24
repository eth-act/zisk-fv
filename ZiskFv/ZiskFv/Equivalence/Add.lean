import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.GoldilocksBridge
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Add
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.add
import ZiskFv.RV64D.BusEffect
import ZiskFv.Airs.BusHypotheses

/-!
End-to-end theorem for RV64 ADD. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_ADD`),
* the compositional ADD spec (`ZiskFv.Spec.Add.add_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_RTYPE_add_pure_equiv`, now buildable thanks to
  Phase 1.5 `Fundamentals/Execution.lean`),

into two companion theorems:

* `equiv_ADD` — circuit-level. States the Goldilocks `c`-packed value
  equals the field sum of source-register lanes (mod carry-out). This
  is the compositional proof that was the centrepiece of Phase 1.
* `equiv_ADD_sail` — Sail-level. States `LeanRV64D.execute_instruction`
  on an RV64 ADD reduces to a concrete monadic block writing
  `r1_val + r2_val` (BitVec 64, wraps mod 2^64) to `rd` and
  advancing `nextPC`. Discharged via `execute_RTYPE_add_pure_equiv`.

**Remaining gap to the full metaplan statement.** The metaplan target
shape is

```
execute_instruction (.RTYPE rs2 rs1 rd rop.ADD) state = (bus_effect exec_row mem_row state).2
```

with `bus_effect` defined in `ZiskFv.RV64D.BusEffect`. The final chain
requires: (1) promoting `BusEffect.lean` from its RV32-shaped 4-byte
memory-bus entries to 8-byte entries (documented TODO in that file),
and (2) a bridging lemma that identifies the Goldilocks-field `c_packed`
with the BitVec 64 sum `r1_val + r2_val` Sail produces. Both are
deferred to Phase 2 as documented in `ai_plans/zisk-fv-phase-1.md`
under "Phase 1.5 status".
-/

namespace ZiskFv.Equivalence.Add

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Add

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Phase 1 equiv_ADD.** For an RV64 ADD instruction `rd, rs1, rs2`
    executed on `state`, *if* the Main/BinaryAdd rows produced by the
    ZisK execution satisfy the ADD-subset constraints and match on the
    operation bus, *then* the Goldilocks-packed `c` lanes encode
    `xreg(rs1) + xreg(rs2)` modulo `2^64` (the carry-out absorbs the
    overflow into the field).

    The first hypothesis is `transpile_ADD`; the second is the
    circuit-side compositional spec; the conclusion is a single field
    equation tying the row's `c` to the source-register sum.

    Coefficient `4294967296 * 4294967296 = 2^64` written in factored form
    so `ring` can match it against the carry-chain coefficient. -/
theorem equiv_ADD
    (rs1 rs2 : Fin 32) (state : RV64State)
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (h_circuit : add_circuit_holds m b r_main r_binary) :
    main_c_packed m r_main
      = (lane_lo (state.xreg rs1) + lane_hi (state.xreg rs1) * 4294967296)
      + (lane_lo (state.xreg rs2) + lane_hi (state.xreg rs2) * 4294967296)
      - b.cout_1 r_binary * (4294967296 * 4294967296) := by
  have h_compositional := add_compositional m b r_main r_binary h_circuit
  -- `add_circuit_holds` bundles `main_row_in_add_mode`, which gives us
  -- `is_external_op = 1` and `op = OP_ADD` — the premises of `transpile_ADD`.
  obtain ⟨_, _, _, h_isext, h_op, _, _⟩ := h_circuit
  -- Apply `transpile_ADD` to discharge the lane equalities.
  obtain ⟨h_a_lo, h_a_hi, h_b_lo, h_b_hi, _, _, _, _, _⟩ :=
    transpile_ADD m r_main state rs1 rs2 h_isext h_op
  rw [h_compositional]
  unfold main_a_packed main_b_packed
  rw [h_a_lo, h_a_hi, h_b_lo, h_b_hi]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an RV64
    ADD (`.RTYPE (r2, r1, rd, rop.ADD)`) reduces to the pure function
    block supplied by `PureSpec.execute_RTYPE_add_pure`, given that the
    source registers are readable and the PC is known. Wraps
    `PureSpec.execute_RTYPE_add_pure_equiv` to expose the Sail chain at
    this module's export surface — pairs with `equiv_ADD` above to
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

/-- **Metaplan theorem.** The shape the original metaplan
    (`ai_plans/zisk-fv-metaplan.md`) targets: Sail's `execute_instruction`
    on an RV64 ADD equals the state computed by applying `bus_effect` to
    the circuit's execution and memory bus rows.

    Phase 2.5 D3 replaced the monolithic `h_bus_execute_matches_sail`
    hypothesis with decomposed structural bus hypotheses, discharged
    internally via the shape-(a) bus-emission lemma
    `ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw`.

    **Hypotheses.**
    * Circuit side (for the companion `equiv_ADD`): `h_circuit` supplies
      `add_circuit_holds m b r_main r_binary`, and `h_main_a`/`h_main_b`
      pin the Main AIR lanes to `state.xreg rs1`/`rs2`.
    * Sail side (from `equiv_ADD_sail`): `h_input_r1`/`h_input_r2`/
      `h_input_rd`/`h_input_pc` expose the source registers and PC.
    * Bus side (Phase 2.5 D3): structural hypotheses on the two-entry
      execution bus and the three-entry memory bus (ordered rs1_read,
      rs2_read, rd_write), plus an rd-correspondence hypothesis
      `h_rd_match` that identifies the bus's rd-write branch with the
      Sail pure-spec `match add_output.rd` branch. These are strictly
      decomposed from the earlier `h_bus_execute_matches_sail` and
      individually Phase-4 derivable from a PIL-level bus-emission spec.

    **Proof closure.** Composes:
    * `equiv_ADD_sail` — reduces LHS to the Sail `do` block,
    * `bus_effect_matches_sail_alu_rrw` — reduces RHS to the shape-(a)
      `do` block (register-write commutation against nextPC),
    * `h_rd_match` — bridges the `if h :` and `match .rd` dispatches.

    **Historical note.** Inlining this reduction historically required a
    per-bus-entry case analysis over `bus_effect`'s
    foldl, which is more than the metaplan commits to at Phase 1.5 —
    the companion theorems (`equiv_ADD`, `equiv_ADD_sail`) already
    carry the mathematical content; the metaplan-shape theorem just
    repackages them into the statement the original metaplan targeted. -/
theorem equiv_ADD_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok add_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok add_input.r2_val state)
    (h_input_rd : add_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some add_input.PC)
    -- Phase 2.5 D3: structural bus hypotheses (Phase-4 derivable from a
    -- PIL-level bus-emission spec). The execution bus carries the PC
    -- read + nextPC write; the memory bus carries rs1_read, rs2_read,
    -- rd_write as three entries matching shape (a).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_add_pure add_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_idx : add_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = add_input.r1_val + add_input.r2_val) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_ADD_sail state add_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
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

/-- **Track-G companion.** Same conclusion as `equiv_ADD_metaplan`, but
    derives `h_input_r1` and `h_input_r2` internally from a single
    `h_bus : (bus_effect exec_row [e0, e1, e2] state).1` hypothesis via
    `chip_bus_hyps_alu_rrw`. Demonstrates the Phase 5 Track G rewiring
    pattern: two of the four Sail-input register-read parameters collapse
    into one bus-precondition parameter plus two "bus byte ↔ Sail input
    value" match hypotheses that are downstream-derivable from a
    PIL-level bus-emission spec + the restated `transpile_ADD` axiom
    (Phase 5 Track H).

    `h_input_pc` and `h_input_rd` stay as parameters: `h_input_pc`
    lives in a different form (`state.regs.get? Register.PC = .some …`)
    that doesn't directly follow from the chip_bus_hyps `Sail.readReg`
    shape without extra monad-unfolding boilerplate; `h_input_rd` ties
    the regidx-type side of rd and is unrelated to `h_bus`.

    Consumer of `chip_bus_hyps_alu_rrw` — establishes that lemma as
    load-bearing for at least one downstream metaplan path. -/
theorem equiv_ADD_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_add_pure add_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Bus precondition (replaces h_input_r1, h_input_r2):
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    -- Bus byte ↔ Sail input value match (downstream-derivable from
    -- transpile_ADD + operation-bus match):
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r1_val : add_input.r1_val
      = U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                    e0.x4, e0.x5, e0.x6, e0.x7])
    (h_r2_ptr : regidx_to_fin r2 = Transpiler.wrap_to_regidx e1.ptr)
    (h_r2_val : add_input.r2_val
      = U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                    e1.x4, e1.x5, e1.x6, e1.x7])
    -- PC and rd sides (unchanged):
    (h_input_rd : add_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some add_input.PC)
    (h_rd_idx : add_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = add_input.r1_val + add_input.r2_val) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- Split h_bus via chip_bus_hyps_alu_rrw.
  obtain ⟨_, h_rs1_read, h_rs2_read⟩ :=
    ZiskFv.Airs.BusHypotheses.chip_bus_hyps_alu_rrw
      state exec_row e0 e1 e2
      h_exec_len h_e0_mult h_e1_mult
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
      h_bus
  -- Rewrite the derived reads through the match hypotheses to get
  -- equalities in terms of `add_input` fields, as required by
  -- `equiv_ADD_metaplan`.
  have h_input_r1 :
      read_xreg (regidx_to_fin r1) state
        = EStateM.Result.ok add_input.r1_val state := by
    rw [h_r1_ptr, h_r1_val]; exact h_rs1_read
  have h_input_r2 :
      read_xreg (regidx_to_fin r2) state
        = EStateM.Result.ok add_input.r2_val state := by
    rw [h_r2_ptr, h_r2_val]; exact h_rs2_read
  exact equiv_ADD_metaplan state add_input r1 r2 rd exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_rd_idx h_rd_val

end ZiskFv.Equivalence.Add
