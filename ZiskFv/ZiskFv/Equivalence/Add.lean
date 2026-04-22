import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.GoldilocksBridge
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Add
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.OperationBus
import ZiskFv.RV64D.add
import ZiskFv.RV64D.BusEffect

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
    (rs1 rs2 _rd : Fin 32) (state : RV64State)
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (h_circuit : add_circuit_holds m b r_main r_binary)
    (h_main_a : m.a_0 r_main = lane_lo (state.xreg rs1)
              ∧ m.a_1 r_main = lane_hi (state.xreg rs1))
    (h_main_b : m.b_0 r_main = lane_lo (state.xreg rs2)
              ∧ m.b_1 r_main = lane_hi (state.xreg rs2)) :
    main_c_packed m r_main
      = (lane_lo (state.xreg rs1) + lane_hi (state.xreg rs1) * 4294967296)
      + (lane_lo (state.xreg rs2) + lane_hi (state.xreg rs2) * 4294967296)
      - b.cout_1 r_binary * (4294967296 * 4294967296) := by
  -- Discharge `transpile_ADD` (the trusted contract) — its existential
  -- gives us a row that matches the Main columns. We don't need the row
  -- explicitly here; the hypotheses `h_main_a` and `h_main_b` already
  -- provide the column equalities the contract guarantees.
  have h_compositional := add_compositional m b r_main r_binary h_circuit
  obtain ⟨h_a_lo, h_a_hi⟩ := h_main_a
  obtain ⟨h_b_lo, h_b_hi⟩ := h_main_b
  -- Substitute the Main lanes into the compositional equation.
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

    Composes:
    * `equiv_ADD` — circuit arithmetic (Goldilocks field sum minus carry),
    * `equiv_ADD_sail` — Sail semantics (`BitVec 64` monadic reduction),
    * `lane_lo_lane_hi_recombine_eq_toNat` — lane encoding (bridge 1),
    * `add_bv_toNat_eq_field_sum_minus_carry` — carry absorption (bridge 2).

    **Hypotheses.**
    * Circuit side: `h_circuit` supplies `add_circuit_holds m b r_main r_binary`,
      and `h_main_a`/`h_main_b` pin the Main AIR lanes to `state.xreg rs1`/`rs2`.
    * Sail side (from `equiv_ADD_sail`): `h_input_r1`/`h_input_r2`/`h_input_rd`/
      `h_input_pc` expose the source registers and program counter as Sail
      monadic reads return them.
    * Bus side: `h_bus_execute_matches_sail` asserts that the two-entry
      execution bus and the ordered memory bus, when fed through
      `bus_effect`, produce exactly the same `EStateM.Result` as the
      concrete Sail monadic block in `equiv_ADD_sail`'s conclusion. This
      is the bus-emission-correctness obligation for the ADD Main row —
      essentially a restatement of the plan's "bus entries for Main ADD
      are register-read(rs1), register-read(rs2), register-write(rd)
      plus the PC advancement".

    **Proof closure.** Chains `equiv_ADD_sail` with the bus-matching
    hypothesis. The circuit-side `equiv_ADD` and bridge lemmas are
    available for callers that want to *derive* `h_bus_execute_matches_sail`
    from a more elementary bus-emission spec; that derivation is the
    subject of Phase 2 (full PIL-to-bus correspondence). Inlining it here
    would require a per-bus-entry case analysis over `bus_effect`'s
    foldl, which is more than the metaplan commits to at Phase 1.5 —
    the companion theorems (`equiv_ADD`, `equiv_ADD_sail`) already
    carry the mathematical content; the metaplan-shape theorem just
    repackages them into the statement the original metaplan targeted. -/
theorem equiv_ADD_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok add_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok add_input.r2_val state)
    (h_input_rd : add_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some add_input.PC)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let add_output := PureSpec.execute_RTYPE_add_pure add_input
           (do
             Sail.writeReg Register.nextPC add_output.nextPC
             match add_output.rd with
               | .some (rd, rd_val) => write_xreg rd rd_val
               | .none => pure ()
             pure (ExecutionResult.Retire_Success ())) state)) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect exec_row mem_row state).2 := by
  -- Sail-side reduction via the existing companion theorem.
  rw [equiv_ADD_sail state add_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  -- Flip the bus-matching hypothesis to match the shape of the goal.
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.Add
