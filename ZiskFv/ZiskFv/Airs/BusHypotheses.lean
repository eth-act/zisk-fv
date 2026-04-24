import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.RV64D.Auxiliaries
import ZiskFv.RV64D.BusEffect

/-!
# BusHypotheses — Sail-side input-state derivation (Phase 5 Track G)

Partner module to `Airs/BusEmission.lean`. Where `BusEmission.lean` reduces
the `bus_effect`'s **output state** (`.2`) to the Sail monadic block the
pure-spec writes, this module extracts the `bus_effect`'s **precondition**
(`.1`) — a conjunction of `read_xreg` / `Sail.readReg` equalities about
the Sail state.

The key observation: looking at `bus_effect`'s definition in
`RV64D/BusEffect.lean`, when the execution bus has the standard two-entry
shape and the memory bus carries ordered register / memory reads, the
`.1` field accumulates exactly the equalities

```
Sail.readReg Register.PC state = .ok <pc from exec_row[0]> state
read_xreg (wrap_to_regidx e_read.ptr) state
  = .ok (U64.toBV #v[e_read.x0, …, e_read.x7]) state
```

These are exactly the `h_input_r1`/`h_input_r2`/`h_input_pc` parameters
every `equiv_<OP>_metaplan` theorem inherits from Phase 1.5. The `chip_bus_hyps_<SHAPE>`
lemmas below let metaplan theorems drop those as separate
parameters: a single `h_bus_cond : (bus_effect exec_row mem_row state).1`
hypothesis plus the structural bus properties split into the individual
read equalities.

This is the openvm-fv Gap 1 closure: their `Equivalence/Mul.lean:492-537`
`chip_bus_hypotheses` plays the identical role against
`Valid_VmAirWrapper`'s `bus_effect`.

Five lemmas, one per bus-entry shape ZisK's Main AIR emits:

* `chip_bus_hyps_alu_rrw`  — shape (a):  `[rs1_read, rs2_read, rd_write]`
* `chip_bus_hyps_branch_rrw` — shape (b): empty memory bus (Binary SM
  routes rs1/rs2 reads via the operation bus)
* `chip_bus_hyps_jump_rrw` — shape (c): `[rd_write]`
* `chip_bus_hyps_load_rrrw` — shape (d): `[rs1_read, mem_read, rd_write]`
* `chip_bus_hyps_store_rrrw` — shape (e): `[rs1_read, rs2_read, mem_write]`
-/

namespace ZiskFv.Airs.BusHypotheses

open Goldilocks
open Interaction

private lemma fgl_one_ne_neg_one : ((1 : FGL) = -1) = False := by decide
private lemma fgl_neg_one_self : ((-1 : FGL) = -1) = True := by decide
private lemma fgl_one_self : ((1 : FGL) = 1) = True := by decide
private lemma fgl_zero_ne_neg_one : ((0 : FGL) = -1) = False := by decide
private lemma fgl_zero_ne_one : ((0 : FGL) = 1) = False := by decide

/-- **Shape (a) — ALU / Arith.** Given the structural bus hypotheses
    that identify this as an ALU-RRW row (exec bus [pc_read, nextpc_write];
    memory bus [rs1_read, rs2_read, rd_write], all at as=1),
    `(bus_effect exec_row [e0, e1, e2] state).1` decomposes into three
    Sail-state equalities: PC read, rs1 read, rs2 read.

    The write entries (exec[1] and e2) contribute no precondition — only
    state transitions — and are handled by the partner lemma
    `bus_effect_matches_sail_alu_rrw` in `BusEmission.lean`. -/
theorem chip_bus_hyps_alu_rrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1) :
    Sail.readReg Register.PC state
        = EStateM.Result.ok
            (BitVec.ofNat 64 (exec_row[0]!.pc).val)
            state
    ∧ read_xreg (Transpiler.wrap_to_regidx e0.ptr) state
        = EStateM.Result.ok
            (U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                          e0.x4, e0.x5, e0.x6, e0.x7])
            state
    ∧ read_xreg (Transpiler.wrap_to_regidx e1.ptr) state
        = EStateM.Result.ok
            (U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                          e1.x4, e1.x5, e1.x6, e1.x7])
            state := by
  -- Unfold the bus_effect precondition under the structural hypotheses.
  unfold bus_effect at h_bus
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self, if_true,
             List.foldl_cons, List.foldl_nil] at h_bus
  simp only [h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
             fgl_neg_one_self, fgl_one_ne_neg_one, fgl_one_self,
             if_true, if_false] at h_bus
  -- The write branch (e2) keeps `.1` unchanged; case-split on whether
  -- rd is x0 (no-op) or a real register — both paths leave `.1` the
  -- same conjunction of the three read equalities. Re-associate from
  -- left-heavy `(A ∧ B) ∧ C` to right-heavy `A ∧ B ∧ C` to match goal.
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp only [h_rd_zero, dite_true] at h_bus
    exact ⟨h_bus.1.1, h_bus.1.2, h_bus.2⟩
  · simp only [h_rd_zero, dite_false] at h_bus
    simp only [write_xreg, writeReg_state_success,
               EStateM.Result.map] at h_bus
    exact ⟨h_bus.1.1, h_bus.1.2, h_bus.2⟩

/-- **Shape (b) — externally-routed branch (BEQ family).** Exec bus
    [pc_read, nextpc_write]; memory bus is empty. No register or memory
    reads appear on the Main memory bus (the Binary SM handles rs1/rs2
    reads via the operation bus).

    The `.1` precondition reduces to the single PC-read equality. -/
theorem chip_bus_hyps_branch_rrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_bus : (bus_effect exec_row [] state).1) :
    Sail.readReg Register.PC state
      = EStateM.Result.ok
          (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[0]!.pc).val))
          state := by
  unfold bus_effect at h_bus
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self, if_true,
             List.foldl_nil] at h_bus
  exact h_bus

/-- **Shape (c) — JAL.** Exec bus [pc_read, nextpc_write]; memory bus
    carries exactly one register-write entry (the rd store).

    The `.1` precondition reduces to the single PC-read equality — the
    write entry contributes only state transitions. -/
theorem chip_bus_hyps_jump_rrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e2 : MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e2] state).1) :
    Sail.readReg Register.PC state
      = EStateM.Result.ok
          (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[0]!.pc).val))
          state := by
  unfold bus_effect at h_bus
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self, if_true,
             List.foldl_cons, List.foldl_nil] at h_bus
  simp only [h_m2_mult, h_m2_as,
             fgl_one_ne_neg_one, fgl_one_self,
             if_true, if_false] at h_bus
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp only [h_rd_zero, dite_true] at h_bus
    exact h_bus
  · simp only [h_rd_zero, dite_false] at h_bus
    simp only [write_xreg, writeReg_state_success,
               EStateM.Result.map] at h_bus
    exact h_bus

-- (jump_rrw shape has 1 memory entry + 2-entry exec bus; no re-association needed)

/-- **Shape (d) — LD.** Exec bus [pc_read, nextpc_write]; memory bus
    [rs1_read, mem_read_8, rd_write]. The rs1 entry is a register read
    (as=1); the mem entry is a memory read (as=2); rd is a register write.

    The `.1` precondition reduces to: PC read, rs1 register read, and
    the 8 memory bytes at `e1.ptr..e1.ptr+7` matching `e1.x0..x7`. -/
theorem chip_bus_hyps_load_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1) :
    Sail.readReg Register.PC state
        = EStateM.Result.ok
            (BitVec.ofNat 64 (exec_row[0]!.pc).val)
            state
    ∧ read_xreg (Transpiler.wrap_to_regidx e0.ptr) state
        = EStateM.Result.ok
            (U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                          e0.x4, e0.x5, e0.x6, e0.x7])
            state
    ∧ state.mem[e1.ptr.toNat]? = .some e1.x0
    ∧ state.mem[e1.ptr.toNat + 1]? = .some e1.x1
    ∧ state.mem[e1.ptr.toNat + 2]? = .some e1.x2
    ∧ state.mem[e1.ptr.toNat + 3]? = .some e1.x3
    ∧ state.mem[e1.ptr.toNat + 4]? = .some e1.x4
    ∧ state.mem[e1.ptr.toNat + 5]? = .some e1.x5
    ∧ state.mem[e1.ptr.toNat + 6]? = .some e1.x6
    ∧ state.mem[e1.ptr.toNat + 7]? = .some e1.x7 := by
  unfold bus_effect at h_bus
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self, if_true,
             List.foldl_cons, List.foldl_nil] at h_bus
  -- e1.as = 2 ≠ 1, so it takes the memory-read branch.
  have h_m1_as_ne_one : (e1.as.val = 1) = False := by rw [h_m1_as]; decide
  have h_m1_as_eq_two : (e1.as.val = 2) = True := by rw [h_m1_as]; decide
  simp only [h_m0_mult, h_m0_as, h_m1_mult, h_m1_as_ne_one, h_m1_as_eq_two,
             h_m2_mult, h_m2_as,
             fgl_neg_one_self, fgl_one_ne_neg_one, fgl_one_self,
             if_true, if_false, if_false_left, if_false_right] at h_bus
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp only [h_rd_zero, dite_true] at h_bus
    -- h_bus has shape `((pc ∧ rs1) ∧ (mem[0] ∧ mem[1] ∧ … ∧ mem[7]))`.
    exact ⟨h_bus.1.1, h_bus.1.2,
           h_bus.2.1, h_bus.2.2.1, h_bus.2.2.2.1, h_bus.2.2.2.2.1,
           h_bus.2.2.2.2.2.1, h_bus.2.2.2.2.2.2.1,
           h_bus.2.2.2.2.2.2.2.1, h_bus.2.2.2.2.2.2.2.2⟩
  · simp only [h_rd_zero, dite_false] at h_bus
    simp only [write_xreg, writeReg_state_success,
               EStateM.Result.map] at h_bus
    exact ⟨h_bus.1.1, h_bus.1.2,
           h_bus.2.1, h_bus.2.2.1, h_bus.2.2.2.1, h_bus.2.2.2.2.1,
           h_bus.2.2.2.2.2.1, h_bus.2.2.2.2.2.2.1,
           h_bus.2.2.2.2.2.2.2.1, h_bus.2.2.2.2.2.2.2.2⟩

/-- **Shape (e) — SD.** Exec bus [pc_read, nextpc_write]; memory bus
    [rs1_read, rs2_read, mem_write_8]. Both rs1 and rs2 are register
    reads (as=1); the memory write is as=2.

    The `.1` precondition reduces to PC read + rs1 register read + rs2
    register read. The memory-write entry contributes only state
    transitions (it's handled by partner `bus_effect_matches_sail_store_rrrw`
    in `BusEmission.lean`). -/
theorem chip_bus_hyps_store_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 2)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1) :
    Sail.readReg Register.PC state
        = EStateM.Result.ok
            (BitVec.ofNat 64 (exec_row[0]!.pc).val)
            state
    ∧ read_xreg (Transpiler.wrap_to_regidx e0.ptr) state
        = EStateM.Result.ok
            (U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                          e0.x4, e0.x5, e0.x6, e0.x7])
            state
    ∧ read_xreg (Transpiler.wrap_to_regidx e1.ptr) state
        = EStateM.Result.ok
            (U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                          e1.x4, e1.x5, e1.x6, e1.x7])
            state := by
  unfold bus_effect at h_bus
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self, if_true,
             List.foldl_cons, List.foldl_nil] at h_bus
  -- e2.as = 2 ≠ 1, so it takes the memory-write branch.
  have h_m2_as_ne_one : (e2.as.val = 1) = False := by rw [h_m2_as]; decide
  simp only [h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
             h_m2_as_ne_one,
             fgl_neg_one_self, fgl_one_ne_neg_one, fgl_one_self,
             if_true, if_false, if_false_left, if_false_right] at h_bus
  obtain ⟨⟨hA, hB⟩, hC⟩ := h_bus
  exact ⟨hA, hB, hC⟩

end ZiskFv.Airs.BusHypotheses
