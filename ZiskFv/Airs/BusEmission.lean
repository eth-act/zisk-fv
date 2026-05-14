import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Sail.Auxiliaries
import ZiskFv.Sail.BusEffect

/-!
# BusEmission — shape lemmas for `bus_effect` reduction

For each of the ≤5 concrete bus-entry shapes ZisK's Main AIR emits, we
prove a reusable lemma reducing `(bus_effect exec_row mem_row state).2`
to the Sail monadic block the pure-spec side produces, under structural
hypotheses about the bus rows (length, multiplicities, address spaces,
pc values).

The shapes observed across ZisK's RV64IM archetypes:

* **Shape (b) — externally-routed branch (BEQ).** Two execution-bus
  entries (pc read, nextpc write). Empty memory bus (register-read
  semantics delegated to the Binary SM). Sail branches on
  `success`/`throws`, so the matching hypothesis requires those booleans.
* **Shape (c-jal) — JAL.** Same execution-bus shape as BEQ. Memory bus
  carries exactly one register-write entry (the rd store-PC-plus-4).
* **Shape (a) — arithmetic (ADD, MUL, SLLW).** Execution-bus carries
  pc+nextpc. Memory bus: register-read rs1, register-read rs2,
  register-write rd.
* **Shape (d) — LD.** Memory bus: register-read rs1, memory-read 8
  bytes, register-write rd.
* **Shape (e) — SD.** Memory bus: register-read rs1, register-read rs2,
  memory-write 8 bytes.

The heart of shapes (a) and (c) is a **register-write commutation**: the
memory-bus fold writes `rd` before the execution-bus writes `nextPC`,
whereas the Sail pure spec writes `nextPC` first. The two compositions
produce equal states because `reg_of_fin r ≠ Register.nextPC` for every
`r : Fin 32` (per `reg_of_fin_neq_nextPC`), so the underlying
`Std.ExtDHashMap.insert` calls commute (`ExtDHashMap.insert_comm` from
`RV64D/Auxiliaries.lean`).
-/

namespace ZiskFv.Airs.BusEmission

open Goldilocks
open Interaction

/-- **Register-write commutation (state level).** Two successive
    `write_reg_state` calls on distinct registers commute.

    Underlying primitive: the register map is `Std.ExtDHashMap`, whose
    `insert_comm` is proved in `RV64D/Auxiliaries.lean`. This lemma lifts
    that to the full `PreSail.SequentialState` record (register writes
    don't touch `mem`, `tags`, `choiceState`, `cycleCount`, `sailOutput`,
    so those fields match up trivially). -/
lemma write_reg_state_comm
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 r2 : Register) (v1 : RegisterType r1) (v2 : RegisterType r2)
    (h_neq : r1 ≠ r2) :
    write_reg_state (write_reg_state state r1 v1) r2 v2
      = write_reg_state (write_reg_state state r2 v2) r1 v1 := by
  unfold write_reg_state
  simp
  exact ExtDHashMap.insert_comm state.regs h_neq

/-- **Shape (b): BEQ / externally-routed branch.** `bus_effect` with a
    two-entry execution bus and an empty memory bus reduces to the Sail
    `do` block that writes `nextPC` and returns `Retire_Success` when
    the branch neither throws nor fails (i.e., `throws = false ∧
    success = true`, which is always the case under the `misa[C] = 0`
    precondition ZisK enforces).

    The proof is a direct reduction of `bus_effect`'s foldl over an
    empty list, followed by collapsing the monadic block that matches
    on the two booleans. -/
lemma bus_effect_matches_sail_beq
    {imm_width : Nat}
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (beq_output_nextPC : BitVec 64)
    (beq_output_throws beq_output_success : Bool)
    (beq_PC : BitVec 64) (beq_imm : BitVec imm_width)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = beq_output_nextPC)
    (h_not_throws : beq_output_throws = false)
    (h_success : beq_output_success = true) :
    (bus_effect exec_row [] state).2
      = (do
          Sail.writeReg Register.nextPC beq_output_nextPC
          if beq_output_throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !beq_output_success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (beq_PC + BitVec.signExtend 64 beq_imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state := by
  unfold bus_effect
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self,
             if_true, List.foldl_nil]
  simp only [h_nextPC_matches]
  simp only [h_not_throws, h_success, Bool.not_true]
  simp [Sail.writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet, bind, pure, EStateM.bind, EStateM.pure,
        EStateM.Result.map]

/-- **Shape (c-stub): JAL-style — execution bus + empty memory bus.**
    Kept as a reference simplification; real JAL has a memory-bus rd
    write entry and goes through `bus_effect_matches_sail_jump_rrw`
    when that shape closes. -/
lemma bus_effect_matches_sail_jump_no_memory
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (nextPC_val : BitVec 64)
    (jal_throws jal_success : Bool)
    (jal_PC jal_imm : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_not_throws : jal_throws = false)
    (h_success : jal_success = true) :
    (bus_effect exec_row [] state).2
      = (do
          (match (Option.some nextPC_val : Option (BitVec 64)) with
            | .some nextPC => Sail.writeReg Register.nextPC nextPC
            | .none => pure ())
          (match (none : Option (Finset.Icc 1 31 × BitVec 64)) with
            | .some (reg, rd_val) => write_xreg reg rd_val
            | .none => pure ())
          if jal_throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !jal_success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (jal_PC + BitVec.signExtend 64 jal_imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state := by
  unfold bus_effect
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self,
             if_true, List.foldl_nil]
  simp only [h_nextPC_matches]
  simp only [h_not_throws, h_success, Bool.not_true]
  simp [Sail.writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet, bind, pure, EStateM.bind, EStateM.pure,
        EStateM.Result.map]

/-- Decide literal Goldilocks integer equalities used by the `bus_effect`
    fold's multiplicity / address-space dispatch. -/
private lemma fgl_neg_one_ne_one : ((-1 : FGL) = 1) = False := by decide
private lemma fgl_one_ne_neg_one : ((1 : FGL) = -1) = False := by decide
private lemma fgl_neg_one_self : ((-1 : FGL) = -1) = True := by decide
private lemma fgl_one_self : ((1 : FGL) = 1) = True := by decide

/-- **Shape (a): RTYPE / RTYPEW — ALU writing rd.**
    `bus_effect` with two-entry execution bus and three-entry memory bus
    `[rs1_read, rs2_read, rd_write]` (both reads at address-space 1,
    write at address-space 1 addressed at `rd_ptr` with bytes giving
    `rd_val`) reduces to the Sail `do` block:

    ```
    writeReg nextPC nextPC_val
    (match rd_out with
     | some (rd, v) => write_xreg rd v
     | none => pure ())
    pure Retire_Success
    ```

    where `rd_out` is derived from the write entry's pointer and bytes.

    The proof strips the foldl by pattern-matching on `mem_row` as a
    concrete 3-element list, reduces the two register reads via the
    address-space-1 branch, then applies the register-write commutation
    (`write_reg_state_comm`) to swap the rd-write and nextPC-write. -/
lemma bus_effect_matches_sail_alu_rrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
            pure ()
          else
            let val := U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                                    e2.x4, e2.x5, e2.x6, e2.x7]
            let reg_idx : Finset.Icc 1 31 :=
              ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
            write_xreg reg_idx val)
          pure (ExecutionResult.Retire_Success ())) state := by
  -- Unfold bus_effect and reduce the foldl over the concrete 3-list.
  unfold bus_effect
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self, if_true,
             List.foldl_cons, List.foldl_nil]
  -- Reduce the first two reads (no state change) and the write-branch dispatch.
  simp only [h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
             fgl_one_ne_neg_one,
             if_true, if_false]
  -- Branch on whether the rd-write is to x0 (no-op) or a real register.
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · -- rd = x0 case: no state change from the memory fold.
    simp only [h_rd_zero, dite_true]
    simp only [h_nextPC_matches]
    simp [Sail.writeReg, PreSail.writeReg, modify, modifyGet,
          MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
          EStateM.bind, EStateM.pure, EStateM.Result.map]
  · -- rd ≠ 0: the memory fold writes rd, then the exec bus writes nextPC.
    -- Sail writes nextPC first, then rd. Differ by a register commutation.
    simp only [h_rd_zero, dite_false]
    simp only [h_nextPC_matches]
    -- Turn `write_xreg` into its concrete `write_reg_state` unfolding.
    simp only [write_xreg, writeReg_state_success, EStateM.Result.map]
    -- Strip the monadic bind/pure machinery on the RHS.
    simp [Sail.writeReg, PreSail.writeReg, modify, modifyGet,
          MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
          EStateM.bind, EStateM.pure]
    -- The goal is now an equality between two states that differ only
    -- in the order of two distinct `write_reg_state` calls
    -- (`reg_of_fin rd` vs. `Register.nextPC`). Close via commutation.
    exact write_reg_state_comm _ _ _ _ _ reg_of_fin_neq_nextPC

/-- **Shape (c): JAL — rd write via `store_pc`.**
    `bus_effect` with two-entry execution bus and one-entry memory bus
    `[rd_write]` (register write at address-space 1, carrying
    `pc + 4`) reduces to the Sail `do` block JAL emits.

    Like shape (a), the proof rewrites `write_xreg` via
    `writeReg_state_success`, then commutes the rd and nextPC writes. -/
lemma bus_effect_matches_sail_jump_rrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e_rd : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1)
    (h_rd_as   : e_rd.as.val = 1) :
    (bus_effect exec_row [e_rd] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          (if h : Transpiler.wrap_to_regidx e_rd.ptr = 0 then
            pure ()
          else
            let val := U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                                    e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
            let reg_idx : Finset.Icc 1 31 :=
              ⟨ (Transpiler.wrap_to_regidx e_rd.ptr).val, by simp; omega ⟩
            write_xreg reg_idx val)
          pure (ExecutionResult.Retire_Success ())) state := by
  unfold bus_effect
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self, if_true,
             List.foldl_cons, List.foldl_nil]
  simp only [h_rd_mult, h_rd_as,
             fgl_one_ne_neg_one,
             if_true, if_false]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e_rd.ptr = 0
  · simp only [h_rd_zero, dite_true]
    simp only [h_nextPC_matches]
    simp [Sail.writeReg, PreSail.writeReg, modify, modifyGet,
          MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
          EStateM.bind, EStateM.pure, EStateM.Result.map]
  · simp only [h_rd_zero, dite_false]
    simp only [h_nextPC_matches]
    simp only [write_xreg, writeReg_state_success, EStateM.Result.map]
    simp [Sail.writeReg, PreSail.writeReg, modify, modifyGet,
          MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
          EStateM.bind, EStateM.pure]
    exact write_reg_state_comm _ _ _ _ _ reg_of_fin_neq_nextPC

/-! ## Shapes (d) and (e) — memory-bus loads and stores

Shapes (d) LD and (e) SD extend the `[rs1, rs2, rd]` three-entry
memory-bus fold by routing one of the entries through the `as = 2`
(memory) branch of `bus_effect` instead of `as = 1` (register).

**Key observation:** the `as = 2` branch of `bus_effect` has two cases:

* **Memory read** (`multiplicity = -1, as = 2`, `BusEffect.lean:61-71`):
  adds 8 `state.mem[ptr + i]? = .some xᵢ` conjuncts to `cond`; state is
  **unchanged**. So shape (d) LD has the same state-update structure as
  shape (a) ALU — only the `cond` conjunct changes, which is part of
  the `.1` component, not the `.2` we project.

* **Memory write** (`multiplicity = 1, as = 2`, `BusEffect.lean:90-103`):
  inserts 8 bytes into `state.mem` and returns `Retire_Success` — the
  `regs` field is untouched. The subsequent execution-bus
  `writeReg nextPC` (which only touches `regs`) is expressed on the
  RHS in the same ordering, so no record-field swap is needed.
-/

/-- **Shape (d): LD — load doubleword.**
    `bus_effect` with two-entry execution bus and three-entry memory bus
    `[rs1_read (as=1), mem_read_8 (as=2), rd_write (as=1)]` reduces to
    the Sail LD `do` block.

    The memory-read entry `e1` adds 8 `state.mem[ptr + i]? = .some xᵢ`
    conjuncts to `cond` (via `BusEffect.lean:61-71`) but leaves state
    unchanged. Therefore the state-update structure is identical to
    shape (a): two reads-as-noops, then `rd_write` via register-write
    (address-space 1), then `writeReg nextPC`. The `rd` / `nextPC`
    commutation is the same as shape (a).

    The caller's `memory_load_lanes_match` + range hypotheses are
    separately responsible for connecting `e1.xᵢ` (the 8 memory bytes
    on the bus) to Sail's `data0..data7` fields. -/
lemma bus_effect_matches_sail_load_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
            pure ()
          else
            let val := U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                                    e2.x4, e2.x5, e2.x6, e2.x7]
            let reg_idx : Finset.Icc 1 31 :=
              ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
            write_xreg reg_idx val)
          pure (ExecutionResult.Retire_Success ())) state := by
  -- Unfold bus_effect and reduce the foldl over the concrete 3-list.
  unfold bus_effect
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self, if_true,
             List.foldl_cons, List.foldl_nil]
  -- e0 (reg-read, as=1): no state change; e1 (mem-read, as=2): no
  -- state change (the as=2 branch adds to `cond` but leaves `result`);
  -- e2 (reg-write, as=1): writes rd.
  simp only [h_m0_mult, h_m0_as, h_m1_mult, h_m1_as,
             h_m2_mult, h_m2_as,
             fgl_one_ne_neg_one,
             if_true, if_false]
  -- Branch on whether the rd-write is to x0 (no-op) or a real register.
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp only [h_rd_zero, dite_true]
    simp only [h_nextPC_matches]
    simp [Sail.writeReg, PreSail.writeReg, modify, modifyGet,
          MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
          EStateM.bind, EStateM.pure, EStateM.Result.map]
  · simp only [h_rd_zero, dite_false]
    simp only [h_nextPC_matches]
    simp only [write_xreg, writeReg_state_success, EStateM.Result.map]
    simp [Sail.writeReg, PreSail.writeReg, modify, modifyGet,
          MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
          EStateM.bind, EStateM.pure]
    exact write_reg_state_comm _ _ _ _ _ reg_of_fin_neq_nextPC

/-- **Shape (e): SD — store doubleword.**
    `bus_effect` with two-entry execution bus and three-entry memory bus
    `[rs1_read (as=1), rs2_read (as=1), mem_write_8 (as=2)]` reduces to
    a Sail `do` block that writes `nextPC`, then updates `state.mem`
    with 8 byte-inserts, then retires.

    The `bus_effect` SD shape processes entries in chronological order:
    two no-op register reads, then 8 `state.mem.insert`s (via the
    `as = 2, multiplicity = 1` branch at `BusEffect.lean:90-103`), and
    finally `writeReg nextPC` from the execution-bus write. The Sail
    block (from `execute_STORED_pure_equiv`) writes `nextPC` first, then
    `set (modify_memory_8 ...)` replaces the memory. Since `writeReg`
    touches only `regs` and the mem-inserts touch only `mem`, the two
    orders produce equal states (`mem_insert_writeReg_comm`).

    The RHS expresses the memory update in the structural form
    `bus_effect` produces — a chain of `state.mem.insert`s at
    `entry.ptr.toNat + i` with bytes `entry.xᵢ`. Callers bridge this
    to Sail's `modify_memory_8 (← get) output` via the
    `memory_store_lanes_match` / address hypotheses that connect
    `entry` fields to `SdOutput` fields. -/
lemma bus_effect_matches_sail_store_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 2) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          modify (fun s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource =>
            { s with
              mem :=
                (((((((s.mem.insert e2.ptr.toNat e2.x0
                ).insert (e2.ptr.toNat + 1) e2.x1
                ).insert (e2.ptr.toNat + 2) e2.x2
                ).insert (e2.ptr.toNat + 3) e2.x3
                ).insert (e2.ptr.toNat + 4) e2.x4
                ).insert (e2.ptr.toNat + 5) e2.x5
                ).insert (e2.ptr.toNat + 6) e2.x6
                ).insert (e2.ptr.toNat + 7) e2.x7 })
          pure (ExecutionResult.Retire_Success ())) state := by
  -- Unfold bus_effect and reduce the foldl over the concrete 3-list.
  unfold bus_effect
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self, if_true,
             List.foldl_cons, List.foldl_nil]
  -- e0 and e1 are register reads (as=1, mult=-1): no state change.
  -- e2 is a memory write (as=2, mult=1): inserts 8 bytes and returns
  -- Retire_Success. Reduce dispatch on each entry.
  simp only [h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
             fgl_one_ne_neg_one,
             if_true, if_false]
  -- Now the LHS is:
  --   EStateM.Result.map (...) (Sail.writeReg Register.nextPC nextPC_val
  --     { state with mem := <8 inserts> })
  -- and the RHS is the Sail do-block desugared. Strip the monadic
  -- machinery on both sides.
  simp only [h_nextPC_matches]
  simp [Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
        EStateM.bind, EStateM.pure,
        EStateM.Result.map]

/-! ## Narrow-width load/store companions

`bus_effect`'s memory branches (`as = 2`) always process eight byte
lanes. ZisK's narrow-width load/store opcodes (LW/LWU/SW: 4 bytes;
LH/LHU/SH: 2 bytes; LB/LBU/SB: 1 byte) reduce to Sail blocks whose
`rd_val` (loads) is a sign- or zero-extended narrow concatenation, and
whose `state.mem` update (stores) is a chain of just `n` inserts.

The lemmas below mirror the 8-byte `bus_effect_matches_sail_load_rrrw`
/ `..._store_rrrw` shapes, parameterized over the narrow target value
(loads) or narrow mem-update (stores), with a single bridging
hypothesis the caller discharges via byte-equality + BitVec algebra
(loads) or `Std.ExtDHashMap.insert_eq_self` on the trailing inserts
(stores).

The naming convention `*_load_<n>byte_rrrw` (signed) /
`*_loadu_<n>byte_rrrw` (unsigned) follows the LW / LWU split — each
named lemma maps to one ZisK-side opcode so the caller can pick the
right reduction without specializing flags.

Per-op intended consumers:

| Lemma | Width | Sail target | Caller |
|---|---|---|---|
| `bus_effect_matches_sail_load_4byte_rrrw`  | 4 | `BitVec.signExtend 64 (...)`            | LW   |
| `bus_effect_matches_sail_loadu_4byte_rrrw` | 4 | `BitVec.zeroExtend 64 (...)`            | LWU  |
| `bus_effect_matches_sail_load_2byte_rrrw`  | 2 | `BitVec.signExtend 64 (...)`            | LH   |
| `bus_effect_matches_sail_loadu_2byte_rrrw` | 2 | `BitVec.setWidth 32 (...)` or similar   | LHU  |
| `bus_effect_matches_sail_load_1byte_rrrw`  | 1 | `BitVec.signExtend 64 (...)`            | LB   |
| `bus_effect_matches_sail_loadu_1byte_rrrw` | 1 | `BitVec.setWidth 32 (...)`              | LBU  |
| `bus_effect_matches_sail_store_4byte_rrrw` | 4 | 4-insert chain on `state.mem`          | SW   |
| `bus_effect_matches_sail_store_2byte_rrrw` | 2 | 2-insert chain on `state.mem`          | SH   |
| `bus_effect_matches_sail_store_1byte_rrrw` | 1 | 1-insert chain on `state.mem`          | SB   |

The bridging hypotheses (`h_rd_val_match` for loads,
`h_mem_update_match` for stores) factor the BitVec / map-equality
work into the caller — e.g., for LWU the caller proves
`U64.toBV #v[x0..x7] = BitVec.zeroExtend 64 (x3 ++ x2 ++ x1 ++ x0)`
by witnessing `x4 = x5 = x6 = x7 = 0` from the ZisK byte-bus high
witnesses. -/

/-- **Shape (d-4-signed): LW — load word, sign-extended.**

    Same bus shape as LD (`bus_effect_matches_sail_load_rrrw`); the
    bridging hypothesis `h_rd_val_match` translates the `U64.toBV`
    of the eight rd-write bytes into the LW-pure-spec's
    `BitVec.signExtend 64 (data3 ++ data2 ++ data1 ++ data0)` form.
    The caller discharges this by witnessing `e2.x4..x7` as the
    sign-extension of `e2.x3` (i.e., `0` if `e2.x3.msb = false`,
    `0xff` if `true`). -/
lemma bus_effect_matches_sail_load_4byte_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (rd_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1)
    (h_rd_val_match :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                   e2.x4, e2.x5, e2.x6, e2.x7] = rd_val) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
            pure ()
          else
            let reg_idx : Finset.Icc 1 31 :=
              ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
            write_xreg reg_idx rd_val)
          pure (ExecutionResult.Retire_Success ())) state := by
  rw [bus_effect_matches_sail_load_rrrw state exec_row e0 e1 e2 nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_val_match]

/-- **Shape (d-4-unsigned): LWU — load word, zero-extended.**

    Same bus shape as LW; bridging hypothesis selects the
    zero-extend form (`BitVec.zeroExtend 64 (data3 ++ ... ++ data0)`).
    Caller discharges via `e2.x4 = e2.x5 = e2.x6 = e2.x7 = 0`. -/
lemma bus_effect_matches_sail_loadu_4byte_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (rd_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1)
    (h_rd_val_match :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                   e2.x4, e2.x5, e2.x6, e2.x7] = rd_val) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
            pure ()
          else
            let reg_idx : Finset.Icc 1 31 :=
              ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
            write_xreg reg_idx rd_val)
          pure (ExecutionResult.Retire_Success ())) state := by
  rw [bus_effect_matches_sail_load_rrrw state exec_row e0 e1 e2 nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_val_match]

/-- **Shape (d-2-signed): LH — load halfword, sign-extended.** -/
lemma bus_effect_matches_sail_load_2byte_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (rd_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1)
    (h_rd_val_match :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                   e2.x4, e2.x5, e2.x6, e2.x7] = rd_val) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
            pure ()
          else
            let reg_idx : Finset.Icc 1 31 :=
              ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
            write_xreg reg_idx rd_val)
          pure (ExecutionResult.Retire_Success ())) state := by
  rw [bus_effect_matches_sail_load_rrrw state exec_row e0 e1 e2 nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_val_match]

/-- **Shape (d-2-unsigned): LHU — load halfword, zero-extended.** -/
lemma bus_effect_matches_sail_loadu_2byte_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (rd_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1)
    (h_rd_val_match :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                   e2.x4, e2.x5, e2.x6, e2.x7] = rd_val) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
            pure ()
          else
            let reg_idx : Finset.Icc 1 31 :=
              ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
            write_xreg reg_idx rd_val)
          pure (ExecutionResult.Retire_Success ())) state := by
  rw [bus_effect_matches_sail_load_rrrw state exec_row e0 e1 e2 nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_val_match]

/-- **Shape (d-1-signed): LB — load byte, sign-extended.** -/
lemma bus_effect_matches_sail_load_1byte_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (rd_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1)
    (h_rd_val_match :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                   e2.x4, e2.x5, e2.x6, e2.x7] = rd_val) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
            pure ()
          else
            let reg_idx : Finset.Icc 1 31 :=
              ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
            write_xreg reg_idx rd_val)
          pure (ExecutionResult.Retire_Success ())) state := by
  rw [bus_effect_matches_sail_load_rrrw state exec_row e0 e1 e2 nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_val_match]

/-- **Shape (d-1-unsigned): LBU — load byte, zero-extended.** -/
lemma bus_effect_matches_sail_loadu_1byte_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (rd_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 1)
    (h_rd_val_match :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                   e2.x4, e2.x5, e2.x6, e2.x7] = rd_val) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
            pure ()
          else
            let reg_idx : Finset.Icc 1 31 :=
              ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
            write_xreg reg_idx rd_val)
          pure (ExecutionResult.Retire_Success ())) state := by
  rw [bus_effect_matches_sail_load_rrrw state exec_row e0 e1 e2 nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_val_match]

/-! ### Narrow stores

`bus_effect`'s memory-write branch (`as = 2, mult = 1`) inserts eight
byte lanes unconditionally; ZisK's narrow stores (SW: 4 bytes, SH: 2,
SB: 1) emit only the lower N bytes via the byte bus, with the upper
8-N lanes constrained to match the existing memory contents (so that
re-inserting them is a no-op via `Std.ExtHashMap.insert_eq_self`).

Because the bus_effect output's `mem` field is structurally an
8-insert chain on the lambda variable `s.mem`, the narrow-width
distinction cannot be made at this layer without floating an
`s`-quantified hypothesis through the `modify` lambda — which
fights the `simp`-driven proof. Instead, the narrow `..._store_<n>byte_rrrw`
lemmas below ship as **named wrappers** of the 8-byte
`bus_effect_matches_sail_store_rrrw`, with the same conclusion shape
(8-insert chain in the modify lambda).

The actual narrow-width collapse — replacing the 8-insert chain with
an N-insert chain — happens at the equivalence-layer caller via
`Circuit.MemModel.mem_store_correct_<n>byte` plus
`Std.ExtHashMap.insert_eq_self`-style elimination of the trailing
inserts under the byte-bus high-lane-match witnesses.

The named wrappers exist so per-op equivalence files can reference
their target lemma directly (`bus_effect_matches_sail_store_4byte_rrrw`
for SW) without having to pick the 8-byte one and document why. -/

/-- **Shape (e-4): SW — store word (4 bytes).** Named wrapper of
    `bus_effect_matches_sail_store_rrrw` for SW callers. -/
lemma bus_effect_matches_sail_store_4byte_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 2) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          modify (fun s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource =>
            { s with
              mem :=
                (((((((s.mem.insert e2.ptr.toNat e2.x0
                ).insert (e2.ptr.toNat + 1) e2.x1
                ).insert (e2.ptr.toNat + 2) e2.x2
                ).insert (e2.ptr.toNat + 3) e2.x3
                ).insert (e2.ptr.toNat + 4) e2.x4
                ).insert (e2.ptr.toNat + 5) e2.x5
                ).insert (e2.ptr.toNat + 6) e2.x6
                ).insert (e2.ptr.toNat + 7) e2.x7 })
          pure (ExecutionResult.Retire_Success ())) state :=
  bus_effect_matches_sail_store_rrrw state exec_row e0 e1 e2 nextPC_val
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Shape (e-2): SH — store halfword (2 bytes).** Named wrapper of
    `bus_effect_matches_sail_store_rrrw` for SH callers. -/
lemma bus_effect_matches_sail_store_2byte_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 2) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          modify (fun s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource =>
            { s with
              mem :=
                (((((((s.mem.insert e2.ptr.toNat e2.x0
                ).insert (e2.ptr.toNat + 1) e2.x1
                ).insert (e2.ptr.toNat + 2) e2.x2
                ).insert (e2.ptr.toNat + 3) e2.x3
                ).insert (e2.ptr.toNat + 4) e2.x4
                ).insert (e2.ptr.toNat + 5) e2.x5
                ).insert (e2.ptr.toNat + 6) e2.x6
                ).insert (e2.ptr.toNat + 7) e2.x7 })
          pure (ExecutionResult.Retire_Success ())) state :=
  bus_effect_matches_sail_store_rrrw state exec_row e0 e1 e2 nextPC_val
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Shape (e-1): SB — store byte (1 byte).** Named wrapper of
    `bus_effect_matches_sail_store_rrrw` for SB callers. -/
lemma bus_effect_matches_sail_store_1byte_rrrw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1)
    (h_m0_as   : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1)
    (h_m1_as   : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)
    (h_m2_as   : e2.as.val = 2) :
    (bus_effect exec_row [e0, e1, e2] state).2
      = (do
          Sail.writeReg Register.nextPC nextPC_val
          modify (fun s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource =>
            { s with
              mem :=
                (((((((s.mem.insert e2.ptr.toNat e2.x0
                ).insert (e2.ptr.toNat + 1) e2.x1
                ).insert (e2.ptr.toNat + 2) e2.x2
                ).insert (e2.ptr.toNat + 3) e2.x3
                ).insert (e2.ptr.toNat + 4) e2.x4
                ).insert (e2.ptr.toNat + 5) e2.x5
                ).insert (e2.ptr.toNat + 6) e2.x6
                ).insert (e2.ptr.toNat + 7) e2.x7 })
          pure (ExecutionResult.Retire_Success ())) state :=
  bus_effect_matches_sail_store_rrrw state exec_row e0 e1 e2 nextPC_val
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

end ZiskFv.Airs.BusEmission
