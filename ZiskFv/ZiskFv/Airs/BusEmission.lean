import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.RV64D.Auxiliaries
import ZiskFv.RV64D.BusEffect

/-!
# BusEmission — shape lemmas for `bus_effect` reduction (Phase 2.5 D3)

This module closes the `h_bus_execute_matches_sail` obligations that all
archetype `equiv_*_metaplan` theorems inherited as parameters from
Phase 1.5. For each of the ≤5 concrete bus-entry shapes ZisK's Main AIR
emits, we prove a reusable lemma that reduces
`(bus_effect exec_row mem_row state).2` to the Sail monadic block the
pure-spec side produces — under **structural** hypotheses about the bus
rows (length, multiplicities, address spaces, pc values) that the caller
can always discharge from a PIL bus-emission spec.

The shapes observed across ZisK's RV64IM archetypes:

* **Shape (b) — externally-routed branch (BEQ).** Two execution-bus
  entries (pc read, nextpc write). Empty memory bus (register-read
  semantics are delegated to the Binary SM — they don't appear on the
  Main memory bus). Sail branches on `success`/`throws`, so the matching
  hypothesis requires those booleans.

* **Shape (c-jal) — JAL.** Same execution-bus shape as BEQ. Memory bus
  carries exactly one register-write entry (the rd store-PC-plus-4).

* **Shape (a) — arithmetic (ADD, MUL).** Execution-bus carries pc+nextpc.
  Memory bus carries three entries: register-read rs1, register-read rs2,
  register-write rd. For ADD we can close this with three instances of
  the register-read/write pattern.

* **Shape (d) — LD.** Memory bus: register-read rs1, memory-read 8 bytes,
  register-write rd. Requires the D1-authored `vmem_read_aligned_equiv`
  to bridge byte lanes to Sail's `vmem_read_addr` loop.

* **Shape (e) — SD.** Memory bus: register-read rs1, register-read rs2,
  memory-write 8 bytes. Requires D1-authored `vmem_write_aligned_equiv`.

**Budget allowance.** Per D3e, hardest shapes may remain parameterized
and deferred to Phase 4. This module ships the shapes that closed
within the 3-day-per-shape budget.
-/

namespace ZiskFv.Airs.BusEmission

open Goldilocks
open Interaction

/-- **Shape (b): BEQ / externally-routed branch.** `bus_effect` with a
    two-entry execution bus and an empty memory bus reduces to the Sail
    `do` block that writes `nextPC` and returns `Retire_Success` when
    the branch neither throws nor fails (i.e., `throws = false ∧
    success = true`, which is always the case under the `misa[C] = 0`
    precondition ZisK enforces).

    The proof is a direct reduction of `bus_effect`'s foldl over an
    empty list, followed by collapsing the monadic block that matches
    on the two booleans.

    **PIL derivation obligation for Phase 4.** The callers discharge the
    four structural hypotheses (exec length, both multiplicities, the pc
    value in slot 1) from a PIL-level bus-emission spec; the boolean
    hypotheses (`throws = false`, `success = true`) come from the ZisK
    `misa[C] = 0` invariant applied to the pure-spec `execute_BEQ_pure`
    output. -/
theorem bus_effect_matches_sail_beq
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
  -- Reduce `bus_effect` on empty memory bus.
  unfold bus_effect
  simp only [h_exec_len, h_e0_mult, h_e1_mult, and_self,
             if_true, List.foldl_nil]
  -- After foldl_nil, the `post_memory` is `initial_result = (pc_read_prop, .ok Retire_Success state)`.
  -- Since post_memory.2 = .ok _ _, the match falls through to the nextPC write branch.
  simp only [h_nextPC_matches]
  -- On the Sail side, reduce the `do` block under the boolean
  -- hypotheses (throws = false, success = true).
  simp only [h_not_throws, h_success, Bool.not_true]
  -- Both sides are now of shape
  --   EStateM.Result.map (fun _ => Retire_Success) (Sail.writeReg Register.nextPC beq_output_nextPC state)
  -- vs.
  --   (do Sail.writeReg Register.nextPC beq_output_nextPC; pure Retire_Success) state.
  -- Unfold the do block and simp through bind/map.
  simp [Sail.writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet, bind, pure, EStateM.bind, EStateM.pure,
        EStateM.Result.map]

/-- **Shape (c-stub): JAL-style — execution bus + empty memory bus.**
    Kept as a reference simplification; real JAL has a memory-bus rd
    write entry and goes through `bus_effect_matches_sail_jal_full`
    when that shape closes (deferred to Phase 4 per D3e — the
    register-write commutation against `Sail.writeReg Register.nextPC`
    requires non-trivial `Std.ExtDHashMap.insert_comm` reasoning).

    Parameters mirror `bus_effect_matches_sail_beq`. -/
theorem bus_effect_matches_sail_jump_no_memory
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

/-! ## Shapes (a), (c-rd-write), (d), (e) — deferred to Phase 4

The remaining four shapes all share a common obstacle: the bus-effect
model applies the memory-bus fold's side-effects **before** the
execution-bus `Sail.writeReg Register.nextPC`, while the Sail
pure-spec monadic block writes `nextPC` **first**, then performs the
register or memory side-effects. The two compositions produce equal
states (the register writes commute because `reg_of_fin r ≠
Register.nextPC` holds for all `r : Fin 32`, per
`reg_of_fin_neq_nextPC` in `RV64D/Auxiliaries.lean`), but the proof
requires `Std.ExtDHashMap.insert_comm`-style reasoning that this phase
did not develop.

The callers of the affected metaplan theorems (`equiv_ADD_metaplan`,
`equiv_JAL_metaplan`, `equiv_LD_metaplan`, `equiv_SD_metaplan`,
`equiv_MUL_metaplan`, `equiv_SLLW_metaplan`) therefore remain
parameterized on `h_bus_execute_matches_sail` — the D3e budget
allowance. Phase 4's scope already includes the PIL-level bus-emission
spec that discharges this hypothesis; closing it there is natural
because the surrounding `matches_entry` / `memory_load_lanes_match` /
etc. predicates are also Phase-4 obligations.

**Signatures for the deferred shape lemmas** (for Phase 4 reference):

* `bus_effect_matches_sail_rtype`: `exec_row` length 2, `mem_row =
  [rs1_read, rs2_read, rd_write]` — pattern for ADD, MUL, SLLW. Reduce
  via `write_reg_state_comm` after handling the foldl through three
  entries.

* `bus_effect_matches_sail_jal`: `exec_row` length 2, `mem_row =
  [rd_write]` — JAL's single register-write entry. Same
  commutation obligation as shape (a) but simpler.

* `bus_effect_matches_sail_ld`: needs `vmem_read_aligned_equiv` from
  D1 (currently blocked — see `ai_plans/zisk-fv-phase-2.md` Task D1).

* `bus_effect_matches_sail_sd`: needs `vmem_write_aligned_equiv` from
  D1 (currently blocked).
-/

end ZiskFv.Airs.BusEmission
