import Mathlib

import ZiskFv.EquivCore.Add
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_ADD` trust-discharge wrapper — BinaryAdd shape

Discharges, on top of the canonical `equiv_ADD`, the
`main_row_in_add_mode` 4-field bundle and the 8 `e2.x{0..7}` byte
ranges. Derives:

* `m.m32 r_main = 0` from `transpile_ADD` (class #1).
* `m.flag r_main = 0` from `op_bus_perm_sound_BinaryAdd` (class #4)
  via the `matches_entry` flag-slot projection (BinaryAdd's
  provider emission pins `flag = 0` per `binary_add.pil:25`).
* `h_e2_0..h_e2_7` from `memory_bus_entry_byte_range_perm_sound`
  (class #5b), unpacking the 8-conjunction into the eight
  hypotheses `equiv_ADD` consumes.

Trust footprint: `transpile_ADD` (#1), `op_bus_perm_sound_BinaryAdd`
(#4), `memory_bus_entry_byte_range_perm_sound` (#5b) plus
`equiv_ADD`'s existing closure. Zero new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.Add


/-- **Trust-discharged wrapper for `equiv_ADD`.**

    Caller obligations (signature header, ordered):
    1. The Sail-side inputs (`state`, `add_input`, `r1`, `r2`, `rd`).
    2. The two AIR validators with the selected Main row index
       (`m : Valid_Main`, `b : Valid_BinaryAdd`, `r_main : ℕ`).
       Compliance.lean shares `(m, b)` across every BinaryAdd-shape
       opcode (ADD, ADDI).
    3. The structural bus rows (`exec_row`, `e0`, `e1`, `e2`).
    4. The activation + opcode pins on Main (`h_main_active`,
       `h_main_op_add`). Both come from Compliance.lean's
       program-counter handshake on the row hosting the ADD
       instruction.
    5. The Main-side constructibility bundle (`h_main_subset`).
       Compliance.lean delivers this from a universal
       `∀ r, add_universal_row m r` parameter shared across all
       BinaryAdd-shape opcodes.
    6. The BinaryAdd-side universal-per-row validity (`h_b_core`).
       Compliance.lean shares this across all BinaryAdd-shape
       opcodes (single AIR per shape).
    7. The lane-match for the rd-write entry (`h_lane_rd`) —
       caller-supplied; discharged downstream from
       `memory_bus_register_write_perm_sound` when Mem-side AIR
       data is plumbed through.
    8. The Sail-side state predicates (SPEC-PRE):
       `h_input_r1_sail`, `h_input_r2_sail`, `h_input_rd`,
       `h_input_pc`.
    9. The bus-protocol structural hypotheses — pass-through from
       `equiv_ADD`; Compliance.lean supplies these from the same
       bus-shape obligations as every other opcode in the shape.

    Derived internally (NOT caller-supplied):
    * `m.m32 r_main = 0` — from `transpile_ADD` (class #1) applied to
      `h_main_active` + `h_main_op_add`.
    * `m.flag r_main = 0` — from `op_bus_perm_sound_BinaryAdd`
      (class #4) → `matches_entry` flag-slot projection. The
      BinaryAdd provider emission pins `flag = 0` (no comparison
      output for pure addition).
    * `h_main_mode : main_row_in_add_mode m r_main` — assembled
      from the four pins above (`is_external_op = 1`, `op = OP_ADD`,
      `m32 = 0`, `flag = 0`).
    * `h_e2_0..h_e2_7 : e2.x{0..7}.val < 256` — unpacked from
      `memory_bus_entry_byte_range_perm_sound e2` (class #5b).

    Trust footprint: `transpile_ADD` (class #1),
    `op_bus_perm_sound_BinaryAdd` (class #4),
    `memory_bus_entry_byte_range_perm_sound` (class #5b), plus
    `equiv_ADD`'s existing closure. Zero new axioms — matches
    `docs/fv/per-air-axiom-map.md`'s 0–1 prediction (at the lower
    bound). -/
theorem equiv_ADD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    -- AIR validators + row index. Compliance.lean shares (m, badd)
    -- across all BinaryAdd-shape opcodes (ADD, ADDI).
    (m : Valid_Main FGL FGL) (badd : ZiskFv.Compliance.BinaryAddWitness)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation / opcode pins. Compliance.lean derives these from
    -- the Main AIR's ROM handshake on the row hosting ADD.
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    -- Main-side constructibility bundle (per-row ADD-subset constraints).
    -- Compliance.lean delivers this from a universal
    -- `∀ r, add_universal_row m r` parameter.
    (h_main_subset : add_subset_holds m r_main)
    -- Lane-match for the rd-write entry — caller-supplied; discharged
    -- downstream from `memory_bus_register_write_perm_sound`.
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    -- Structural promise bundle (15 fields). Subsumes the prior inline
    -- `h_input_r1_sail`, `h_input_r2_sail`, `h_input_rd`, `h_input_pc`,
    -- `h_exec_len`, `h_e0_mult`, `h_e1_mult`, `h_nextPC_matches`,
    -- `h_m0_mult`, `h_m0_as`, `h_m1_mult`, `h_m1_as`, `h_m2_mult`,
    -- `h_m2_as`, `h_rd_idx` binders.
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨b, h_b_core⟩ := badd
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_add⟩ := pins
  -- ============ Derive `m.m32 r_main = 0` via `transpile_ADD` ============
  -- Fire `transpile_ADD` with arbitrary placeholders for the ghost
  -- `RV64State` / `Fin 32` parameters; we consume only `m32 = 0`
  -- (the other pins are internally used inside `add_discharge`).
  have h_tr := ZiskFv.Trusted.transpile_ADD
    m r_main ({ xreg := fun _ => 0#64, pc := 0#64 } : RV64State)
    (0 : Fin 32) (0 : Fin 32) h_main_active h_main_op_add
  obtain ⟨_, _, _, _, h_m32, _, _, _, _⟩ := h_tr
  -- ============ Derive `m.flag r_main = 0` via op-bus matches_entry ============
  -- `op_bus_perm_sound_BinaryAdd` gives an existential `r_b` with
  -- `matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryAdd b r_b)`;
  -- BinaryAdd's bus row pins `flag := 0` (binary_add.pil:25,
  -- `proves_operation` with implicit `flag = 0`), so the matches_entry
  -- flag-slot equality projects to `m.flag r_main = 0`.
  -- Note: `h_main_op_add : m.op r_main = OP_ADD` and `OP_ADD := (10 : FGL)`
  -- definitionally.
  obtain ⟨_r_b, h_match⟩ :=
    op_bus_perm_sound_BinaryAdd m b r_main h_main_active h_main_op_add
  have h_flag : m.flag r_main = 0 := by
    have := h_match
    simp only [matches_entry, opBus_row_Main, opBus_row_BinaryAdd] at this
    exact this.2.2.2.2.2.2.2.2.1
  -- ============ Assemble `main_row_in_add_mode` ============
  have h_main_mode : main_row_in_add_mode m r_main :=
    ⟨h_main_active, h_main_op_add, h_m32, h_flag⟩
  -- ============ Discharge the 8 e2 byte ranges ============
  -- `memory_bus_entry_byte_range_perm_sound` (class #5b) packages all
  -- 8 byte-range facts for a single memory-bus entry; we destructure.
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    memory_bus_entry_byte_range_perm_sound e2
  -- ============ Delegate to canonical `equiv_ADD` ============
  exact ZiskFv.EquivCore.Add.equiv_ADD
    state add_input r1 r2 rd m ⟨b, h_b_core⟩ r_main
    ⟨exec_row, e0, e1, e2⟩
    promises h_main_subset h_main_mode h_lane_rd
    ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩

end ZiskFv.Compliance
