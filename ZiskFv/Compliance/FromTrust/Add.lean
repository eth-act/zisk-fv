import Mathlib

import ZiskFv.Equivalence.Add
import ZiskFv.Equivalence.Promises.RType
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.EntryRanges

/-!
# `equiv_ADD` trust-discharge wrapper
## Why ADD

ADD is the canonical exemplar for the BinaryAdd shape (which covers
ADD and ADDI). Per `docs/fv/per-air-axiom-map.md` it has the smallest
predicted axiom delta (0–1) of the six remaining provider-AIR shapes:

* No mode columns on the provider AIR (`m32` lives on Main only;
  BinaryAdd is single-mode). Category 2 N/A on the provider side.
* No signed-vs-unsigned distinction. Category 3 N/A.
* Range/bound discharged via `binary_add_columns_in_range` (already
  on the trust ledger), internalized by `equiv_ADD` through
  `Bridge/BinaryAdd.lean::add_discharge`.
* Lane-match (category 1) is internalized by `equiv_ADD` via
  `add_discharge` consuming `op_bus_perm_sound_BinaryAdd`
  (class #4) + `binary_add_columns_in_range` (class #5b).
* Operand bridges (category 5) are internalized by `equiv_ADD` via
  `Bridge/SailStateBridge.lean::add_input_bridges_of_read_xreg`
  (pure Lean, no axiom).

The remaining wrapper-level discharge targets on `equiv_ADD` are
not promise hypotheses on Sail outputs but **structural-unpacking
bundles** plus **byte-range obligations**:

1. `h_main_mode : main_row_in_add_mode m r_main` — a 4-field bundle
   (`is_external_op = 1`, `op = OP_ADD`, `m32 = 0`, `flag = 0`).
2. `h_e2_0..h_e2_7` — 8 byte-range hypotheses (`.val < 256`) on
   the rd-write memory-bus entry `e2`.

## 5-category discharge applied

* **Lane-match.** Internalized by `equiv_ADD` via `add_discharge`
  (consumes `op_bus_perm_sound_BinaryAdd`, class #4). Pre-discharged
  on the canonical surface.
* **Mode pins.** Provider AIR has no mode columns (N/A). Main-side
  mode pins are split:
  * `m32 = 0` — derived from `transpile_ADD` (class #1) applied to
    `h_main_active + h_main_op_add`.
  * `flag = 0` — derived from `op_bus_perm_sound_BinaryAdd`
    (class #4) projected through `matches_entry`'s `.flag` slot,
    which is `0` by the BinaryAdd provider emission
    (`binary_add.pil:25`, `proves_operation(op: OP_ADD, ...)` with
    implicit `flag = 0`).
* **Sign-witness pins.** N/A — ADD is unsigned addition.
* **Range/bound.** Two parts:
  * BinaryAdd chunk ranges — internalized by `equiv_ADD` via
    `add_discharge` (consumes `binary_add_columns_in_range`,
    class #5b).
  * Memory-bus entry byte ranges — derived from
    `memory_bus_entry_byte_range_perm_sound` (class #5b). The
    wrapper unpacks the 8-conjunction into 8 individual hypotheses
    needed by `equiv_ADD`.
* **Operand bridges.** Internalized by `equiv_ADD` via
  `add_discharge` (consumes `add_input_bridges_of_read_xreg` — pure
  Lean). Pre-discharged on the canonical surface.

## Anti-laundering report

Per the discharge-recipe.md wrapper-specific checks:

* **No new axioms.** This wrapper consumes only existing trust-ledger
  axioms: `transpile_ADD` (class #1), `op_bus_perm_sound_BinaryAdd`
  (class #4), `memory_bus_entry_byte_range_perm_sound` (class #5b),
  plus `equiv_ADD`'s existing closure. Trust ledger unchanged at
  116 axioms — matches the per-AIR axiom map's 0-new-axioms prediction
  for BinaryAdd (lower bound of the 0–1 range).
* **Bridges cross-shape if possible.** No helpers added — the
  `flag = 0` projection from `matches_entry` is a one-liner that
  does not warrant a generic bridge. (If a future shape's wrapper
  needs the same projection it can be lifted into
  `Airs/OperationBus/Bridge.lean` then.)
* **Caller-burden shrinks.** See the count below.

## Caller-burden

`equiv_ADD` (canonical): 41 binders / 27 hypotheses.
`equiv_ADD_from_trust` (this file): 34 binders / 20 hypotheses.

Net −7 binders / −7 hypotheses per BinaryAdd-shape opcode. Composition:

* Drops `h_main_mode` (1 binder): the 4-field bundle is reassembled
  inside the wrapper from `h_main_active` + `h_main_op_add` (added,
  +2 binders) plus the derived `m32 = 0` (transpile) and `flag = 0`
  (op-bus matches_entry projection).
* Drops `h_e2_0..h_e2_7` (8 binders): the 8 byte-range obligations
  are discharged uniformly via
  `memory_bus_entry_byte_range_perm_sound e2`.

Net: −1 − 8 + 2 = −7 binders. Hypothesis count drops symmetrically
because all removed binders were hypotheses.

This matches the discharge-recipe.md "caller-burden must shrink"
discipline. At the global `Compliance.lean` level the reduction
extends further because `(m, b, ∀ r, core_every_row b r)` collapse
into shared parameters across ADD + ADDI, and `h_main_active` /
`h_main_op_add` come from Compliance.lean's program-counter handshake.

## Cross-shape lessons

* The **`flag = 0` projection from `matches_entry`** is a one-liner
  reusable for every BinaryAdd-shape opcode (currently just ADD and
  ADDI). For other provider AIRs the `flag` slot may carry an output
  (e.g. Binary's `cout` for ADD/SUB, comparison verdicts for SLT*),
  so this projection is BinaryAdd-shape-specific and stays in this
  exemplar file.
* The **byte-range bulk discharge** via
  `memory_bus_entry_byte_range_perm_sound` works for any opcode with
  a memory-bus rd-write entry — i.e. every opcode where the
  `equiv_<OP>` signature has 8 `h_e2_*` hypotheses. This includes
  the entire BinaryAdd shape (ADD, ADDI), most Binary shape ops
  (AND, OR, XOR, etc.), most Arith ops, and the rd-writing
  ControlFlow ops (LUI, AUIPC, JAL, JALR). LUI's wrapper does not
  use it because `equiv_LUI`'s signature already internalized the
  byte-range discharge in PR #19's earlier work; the ADD signature
  retains the 8 `h_e2_*` parameters and so benefits more from this
  discharge.
* **No new bridge added** to `Equivalence/Bridge/SailStateBridge.lean`
  or `Equivalence/Bridge/BinaryAdd.lean`. The existing `add_discharge`
  bridge is already what `equiv_ADD` consumes; no shape-level gap
  was surfaced by this exemplar.
* The discharge generalizes mechanically to ADDI: swap `transpile_ADD`
  for `transpile_ADDI`, swap `OP_ADD = 10` for whatever ADDI's
  op-literal projection is (still 10 — ADDI piggybacks on OP_ADD per
  `Transpiler.lean:1898`'s docstring), and reuse the same matches_entry
  flag projection.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.Add

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Pilot wrapper for `equiv_ADD`.**

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
theorem equiv_ADD_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    -- AIR validators + row index. Compliance.lean shares (m, b)
    -- across all BinaryAdd-shape opcodes (ADD, ADDI).
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Activation / opcode pins. Compliance.lean derives these from
    -- the Main AIR's ROM handshake on the row hosting ADD.
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_add : m.op r_main = OP_ADD)
    -- Main-side constructibility bundle (per-row ADD-subset constraints).
    -- Compliance.lean delivers this from a universal
    -- `∀ r, add_universal_row m r` parameter.
    (h_main_subset : add_subset_holds m r_main)
    -- BinaryAdd-side universal-per-row validity.
    (h_b_core : ∀ r, ZiskFv.Airs.BinaryAdd.core_every_row b r)
    -- Lane-match for the rd-write entry — caller-supplied; discharged
    -- downstream from `memory_bus_register_write_perm_sound`.
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    -- Structural promise bundle (15 fields). Subsumes the prior inline
    -- `h_input_r1_sail`, `h_input_r2_sail`, `h_input_rd`, `h_input_pc`,
    -- `h_exec_len`, `h_e0_mult`, `h_e1_mult`, `h_nextPC_matches`,
    -- `h_m0_mult`, `h_m0_as`, `h_m1_mult`, `h_m1_as`, `h_m2_mult`,
    -- `h_m2_as`, `h_rd_idx` binders.
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd exec_row e0 e1 e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
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
  exact ZiskFv.Equivalence.Add.equiv_ADD
    state add_input r1 r2 rd m b r_main exec_row e0 e1 e2
    promises h_main_subset h_main_mode h_b_core h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7

end ZiskFv.Compliance
