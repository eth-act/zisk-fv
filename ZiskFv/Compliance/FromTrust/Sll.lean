import Mathlib

import ZiskFv.Equivalence.Sll
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension

/-!
# `equiv_SLL` trust-discharge wrapper
## Why SLL

SLL is the canonical exemplar for the BinaryExtension shape (which
covers SLL, SLLI, SRL, SRLI, SRA, SRAI, SLLW, SRLW, SRAW, SLLIW,
SRLIW, SRAIW — twelve shift opcodes — plus the internal
SEXT_B/SEXT_H/SEXT_W used by signed loads).

* Un-cascaded — SLL only consumes `BinaryExtension`; no downstream
  AIR chain. (The signed loads LB/LH/LW do feed the SEXT outputs
  into the load result and so cascade through `SextLoadBridge.lean`;
  the shift opcodes do not.)
* No sign extension — SLL is left-shift. The sign-witness pin
  category (3) is N/A for SLL specifically. SRA / SRAI / SRAW /
  SRAIW (signed-shift) would consume a sign-witness pin that this
  exemplar's wrapper does not need.
* Single-mode — 64-bit shift (`m32 = 0`). The W variants (SLLW,
  SRLW, SRAW, SLLIW, SRLIW, SRAIW) flip to `m32 = 1` but the same
  bridge infrastructure (`Bridge/BinaryExtension.lean::shift_pin_w_eq_of_shift_match`)
  handles it.

The canonical `equiv_SLL` already internalizes the heavy lifting
this AIR's shape would otherwise expose to the wrapper:

* The 8 per-byte rd-write entry ranges (`h_e2_0..h_e2_7`) — derived
  inside `equiv_SLL` from `memory_bus_entry_byte_range_perm_sound`
  (class #5b).
* The 17 BinaryExtension chunk ranges (`h_a_range`, `hc_0..hc_15`) —
  derived inside `equiv_SLL` from `binary_extension_columns_in_range`
  (class #6).
* The c-lane sum bounds (`hc_lo_sum_lt` / `hc_hi_sum_lt`) — derived
  inside `equiv_SLL` from `hc_{lo,hi}_sum_lt_of_match` (pure-Lean
  bridge consuming `main_columns_in_range` and
  `binary_extension_columns_in_range`).
* The op-is-shift pin (`op_is_shift = 1`) — derived inside
  `equiv_SLL` from `binary_extension_op_is_shift_pin` (class #6).
* The 8-byte BinaryExtensionTable witness (`h_bytes`) — from
  `binary_extension_row_byte_lookups` (class #6).
* The packed-a / shift-pin operand bridges — derived inside
  `equiv_SLL` from `Bridge/BinaryExtension.lean::packed_a_eq_of_shift_match_m32_0`
  + `shift_pin_eq_of_shift_match_m32_0` (pure-Lean, consuming
  `transpile_SLL` (class #1) + `h_match`).

What remains for the wrapper to discharge is the **op-bus
matches_entry handshake** (`h_match`) — currently a caller-supplied
witness on the canonical surface, but derivable from the trust-ledger
axiom `op_bus_perm_sound_BinaryExtension` (class #4) given the Main
opcode pin. This eliminates two binders (`r_binary` and `h_match`)
because the existential `r_e : ℕ` produced by the op-bus axiom
serves as the `r_binary` row index, freeing the caller from supplying
either.

## 5-category discharge applied

* **Lane-match.** Internalized by `equiv_SLL` via
  `project_match_op_clo_chi` + `hc_{lo,hi}_sum_lt_of_match` (consume
  `op_bus_perm_sound_BinaryExtension` (class #4) through `h_match`).
  Pre-discharged on the canonical surface.
* **Mode pins.** Internalized by `equiv_SLL` via
  `binary_extension_op_is_shift_pin` (class #6). The Main-side
  `m32 = 0` pin comes from `transpile_SLL` (class #1) — already
  consumed inside `equiv_SLL` via the Bridge helpers.
* **Sign-witness pins.** N/A — SLL is left-shift, no sign extension.
  (The signed-load family LB/LH/LW reuses this AIR via SEXT_B/H/W
  and DOES need a sign-witness pin; this is separate from SLL
  specifically. See per-AIR axiom map's "Predicted gaps" section.)
* **Range/bound.** Internalized by `equiv_SLL` via
  `binary_extension_columns_in_range` (class #6) and
  `memory_bus_entry_byte_range_perm_sound` (class #5b).
  Pre-discharged on the canonical surface.
* **Operand bridges.** Internalized by `equiv_SLL` via the
  `packed_a_eq_of_shift_match_m32_0` + `shift_pin_eq_of_shift_match_m32_0`
  bridges in `Bridge/BinaryExtension.lean` (pure-Lean, consume
  `transpile_SLL` (class #1) + `h_input_r{1,2}_sail`). Pre-discharged
  on the canonical surface.

The remaining wrapper-level discharge target is the op-bus handshake
itself (`h_match`), discharged via `op_bus_perm_sound_BinaryExtension`.

## Anti-laundering report

Per the discharge-recipe.md wrapper-specific checks:

* **No new axioms.** This wrapper consumes only existing trust-ledger
  axioms: `op_bus_perm_sound_BinaryExtension` (class #4) plus
  `equiv_SLL`'s existing closure. Trust ledger unchanged — UNDER the
  per-AIR axiom map's 1–2 prediction. The prediction's "new axioms"
  budget anticipated SRA-family sign-witness pins (Category 3) which
  are N/A for SLL specifically.
* **Bridges cross-shape if possible.** No helpers added — the
  op-bus discharge is a 3-line application of
  `op_bus_perm_sound_BinaryExtension`. (If a future shape's wrapper
  needs the same one-line projection pattern it can be lifted into
  `Airs/OperationBus/Bridge.lean` then.)
* **Caller-burden shrinks.** See the count below.

## Caller-burden

`equiv_SLL` (canonical): 32 binders / 19 hypotheses.
`equiv_SLL_from_trust` (this file): 30 binders / 18 hypotheses.

Net −2 binders / −1 hypothesis per BinaryExtension-shape opcode.
Composition:

* Drops `r_binary` (1 binder, [row]): the existential `r_e` returned
  by `op_bus_perm_sound_BinaryExtension` serves the role.
* Drops `h_match` (1 binder, [other]): the `matches_entry` witness
  is now derived inside the wrapper from
  `op_bus_perm_sound_BinaryExtension m v r_main h_main_active <op-disj>`.

The headline drop count is smaller than ADD's (−7) because the
BinaryExtension canonical surface `equiv_SLL` had already internalized
the 17 chunk-range and 8 byte-range bulk discharges in the PR #19
era. The remaining surface-level promise hypotheses on this shape's
canonical theorems are all bus-protocol structural (the 8 [bus_shape]
binders, the `h_lane_rd` register-write lane match, the Sail-side
SPEC-PRE preconditions) — exactly the residue every shape's wrapper
keeps caller-supplied pending the Mem-pilot + Compliance.lean
pipeline.

At the global Compliance.lean level the reduction extends further
because:
* `(m, v, r_binary)` collapse into shared parameters across all
  twelve shift opcodes (single AIR per shape).
* `h_main_active` / `h_main_op` come from Compliance.lean's
  program-counter handshake — shared across all opcodes.
* `h_lane_rd` will be discharged from
  `memory_bus_register_write_perm_sound` once the Mem-side AIR data
  is plumbed through Compliance.lean.

## Cross-shape lessons

* The **op-bus handshake discharge pattern** — apply
  `op_bus_perm_sound_<Provider>` with the Main opcode pin to obtain
  `∃ r_provider, matches_entry ...`, destructure into `r_provider` +
  `h_match`, delegate — is **reusable across every provider-AIR
  shape** (Binary, BinaryExtension, BinaryAdd, ArithMul, ArithDiv,
  Mem). Each provider axiom has its own opcode disjunction; the
  pattern is otherwise identical.
* The BinaryExtension shape was the **cleanest demonstration** of
  this pattern because the canonical `equiv_SLL` already exposes
  `h_match` directly (without further unpacking into `h_match_clo`
  / `h_match_chi` — those are derived inside via
  `project_match_op_clo_chi`). For shapes where the canonical
  theorem still exposes the projected lane-match equations
  separately (e.g. some Binary variants), the wrapper does the
  projection at the wrapper level instead.
* **No new bridge added** to `Equivalence/Bridge/SailStateBridge.lean`
  or `Equivalence/Bridge/BinaryExtension.lean`. The existing
  infrastructure is sufficient for SLL's discharge.
* The discharge generalizes mechanically to the eleven other shift
  opcodes (SLLI, SRL, SRLI, SRA, SRAI, SLLW, SRLW, SRAW, SLLIW,
  SRLIW, SRAIW). The differences are:
  - Opcode disjunction member in the `op_bus_perm_sound_BinaryExtension`
    application (each is one of 0x21..0x26).
  - SRA/SRAI/SRAW/SRAIW additionally consume a sign-witness pin
    (Category 3) — predicted as the 1–2 new axiom in the per-AIR
    map; orthogonal to this exemplar's pattern.
  - SLLI/SRLI/SRAI use the immediate-shift bridge variants
    (`shift_pin_immediate_eq_of_shift_match`) — also already in
    `Bridge/BinaryExtension.lean`.
  - SLLW/SRLW/SRAW/SLLIW/SRLIW/SRAIW use the W-variant bridges
    (`packed_a_lo32_eq_of_shift_match_m32_1`, `shift_pin_w_eq_of_shift_match`)
    — also already in `Bridge/BinaryExtension.lean`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Pilot wrapper for `equiv_SLL`.**

    Caller obligations (signature header, ordered):
    1. The Sail-side inputs (`state`, `sll_input`, `r1`, `r2`, `rd`).
    2. The two AIR validators with the selected Main row index
       (`m : Valid_Main`, `v : Valid_BinaryExtension`, `r_main : ℕ`).
       Compliance.lean shares `(m, v)` across every BinaryExtension-shape
       opcode (all twelve shifts plus the three internal SEXTs).
    3. The structural bus rows (`exec_row`, `e0`, `e1`, `e2`).
    4. The activation + opcode pins on Main (`h_main_active`,
       `h_main_op`). Both come from Compliance.lean's program-counter
       handshake on the row hosting the SLL instruction.
    5. The lane-match for the rd-write entry (`h_lane_rd`) —
       caller-supplied; discharged downstream from
       `memory_bus_register_write_perm_sound`.
    6. The Sail-side state predicates (SPEC-PRE):
       `h_input_r1_sail`, `h_input_r2_sail`, `h_input_rd`, `h_input_pc`.
    7. The bus-protocol structural hypotheses — pass-through from
       `equiv_SLL`; Compliance.lean supplies these from the same
       bus-shape obligations as every other opcode in the shape.

    Derived internally (NOT caller-supplied):
    * `r_binary : ℕ` — existential witness from
      `op_bus_perm_sound_BinaryExtension`.
    * `h_match : matches_entry (opBus_row_Main m r_main)
        (opBus_row_BinaryExtension v r_binary)` — derived from
      `op_bus_perm_sound_BinaryExtension m v r_main h_main_active`
      with the op-disjunction satisfied via `Or.inl h_main_op`.

    Trust footprint: `op_bus_perm_sound_BinaryExtension` (class #4)
    plus `equiv_SLL`'s existing closure (which transitively consumes
    `transpile_SLL` (class #1), `binary_extension_columns_in_range`
    (class #6), `binary_extension_op_is_shift_pin` (class #6),
    `binary_extension_row_byte_lookups` (class #6),
    `memory_bus_entry_byte_range_perm_sound` (class #5b),
    `main_columns_in_range` (class #5b)). Zero new axioms — UNDER
    `docs/fv/per-air-axiom-map.md`'s 1–2 prediction (SRA-family
    sign-witness pin is N/A for SLL specifically). -/
theorem equiv_SLL_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    -- AIR validators + row index. Compliance.lean shares (m, v)
    -- across all BinaryExtension-shape opcodes (twelve shifts).
    (m : Valid_Main C FGL FGL)
    (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Sail-side state predicates (SPEC-PRE).
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sll_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sll_input.r2_val state)
    (h_input_rd : sll_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sll_input.PC)
    -- Bus-protocol structural hypotheses — pass-through from `equiv_SLL`.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sll_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Activation / opcode pins. Compliance.lean derives these from
    -- the Main AIR's ROM handshake on the row hosting SLL.
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL)
    -- Lane-match for the rd-write entry — caller-supplied; discharged
    -- downstream from `memory_bus_register_write_perm_sound`.
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- ============ Derive (r_binary, h_match) via op-bus permutation soundness ============
  -- `op_bus_perm_sound_BinaryExtension` takes the Main activation +
  -- opcode-disjunction pins (covering SLL=0x21 through SEXT_W=0x29).
  -- For SLL specifically the disjunction member is `m.op r_main = 0x21`,
  -- which `h_main_op : m.op r_main = OP_SLL` supplies — `OP_SLL := 33 = 0x21`
  -- definitionally per `Fundamentals/Transpiler.lean:162` (and
  -- `BinaryExtensionTable.OP_SLL := 0x21` per `Airs/BinaryExtensionTable.lean:36`).
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryExtension m v r_main h_main_active
      (Or.inl h_main_op)
  -- ============ Delegate to canonical `equiv_SLL` ============
  exact ZiskFv.Equivalence.Sll.equiv_SLL state sll_input r1 r2 rd
    m v r_main r_binary exec_row e0 e1 e2
    { input_r1_eq := h_input_r1_sail
      input_r2_eq := h_input_r2_sail
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := h_m0_mult
      m0_as := h_m0_as
      m1_mult := h_m1_mult
      m1_as := h_m1_as
      m2_mult := h_m2_mult
      m2_as := h_m2_as
      rd_idx := h_rd_idx }
    h_main_active h_main_op h_match h_lane_rd

end ZiskFv.Compliance
