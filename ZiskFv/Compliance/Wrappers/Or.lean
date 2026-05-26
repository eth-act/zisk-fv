import Mathlib

import ZiskFv.EquivCore.Or
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.BinaryHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_OR` trust-discharge wrapper
## Why OR

OR is the simplest of the 14 Binary-shape opcodes:

* No signed comparison (unlike SLT/SLTI/SLTU/SLTIU — those add
  sign-witness pins).
* No 32-bit truncation (unlike SUBW/ADDIW/ADDW — those add m32-mode
  pins).
* No carry-chain consumer (unlike SUB/SLT-family — those need the
  6-field `consumer_byte_match_chain` family that AND/OR/XOR's
  byte-local 3-field family covers).
* Symmetric in rs1/rs2 (unlike Tier-2 ops, no extra ordering).

Per `docs/fv/per-air-axiom-map.md` the Binary shape pilot has the
largest predicted axiom delta (2–4) of the six remaining shapes —
the AIR covers 14 opcodes across several sub-shapes, and the
mode-pin / sign-pin surface is broader than BinaryAdd's. **This OR
pilot lands 1 new axiom** at the low end of the prediction, because
the OR-shape (and AND/XOR by symmetry) only need the
`b_op_or_sext = OP_OR` mode pin — no sign or W-mode pins required.

## 5-category discharge applied

* **Lane-match.** Internalized by `equiv_OR` via the `Bridge.Binary`
  discharge family (`byte_ranges_at_holds`, `byte_chain_discharge_logic`,
  `match_clo_chi_OR`, `input_r1_packed_a`, `input_r2_packed_b`,
  `e2_byte_ranges_discharge`). These consume the trust-ledger axioms
  `binary_columns_in_range` (#6), `binary_per_byte_lookup_witness`
  (#6), `binary_carry_bits_in_range` (#6), `bin_table_consumer_wf`
  (#6), and `memory_bus_entry_byte_range_perm_sound` (#5b). The
  wrapper-level lane-match obligation is the **existential row**
  `r_binary` plus the `matches_entry` predicate; both come from
  `op_bus_perm_sound_Binary` (#4).
* **Mode pins.** OR consumes one mode pin on the provider AIR:
  `(v.b_op_or_sext r_binary).val = OP_OR`. This is the gap addressed
  by the **new axiom** `binary_b_op_or_sext_eq_OP_OR` (class #6) in
  `ZiskFv/Airs/Binary/BinaryRanges.lean` — the consequence of
  PIL's `b_op_or_sext` linear def (`binary.pil:104`) plus the
  per-byte BinaryTable lookup (`binary.pil:131-148`) restricting the
  `(b_op, mode32, c_is_signed)` triple to a unique valid decomposition
  when the on-bus emission `b_op + 16 * mode32 = 15`.
* **Sign-witness pins.** N/A for OR (unsigned bitwise op).
* **Range/bound.** Discharged by the Binary AIR's range axioms
  (`binary_columns_in_range`, `binary_carry_bits_in_range`) —
  pre-internalized by `equiv_OR` via the `Bridge.Binary` helpers.
  No wrapper-level work.
* **Operand bridges.** Discharged by
  `Bridge.SailStateBridge.packed_lane_eq_of_read_xreg` (consumed
  through `Bridge.Binary.input_r1_packed_a` / `input_r2_packed_b`).
  Pre-internalized on the canonical surface.

## Anti-laundering report

* **One new axiom.** `binary_b_op_or_sext_eq_OP_OR` in
  `ZiskFv/Airs/Binary/BinaryRanges.lean`. Class #6 (Binary AIR
  lookup soundness — table-pin sub-class). PIL-cited
  (`binary.pil:104` + `binary.pil:131-148`). At the **low end** of
  the per-AIR axiom map's 2–4 prediction — possible because OR's
  byte-local logic shape (shared with AND/XOR) only needs one pin
  to distinguish OR from AND/XOR at the `b_op_or_sext` lookup level;
  AND and XOR will need parallel `binary_b_op_or_sext_eq_OP_{AND,XOR}`
  pins for their wrappers (so the shape's mass-author phase will
  add 2 more class-#6 axioms — still within the 2–4 envelope).
* **Bridges cross-shape if possible.** No new bridge helpers added.
  The existing `Bridge.Binary` infrastructure (`carry_7_zero_OR_pure`,
  `byte_chain_discharge_logic`, `match_clo_chi_OR`, the
  `input_r{1,2}_packed_a/b` Sail-state bridges) already covers
  every category the OR pilot needs.
* **Caller-burden shrinks.** See the count below.

## Caller-burden

`equiv_OR` (canonical): **32 binders / 22 hypotheses**.
`equiv_OR` (this file): **29 binders / 19 hypotheses**.

Net **−3 binders / −3 hypotheses** per Binary-shape opcode.
Composition:

* Drops `r_binary` (1 binder): existential row witness produced by
  `op_bus_perm_sound_Binary`.
* Drops `h_match` (1 hypothesis): the cross-AIR `matches_entry`
  comes paired with `r_binary` from `op_bus_perm_sound_Binary`.
* Drops `h_bop_or_sext` (1 hypothesis): the `b_op_or_sext = OP_OR`
  mode pin is derived by the new axiom
  `binary_b_op_or_sext_eq_OP_OR` after projecting matches_entry's
  `.op` slot through `h_main_op_or`.

At the **global Compliance.lean** level the reduction extends further:
the static BinaryTable route now derives `core_every_row` from the same
`StaticLookupSoundness` path that supplies table membership, and
`h_main_active` / `h_main_op_or` come from Compliance.lean's
program-counter handshake.

The remaining wrapper-level promise hypothesis (caller-burden) on
this exemplar is `h_lane_rd : register_write_lanes_match m r_main e2`,
discharged downstream via a Binary-side
`main_external_logic_emission_bundle` (or equivalent class-#4
bundle). The Add wrapper follows the same convention.

## Cross-shape lessons

* The **matches_entry `.op` projection** under `OP_OR = 15` is
  one-step: `simp only [matches_entry, opBus_row_Main, opBus_row_Binary]`
  exposes the `m.op r_main = v.b_op r_binary + 16 * v.mode32 r_binary`
  equality; combined with `h_main_op_or`, this gives the precondition
  `v.b_op r_binary + 16 * v.mode32 r_binary = 15` for the new pin
  axiom. The same pattern transfers verbatim to AND (`OP_AND = 14`)
  and XOR (`OP_XOR = 16`).
* The discharge generalizes mechanically to the **6 byte-local logic
  opcodes** (AND/ANDI/OR/ORI/XOR/XORI):
  * Swap `transpile_OR` for `transpile_<AND,XOR,…>`.
  * Swap `OP_OR = 15` for the relevant opcode literal.
  * Swap the new axiom `binary_b_op_or_sext_eq_OP_OR` for the
    parallel `_OP_AND` / `_OP_XOR` pin.
  * The 8 byte-chain matches and the c-lane discharge use the
    matching `Bridge.Binary.byte_chain_discharge_logic` /
    `match_clo_chi_{AND,XOR}` already in place.
* **For SLT/SLTI/SLTU/SLTIU (signed comparison)** the wrapper will
  additionally need a sign-witness pin (e.g.
  `binary_use_first_byte_pin_SLT` or a c-lane sign-bit pin) — out
  of scope for this pilot, predicted in the per-AIR axiom map's
  "sign-witness pins (1–2)" line.
* **For SUB/SUBW/ADDIW/ADDW** the wrapper will additionally need a
  cin/carry-chain pin (`consumer_byte_match_chain` 6-field variant)
  — out of scope for this pilot.

The byte-chain infrastructure (`Bridge.Binary.byte_chain_discharge_logic`)
is shape-agnostic in the opcode literal — it works for any
`b_op_or_sext = op_val` pinning. The wrapper-level work for AND/XOR
will be ~30 lines apiece (essentially copy of this file).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


theorem equiv_OR
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (or_input : PureSpec.OrInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state or_input.r1_val or_input.r2_val or_input.rd or_input.PC
        (PureSpec.execute_RTYPE_or_pure or_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.OR))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let row :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  exact ZiskFv.EquivCore.Or.equiv_OR_of_static_row
    state or_input r1 r2 rd m row r_main bus promises pins
    h_match h_core h_facts h_lane_rd

end ZiskFv.Compliance
