import Mathlib

import ZiskFv.EquivCore.Or
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
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

The historical OR pilot originally exposed the Binary shape before the
Clean/static Binary route existed. The live wrapper now consumes the shared
Clean Binary balance and exact table facts; the old Binary trust file has
been retired.

## 5-category discharge applied

* **Lane-match.** Internalized by the Clean/static Binary provider route.
  The retired multiplicity-based BinaryTable path and `bin_table_consumer_wf`
  no longer appear in the canonical closure.
* **Mode pins.** OR's `b_op_or_sext = OP_OR` fact is derived through
  the Clean/static Binary provider path and exact BinaryTable lookup facts.
* **Sign-witness pins.** N/A for OR (unsigned bitwise op).
* **Range/bound.** Discharged by the Clean/static Binary route and
  `Bridge.Binary` helpers. No wrapper-level work.
* **Operand bridges.** Discharged by
  `Bridge.SailStateBridge.packed_lane_eq_of_read_xreg` (consumed
  through `Bridge.Binary.input_r1_packed_a` / `input_r2_packed_b`).
  Pre-internalized on the canonical surface.

## Anti-laundering report

* **No new axiom.** The former Binary table-pin path is gone from the live
  trust ledger; this wrapper relies on the shared Clean/static Binary route.
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


lemma equiv_OR
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
    (h_input_r1_row : or_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : or_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
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
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  obtain ⟨h_row_spec, h_static_specs⟩ := h_component_spec
  exact ZiskFv.EquivCore.Or.equiv_OR_of_static_row
    state or_input r1 r2 rd m row r_main bus promises pins
    h_match h_row_spec h_core h_static_specs h_facts
    (by simpa [row] using h_input_r1_row)
    (by simpa [row] using h_input_r2_row)
    h_lane_rd

end ZiskFv.Compliance
