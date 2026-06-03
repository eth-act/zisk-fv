import Mathlib

import ZiskFv.EquivCore.Andi
import ZiskFv.EquivCore.Promises.IType
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_ANDI` Compliance wrapper — Binary ITYPE shape

> **Status:** round 3.I (ITYPE constructibility bundles).
> Mirrors `Wrappers/And.lean` (RTYPE AND, Binary provider) with the
> ITYPE-specific immediate-routing addition (`h_andi_subset`).
>
> Lives outside the canonical surface (under
> `Compliance/Wrappers/`) so V1 anti-laundering metrics on the
> canonical theorem are unaffected.

## Why ANDI

ANDI is the Binary-provider ITYPE companion to AND: the same Binary
state-machine handles both, distinguished only by the transpiler's
`b`-lane routing — AND reads `xreg(rs2)` onto Main's b-lanes; ANDI
routes the sign-extended 12-bit immediate. The Sail-level immediate
must therefore appear in the canonical equiv as a structural pin
(`itype_imm_subset_holds_main`) since `transpile_ANDI` leaves
`imm_b_lo`/`imm_b_hi` caller-routed.

## 5-category discharge applied

* **Lane-match.** Internalized by `equiv_ANDI` via the new
  `Bridge.Binary.itype_imm_subset_binary_row_of_main` (Main-form to
  8-byte Binary-row form) plus the existing `input_r1_packed_a` and
  `match_clo_chi_AND` bridges. The wrapper-level lane-match
  obligation on `e2` is caller-supplied (`h_lane_rd`).
* **Mode pins.** Provider AIR (`Valid_Binary`) `b_op_or_sext = OP_AND`
  mode pin derived from `binary_b_op_or_sext_eq_OP_AND` (class #6).
  Existential row witness `r_binary` + `matches_entry` from
  `op_bus_perm_sound_Binary` (class #4).
* **Sign-witness pins.** N/A (logical op).
* **Range/bound.** Discharged by `binary_columns_in_range` (class
  #6) + `memory_bus_entry_byte_range_perm_sound` (class #5b) —
  internalized by `equiv_ANDI`.
* **Operand bridges.** `h_input_r1_circuit` and `h_input_imm_circuit`
  internalized by `equiv_ANDI` via `transpile_ANDI` (class #1) +
  the two Binary bridges. The Main-form immediate pin
  (`h_andi_subset`) is the structural-unpacking parameter — passed
  through from caller.

## Anti-laundering report

* **No new axioms.** Consumes only `transpile_ANDI` (class #1),
  `op_bus_perm_sound_Binary` (class #4),
  `binary_b_op_or_sext_eq_OP_AND` (class #6),
  `memory_bus_entry_byte_range_perm_sound` (class #5b), plus
  `equiv_ANDI`'s existing closure.
* **Caller-burden shrinks.** Wrapper drops `r_binary`, `h_match`,
  `h_bop_or_sext` (3 caller binders) — derived internally. Net
  -3 binders vs. the refactored canonical surface, mirroring
  AndExemplar's reduction.
* **Constructibility bundle.** `h_andi_subset` is a per-row pin
  delivered by `Compliance.lean` from a program-level universal —
  not a new caller-supplied promise hypothesis.

## Cross-shape lessons

Pattern transfers verbatim to ORI/XORI (Binary-provider ITYPE
variants) — swap opcode literal, transpile axiom, and
`binary_b_op_or_sext_eq_OP_*` mode-pin axiom.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.EquivCore.Promises


lemma equiv_ANDI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (andi_input : PureSpec.AndiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_AND)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : andi_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 andi_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_andi_subset : itype_imm_subset_holds_main m r_main andi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state andi_input.r1_val andi_input.imm andi_input.rd andi_input.PC
        (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
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
  exact ZiskFv.EquivCore.Andi.equiv_ANDI_of_static_row
    state andi_input r1 rd imm m row r_main bus promises pins
    h_match h_row_spec h_core h_static_specs h_facts
    (by simpa [row] using h_input_r1_row)
    (by simpa [row] using h_input_imm_row)
    h_lane_rd h_andi_subset

end ZiskFv.Compliance
