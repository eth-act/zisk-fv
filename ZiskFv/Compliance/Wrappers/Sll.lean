import Mathlib

import ZiskFv.EquivCore.Sll
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.BinaryExtensionHelpers
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SLL` trust-discharge wrapper

Discharges the op-bus `matches_entry` handshake on top of the
canonical `equiv_SLL`. The canonical surface already internalizes
the BinaryExtension chunk/byte ranges, the op-is-shift pin, the
byte-lookup table witness, and the packed-a / shift-pin operand
bridges; what remains for the wrapper is to derive `h_match` from
`op_bus_perm_sound_BinaryExtension` (class #4) given the Main opcode
pin. The existential row index `r_e` from that axiom serves as
`r_binary`, eliminating two binders (`r_binary`, `h_match`) versus
the canonical signature.

Trust footprint: `op_bus_perm_sound_BinaryExtension` (class #4)
plus `equiv_SLL`'s existing closure. Zero new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


/-- **Trust-discharged wrapper for `equiv_SLL`.**

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
    plus `equiv_SLL`'s closure. The core SLL proof now derives the
    shift pin, `a`-byte ranges, `c`-lane ranges, and `c`-lane sum
    bounds from the exact Clean/static BinaryExtensionTable provider
    row, so its semantic closure no longer includes the generic
    retired range-bus axiom. The remaining opcode-specific trust is
    SLL row-shape contract (class #1). Zero new axioms. -/
lemma equiv_SLL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    -- AIR validators + row index. Compliance.lean shares (m, v)
    -- across all BinaryExtension-shape opcodes (twelve shifts).
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    -- Structural promise bundle (15 fields). Subsumes the prior inline
    -- Sail-side state predicates + bus-protocol structural hypotheses.
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Activation / opcode pins. Compliance.lean derives these from
    -- the Main AIR's ROM handshake on the row hosting SLL.
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : sll_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : sll_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    -- Lane-match for the rd-write entry — caller-supplied; discharged
    -- downstream from `memory_bus_register_write_perm_sound`.
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let row :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  exact ZiskFv.EquivCore.Sll.equiv_SLL_of_static_row state sll_input r1 r2 rd
    m row r_main bus promises pins h_match h_shift_facts.1
    (by simpa [row] using h_input_r1_row)
    (by simpa [row] using h_shift_pin_row)
    h_shift_facts.2 h_lane_rd

-- equiv_<OP>_of_static_lookup (alt route, op_bus_perm_sound) deleted in T4-purge P3.2.

end ZiskFv.Compliance
