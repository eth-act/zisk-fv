import Mathlib

import ZiskFv.Equivalence_v1.Lw
import ZiskFv.Equivalence_v1.Promises.Load
import ZiskFv.Equivalence_v1.Promises.BinaryExtensionHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.Tables.BinaryExtensionTable
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_LW` Compliance wrapper — signed-load BinExt SEXT_W chain

> **Status:** First of three signed-load wrappers (LW / LH / LB).
> Lives outside the canonical surface so V1 anti-laundering metrics
> on the canonical theorem are unaffected.

## 5-category discharge applied

* **Lane-match.** Pre-discharged on the canonical surface via
  `Bridge.Mem.lw_discharge_full` (Mem-side, `main_sext_load_emission_bundle`
  class #4) plus `SextLoadBridge.load_word_c_packed` (BinExt-side
  c-lane packing). The wrapper additionally discharges the four
  BinExt input lane-match equations `h_a0..3_match` via
  `Bridge.BinaryExtension.sext_lane_match_bytes_eq_of_match` —
  derived from the same Mem bundle's b-side equation plus
  `op_is_shift = 0` (from `binary_extension_op_is_shift_pin`,
  class #6) and the op-bus handshake (class #4).
* **Mode pins.** `op_is_shift = 0` derived inside the wrapper via
  `binary_extension_op_is_shift_pin` (class #6) on the SEXT_W
  branch.
* **Sign-witness pins.** N/A — the sign-extension equation is itself
  pre-discharged on the canonical surface via the
  `SextLoadBridge.load_word_c_packed` chain (consuming
  `bin_ext_table_consumer_wf` class #6 +
  `binary_extension_sext_w_chunks_eq_signextend_nat` class #6).
* **Range/bound.** Pre-discharged via
  `binary_extension_columns_in_range` (class #6) for the c-lane
  sum bounds (via `hc_{lo,hi}_sum_lt_of_match`) plus
  `memory_bus_entry_byte_range_perm_sound` (class #5b) for the
  e1/e2 byte ranges.
* **Operand bridges.** The Sail address bridge is consumed via
  `lw_state_assumptions` (SPEC-PRE).

## Anti-laundering report

* **Zero new axioms** — consumes only existing trust-ledger axioms.
  Matches Family B's prediction.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus
open ZiskFv.Equivalence_v1.Promises

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_LW`.** Replaces the eight
    BinExt-side promise hypotheses (`h_op_binary`, `h_bytes`,
    `hc_lo_sum_lt`, `hc_hi_sum_lt`, `h_match_clo`, `h_match_chi`,
    `h_a0_match`..`h_a3_match`) of the canonical `equiv_LW` with
    derivations from the trust ledger, leaving the caller with only
    the Mem-shape obligations + AIR validators + bus-protocol
    structural hypotheses. -/
theorem equiv_LW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lw_input : PureSpec.LwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validators + row index.
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation + opcode pin (Compliance ROM handshake).
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_W)
    -- Structural promise bundle (12 fields, see Promises/Load.lean).
    (promises : ZiskFv.Equivalence_v1.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lw_state_assumptions lw_input state)
        (PureSpec.execute_LOADW_pure lw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lw_input.imm,
        regidx.Regidx lw_input.r1,
        regidx.Regidx lw_input.rd,
        false,
        4
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  -- Run the BinExt-side full-discharge pipeline via the helper.
  obtain ⟨r_binary, lfd⟩ :=
    load_full_discharge_LW main v r_main e1 e2
      lw_input.r1_val lw_input.imm lw_input.rd
      h_main_active h_main_op
      promises.m1_mult promises.m1_as promises.m2_mult promises.m2_as
  have h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  -- Delegate to canonical `equiv_LW`.
  exact ZiskFv.Equivalence_v1.Lw.equiv_LW
    state lw_input regs
    ⟨exec_row, e0, e1, e2⟩
    promises
    main mem r_main
    ⟨h_main_active, h_main_op⟩
    v r_binary lfd.h_op_binary h_bytes lfd.hc_lo_sum_lt lfd.hc_hi_sum_lt
    lfd.h_match_clo lfd.h_match_chi
    lfd.h_a0_match lfd.h_a1_match lfd.h_a2_match lfd.h_a3_match

end ZiskFv.Compliance
