import Mathlib

import ZiskFv.Equivalence_v1.Lh
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
# `equiv_LH` Compliance wrapper — signed-load BinExt SEXT_H chain

> **Status:** Second of three signed-load wrappers (LW / LH / LB).
> Mirrors `equiv_LW` (`Compliance/Wrappers/Lw.lean`) with a
> narrower SEXT_H chain (2-byte input → sign-extend to 64 bits).

## 5-category discharge applied

Mirrors `equiv_LW` exactly; see that file for the full
write-up. The only differences are:

* opcode literal `OP_SIGNEXTEND_H = 0x28` instead of `0x29` (8th
  disjunct of `op_bus_perm_sound_BinaryExtension`).
* canonical equiv `equiv_LH` consumes only `h_a0_match` and
  `h_a1_match` (2 bytes for halfword) instead of all four.
* circuit packing chain uses `load_half_c_packed` /
  `binary_extension_sext_h_chunks_eq_signextend_nat` (pre-discharged
  on the canonical surface).

## Anti-laundering report

* **Zero new axioms** — consumes only existing trust-ledger axioms.
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


/-- **Compliance wrapper for `equiv_LH`.** Replaces the BinExt-side
    promise hypotheses (`h_op_binary`, `h_bytes`, `hc_lo_sum_lt`,
    `hc_hi_sum_lt`, `h_match_clo`, `h_match_chi`, `h_a0_match`,
    `h_a1_match`) of the canonical `equiv_LH` with derivations from
    the trust ledger, leaving the caller with only the Mem-shape
    obligations + AIR validators + bus-protocol structural
    hypotheses. -/
theorem equiv_LH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validators + row index.
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation + opcode pin (Compliance ROM handshake).
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_H)
    -- Structural promise bundle (12 fields, see Promises/Load.lean).
    (promises : ZiskFv.Equivalence_v1.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lh_state_assumptions lh_input state)
        (PureSpec.execute_LOADH_pure lh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm,
        regidx.Regidx lh_input.r1,
        regidx.Regidx lh_input.rd,
        false,
        2
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  -- Run the BinExt-side full-discharge pipeline via the helper.
  obtain ⟨r_binary, lfd⟩ :=
    load_full_discharge_LH main v r_main e1 e2
      lh_input.r1_val lh_input.imm lh_input.rd
      h_main_active h_main_op
      promises.m1_mult promises.m1_as promises.m2_mult promises.m2_as
  have h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  -- Delegate to canonical `equiv_LH`.
  exact ZiskFv.Equivalence_v1.Lh.equiv_LH
    state lh_input regs
    ⟨exec_row, e0, e1, e2⟩
    promises
    main mem r_main
    ⟨h_main_active, h_main_op⟩
    v r_binary lfd.h_op_binary h_bytes lfd.hc_lo_sum_lt lfd.hc_hi_sum_lt
    lfd.h_match_clo lfd.h_match_chi
    lfd.h_a0_match lfd.h_a1_match

end ZiskFv.Compliance
