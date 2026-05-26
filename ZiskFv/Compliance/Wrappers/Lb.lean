import Mathlib

import ZiskFv.EquivCore.Lb
import ZiskFv.EquivCore.Promises.Load
import ZiskFv.EquivCore.Promises.BinaryExtensionHelpers
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
# `equiv_LB` Compliance wrapper — signed-load BinExt SEXT_B chain

> **Status:** Third of three signed-load wrappers (LW / LH / LB).
> Mirrors `equiv_LH` (`Compliance/Wrappers/Lh.lean`) with
> the narrowest SEXT_B chain (1-byte input → 64-bit sign-extend).

## 5-category discharge applied

Mirrors `equiv_LW` exactly; see that file for the full
write-up. The only differences are:

* opcode literal `OP_SIGNEXTEND_B = 0x27` (7th disjunct of
  `op_bus_perm_sound_BinaryExtension`).
* canonical equiv `equiv_LB` consumes only `h_a0_match` (1 byte for
  byte load).
* circuit packing chain uses `load_byte_c_packed` /
  `binary_extension_sext_b_chunks_eq_signextend_nat` (pre-discharged
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
open ZiskFv.EquivCore.Promises


/-- **Compliance wrapper for `equiv_LB`.** Replaces the BinExt-side
    promise hypotheses (`h_op_binary`, `h_bytes`, `hc_lo_sum_lt`,
    `hc_hi_sum_lt`, `h_match_clo`, `h_match_chi`, `h_a0_match`) of
    the canonical `equiv_LB` with derivations from the trust ledger,
    leaving the caller with only the Mem-shape obligations + AIR
    validators + bus-protocol structural hypotheses. -/
theorem equiv_LB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validators + row index.
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation + opcode pin (Compliance ROM handshake).
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_B)
    -- Structural promise bundle (12 fields, see Promises/Load.lean).
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lb_state_assumptions lb_input state)
        (PureSpec.execute_LOADB_pure lb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lb_input.imm,
        regidx.Regidx lb_input.r1,
        regidx.Regidx lb_input.rd,
        false,
        1
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  -- Run the BinExt-side full-discharge pipeline via the helper. This
  -- bundles `op_bus_perm_sound_BinaryExtension` + `project_match_op_clo_chi`
  -- + c-lane sum bounds + `op_is_shift = 0` + `lb_discharge_full` +
  -- `sext_lane_match_bytes_eq_of_match` into a single call.
  obtain ⟨r_binary, lfd⟩ :=
    load_full_discharge_LB main v r_main e1 e2
      lb_input.r1_val lb_input.imm lb_input.rd
      h_main_active h_main_op
      promises.m1_mult promises.m1_as promises.m2_mult promises.m2_as
  -- `h_bytes` lives outside the `Prop`-valued discharge bundle.
  have h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  -- Delegate to canonical `equiv_LB`.
  exact ZiskFv.EquivCore.Lb.equiv_LB
    state lb_input regs
    ⟨exec_row, e0, e1, e2⟩
    promises
    main mem r_main
    ⟨h_main_active, h_main_op⟩
    v r_binary lfd.h_op_binary h_bytes lfd.hc_lo_sum_lt lfd.hc_hi_sum_lt
    lfd.h_match_clo lfd.h_match_chi
    lfd.h_a0_match

/-- Static-lookup route for the LB wrapper. This is not the canonical wrapper
    surface; it is the C7 rewiring target that consumes the shared
    BinaryExtension static lookup witness instead of the legacy table axiom. -/
theorem equiv_LB_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lb_state_assumptions lb_input state)
        (PureSpec.execute_LOADB_pure lb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lb_input.imm,
        regidx.Regidx lb_input.r1,
        regidx.Regidx lb_input.rd,
        false,
        1
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  obtain ⟨r_binary, lfd⟩ :=
    load_full_discharge_LB_of_static_lookup main v r_main offset env e1 e2
      lb_input.r1_val lb_input.imm lb_input.rd h_static
      h_main_active h_main_op
      promises.m1_mult promises.m1_as promises.m2_mult promises.m2_as
  let h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes] using
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookup_wfs_of_static_lookup
      v r_binary offset env h_static
  exact ZiskFv.EquivCore.Lb.equiv_LB_of_wf
    state lb_input regs
    ⟨exec_row, e0, e1, e2⟩
    promises
    main mem r_main
    ⟨h_main_active, h_main_op⟩
    v r_binary lfd.h_op_binary h_bytes h_wfs
    lfd.hc_lo_sum_lt lfd.hc_hi_sum_lt
    lfd.h_match_clo lfd.h_match_chi
    lfd.h_a0_match

/-- Row-explicit + static-lookup route for the LB wrapper.
    Takes `r_binary + h_match` directly, bypassing
    `op_bus_perm_sound_BinaryExtension`. The dispatcher-side
    `equiv_LB_via_static_binary_extension` derives both from a Clean
    BinaryFamily ensemble balance. -/
theorem equiv_LB_of_static_match
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      matches_entry (opBus_row_Main main r_main) (opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lb_state_assumptions lb_input state)
        (PureSpec.execute_LOADB_pure lb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lb_input.imm,
        regidx.Regidx lb_input.r1,
        regidx.Regidx lb_input.rd,
        false,
        1
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  have lfd :=
    load_full_discharge_LB_of_match main v r_main r_binary offset env e1 e2
      lb_input.r1_val lb_input.imm lb_input.rd h_static h_match
      h_main_active h_main_op
      promises.m1_mult promises.m1_as promises.m2_mult promises.m2_as
  let h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes] using
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookup_wfs_of_static_lookup
      v r_binary offset env h_static
  exact ZiskFv.EquivCore.Lb.equiv_LB_of_wf
    state lb_input regs
    ⟨exec_row, e0, e1, e2⟩
    promises
    main mem r_main
    ⟨h_main_active, h_main_op⟩
    v r_binary lfd.h_op_binary h_bytes h_wfs
    lfd.hc_lo_sum_lt lfd.hc_hi_sum_lt
    lfd.h_match_clo lfd.h_match_chi
    lfd.h_a0_match

end ZiskFv.Compliance
