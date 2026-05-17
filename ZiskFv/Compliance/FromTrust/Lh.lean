import Mathlib

import ZiskFv.Equivalence.Lh
import ZiskFv.Equivalence.Promises.Load
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Equivalence.Bridge.BinaryExtension
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
> Mirrors `equiv_LW_from_trust` (`Compliance/FromTrust/Lw.lean`) with a
> narrower SEXT_H chain (2-byte input → sign-extend to 64 bits).

## 5-category discharge applied

Mirrors `equiv_LW_from_trust` exactly; see that file for the full
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

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_LH`.** Replaces the BinExt-side
    promise hypotheses (`h_op_binary`, `h_bytes`, `hc_lo_sum_lt`,
    `hc_hi_sum_lt`, `h_match_clo`, `h_match_chi`, `h_a0_match`,
    `h_a1_match`) of the canonical `equiv_LH` with derivations from
    the trust ledger, leaving the caller with only the Mem-shape
    obligations + AIR validators + bus-protocol structural
    hypotheses. -/
theorem equiv_LH_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validators + row index.
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation + opcode pin (Compliance ROM handshake).
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_H)
    -- Structural promise bundle (12 fields, see Promises/Load.lean).
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
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
  -- Bundle fields used later in the proof body (do NOT consume `promises`
  -- with `obtain` since it is passed through to `equiv_LH`).
  have h_m1_mult := promises.m1_mult
  have h_m1_as := promises.m1_as
  have h_m2_mult := promises.m2_mult
  have h_m2_as := promises.m2_as
  -- ============ Derive (r_binary, h_match) via op-bus permutation soundness ============
  -- `OP_SIGNEXTEND_H = 40 = 0x28` matches the 8th disjunct of
  -- `op_bus_perm_sound_BinaryExtension`'s opcode coverage.
  have h_main_op_disj :
      main.op r_main = 0x21 ∨ main.op r_main = 0x22 ∨ main.op r_main = 0x23
      ∨ main.op r_main = 0x24 ∨ main.op r_main = 0x25 ∨ main.op r_main = 0x26
      ∨ main.op r_main = 0x27 ∨ main.op r_main = 0x28 ∨ main.op r_main = 0x29 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op)))))))
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryExtension main v r_main h_main_active h_main_op_disj
  -- ============ Project `op` / `c_lo` / `c_hi` from matches_entry ============
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main r_binary h_match
  have h_op_binary : (v.op r_binary).val
      = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_H := by
    rw [← h_op_fgl, h_main_op]; decide
  -- ============ c-lane sum bounds via row-level discharge ============
  have hc_lo_sum_lt :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      main v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      main v r_main r_binary h_match_chi
  -- ============ h_bytes from binary_extension_row_byte_lookups ============
  have h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  -- ============ op_is_shift = 0 from the SEXT_H branch of the pin ============
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SIGNEXTEND_H := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift_zero : v.op_is_shift r_binary = 0 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin v r_binary).2
      (Or.inr (Or.inl h_op_v_eq))
  -- ============ Mem-side bundle (b-lo, b-hi, c-lo, c-hi, ptr, rd routing) ============
  obtain ⟨h_main_emit_b, _h_main_emit_c, _h_ptr_match,
          _h_rd_zero_iff, _h_rd_idx⟩ :=
    ZiskFv.Equivalence.Bridge.Mem.lh_discharge_full
      main r_main e1 e2 lh_input.r1_val lh_input.imm lh_input.rd
      h_main_active h_main_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  -- The bundle's first conjunct contains m.b_0 = memory_entry_lo e1.
  have h_main_b0_eq : main.b_0 r_main
      = ZiskFv.Airs.MemoryBus.memory_entry_lo e1 := h_main_emit_b.1
  -- ============ SEXT lane-match: derive (free_in_a_i).val = e1.x_i.val ============
  obtain ⟨h_a0_match, h_a1_match, _h_a2_match, _h_a3_match⟩ :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.sext_lane_match_bytes_eq_of_match
      main v r_main r_binary e1 h_main_b0_eq h_op_is_shift_zero h_match
  -- ============ Delegate to canonical `equiv_LH` ============
  exact ZiskFv.Equivalence.Lh.equiv_LH
    state lh_input regs
    ⟨exec_row, e0, e1, e2⟩
    promises
    main mem r_main
    ⟨h_main_active, h_main_op⟩
    v r_binary h_op_binary h_bytes hc_lo_sum_lt hc_hi_sum_lt
    h_match_clo h_match_chi
    h_a0_match h_a1_match

end ZiskFv.Compliance
