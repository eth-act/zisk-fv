import Mathlib

import ZiskFv.Equivalence.Lw
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Equivalence.Bridge.BinaryExtension
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.BinaryExtensionTable

/-!
# `equiv_LW` Compliance wrapper — signed-load BinExt SEXT_W chain (Step 4.2 round 4.C)

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

namespace ZiskFv.Equivalence.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_LW`.** Replaces the eight
    BinExt-side promise hypotheses (`h_op_binary`, `h_bytes`,
    `hc_lo_sum_lt`, `hc_hi_sum_lt`, `h_match_clo`, `h_match_chi`,
    `h_a0_match`..`h_a3_match`) of the canonical `equiv_LW` with
    derivations from the trust ledger, leaving the caller with only
    the Mem-shape obligations + AIR validators + bus-protocol
    structural hypotheses. -/
theorem equiv_LW_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lw_input : PureSpec.LwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    -- AIR validators + row index.
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Activation + opcode pin (Compliance ROM handshake).
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_W)
    -- Sail-side state predicates (SPEC-PRE).
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lw_state_assumptions lw_input state)
    -- Bus-protocol structural hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADW_pure lw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lw_input.imm,
        regidx.Regidx lw_input.r1,
        regidx.Regidx lw_input.rd,
        false,
        4
      ))) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- ============ Derive (r_binary, h_match) via op-bus permutation soundness ============
  -- `OP_SIGNEXTEND_W = 41 = 0x29` matches the 9th disjunct of
  -- `op_bus_perm_sound_BinaryExtension`'s opcode coverage.
  have h_main_op_disj :
      main.op r_main = 0x21 ∨ main.op r_main = 0x22 ∨ main.op r_main = 0x23
      ∨ main.op r_main = 0x24 ∨ main.op r_main = 0x25 ∨ main.op r_main = 0x26
      ∨ main.op r_main = 0x27 ∨ main.op r_main = 0x28 ∨ main.op r_main = 0x29 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_main_op)))))))
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryExtension main v r_main h_main_active h_main_op_disj
  -- ============ Project `op` / `c_lo` / `c_hi` from matches_entry ============
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main r_binary h_match
  have h_op_binary : (v.op r_binary).val
      = ZiskFv.Airs.BinaryExtensionTable.OP_SEXT_W := by
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
  -- ============ op_is_shift = 0 from the SEXT_W branch of the pin ============
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SIGNEXTEND_W := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift_zero : v.op_is_shift r_binary = 0 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin v r_binary).2
      (Or.inr (Or.inr h_op_v_eq))
  -- ============ Mem-side bundle (b-lo, b-hi, c-lo, c-hi, ptr, rd routing) ============
  obtain ⟨h_main_emit_b, _h_main_emit_c, _h_ptr_match,
          _h_rd_zero_iff, _h_rd_idx⟩ :=
    ZiskFv.Equivalence.Bridge.Mem.lw_discharge_full
      main r_main e1 e2 lw_input.r1_val lw_input.imm lw_input.rd
      h_main_active h_main_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  -- The bundle's first conjunct contains m.b_0 = memory_entry_lo e1.
  have h_main_b0_eq : main.b_0 r_main
      = ZiskFv.Airs.MemoryBus.memory_entry_lo e1 := h_main_emit_b.1
  -- ============ SEXT lane-match: derive (free_in_a_i).val = e1.x_i.val ============
  obtain ⟨h_a0_match, h_a1_match, h_a2_match, h_a3_match⟩ :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.sext_lane_match_bytes_eq_of_match
      main v r_main r_binary e1 h_main_b0_eq h_op_is_shift_zero h_match
  -- ============ Delegate to canonical `equiv_LW` ============
  exact ZiskFv.Equivalence.Lw.equiv_LW
    state lw_input mstatus pmaRegion misa mseccfg
    exec_row e0 e1 e2 risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    main mem r_main h_main_active h_main_op
    v r_binary h_op_binary h_bytes hc_lo_sum_lt hc_hi_sum_lt
    h_match_clo h_match_chi
    h_a0_match h_a1_match h_a2_match h_a3_match

end ZiskFv.Equivalence.Compliance
