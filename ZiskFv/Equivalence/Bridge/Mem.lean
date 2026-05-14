import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.MemoryBus.MemAlignBridge
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Equivalence.Bridge.SailStateBridge

/-!
# Mem discharge bridge

Implements *promise discharge* for the Mem-AIR-shape opcodes —
loads (`LD` / `LBU` / `LHU` / `LWU` / `LB` / `LH` / `LW`) and
stores (`SD` / `SB` / `SH` / `SW`).

Unlike the BinaryAdd / Binary / BinaryExtension / Arith bridges,
the Mem-side derivation infrastructure was authored *before* the
Step 2 bridge convention was established. The bulk of the work
lives in:

* `ZiskFv/Airs/MemoryBus/MemBridge.lean` — `lookup_consumer_matches_provider_load`
  and `lookup_consumer_matches_provider_store` axioms plus the
  `memory_{load,store}_lanes_match_of_mem_row` packaging theorems
  that produce the existential Mem row witness from the Main-side
  emission.
* `ZiskFv/Airs/MemoryBus/LaneMatch.lean` — the
  `memory_bus_register_write_perm_sound` axiom plus
  `register_{write,read_rs1,read_rs2}_lanes_match_of_bus_emission`
  theorems for the register-side lane match (`as = 1`).
* `ZiskFv/Airs/MemoryBus/MemAlignBridge.lean` — the
  `memalign_load_perm_sound` and
  `mem_align_rom_subdoubleword_load_value_1_zero` axioms plus the
  derived sub-doubleword zero-pad theorems
  (`memalign_subdoubleword_load_high_bytes_zero` etc.) that
  ground LBU / LHU / LWU's high-byte-zero claims.

This module is a thin façade re-exporting those theorems under a
single `Bridge.Mem` namespace alias so that downstream
`equiv_<OP>` proofs (Step 3) can consume Mem-side discharges
through the same import path the other bridges use.

No new axioms; no new derivation. All Mem-side trust was already
encoded prior to the Step 2 bridge convention; this file simply
groups it for uniform downstream access.
-/

namespace ZiskFv.Equivalence.Bridge.Mem

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Load-side discharge.** Re-export of
    `MemoryBus.memory_load_lanes_match_of_mem_row`: given a Main
    emission whose `b` lanes pack the entry's lo/hi halves
    (`as = 2`, `multiplicity = -1`), deliver the lane-match
    conclusion plus an existential Mem-AIR row witness grounded by
    `lookup_consumer_matches_provider_load`. Consumed by
    `equiv_LD` / `equiv_LBU` / `equiv_LHU` / `equiv_LWU` (and
    indirectly by `equiv_LB` / `equiv_LH` / `equiv_LW` after the
    sign-extension chain in `Circuit/SextLoadBridge.lean`). -/
theorem load_discharge
    (main : Valid_Main C FGL FGL) (mem : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_main_emit : main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e
                   ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = -1) :
    ZiskFv.Airs.MemoryBus.memory_load_lanes_match main r_main e
    ∧ ∃ r_mem, ZiskFv.Airs.MemoryBus.MemBridge.mem_row_matches_entry mem r_mem e ∧ mem.wr r_mem = 0 :=
  ZiskFv.Airs.MemoryBus.MemBridge.memory_load_lanes_match_of_mem_row main mem r_main e h_main_emit

/-- **Store-side discharge.** Symmetric to `load_discharge` for
    stores (`multiplicity = 1`, Main's `c` lanes carry the value).
    Consumed by `equiv_SD` / `equiv_SB` / `equiv_SH` / `equiv_SW`. -/
theorem store_discharge
    (main : Valid_Main C FGL FGL) (mem : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_main_emit : main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e
                   ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = 1) :
    ZiskFv.Airs.MemoryBus.memory_store_lanes_match main r_main e
    ∧ ∃ r_mem, ZiskFv.Airs.MemoryBus.MemBridge.mem_row_matches_entry mem r_mem e ∧ mem.wr r_mem = 1 :=
  ZiskFv.Airs.MemoryBus.MemBridge.memory_store_lanes_match_of_mem_row main mem r_main e h_main_emit

/-! ## Per-opcode `<op>_discharge_full` entry points

For each Mem-AIR-shape opcode, the entry point below packages the
full set of memory-side promise hypotheses an `equiv_<OP>` theorem
needs into a single derivation, consuming the trust-ledger entries
* `main_load_emission_bundle` / `main_store_emission_bundle`
  (NEW — Main row's memory-bus emission shape, class #4),
* `lookup_consumer_matches_provider_load` / `..._store`
  (existing — class #4 memory-bus permutation soundness),
* `memory_bus_entry_byte_range_perm_sound` (existing — class #5b
  byte-range bus soundness),
* transpile contracts (`transpile_LD`, `transpile_SD`, ...).

Caller obligations after this discharge collapse to:
* `main : Valid_Main C FGL FGL`, `mem : Valid_Mem C FGL FGL`,
  `r_main : ℕ` (validators + row index);
* `h_active`, `h_op_main` (Main row activation + opcode pin —
  derivable from `transpile_<OP>` once the global Compliance
  theorem provides `core_every_row m r_main` + the Sail decode);
* `e1`, `e2 : MemoryBusEntry FGL` (bus entries, structural);
* `h_e1_mult`, `h_e1_as_val`, `h_e2_mult`, `h_e2_as_val` (bus shape
  pins, already required by `equiv_<OP>` regardless).

The discharge entry point returns the full bundle each per-opcode
equiv currently consumes as separate parameters:
`h_main_emit_b`, `h_main_emit_c`, `h_ptr_match`, `h_copy0`,
`h_copy1`, `h_ext`, `h_op`, `h_rd_zero_iff`, `h_rd_idx`
(for loads), and the store analogue. -/

/-- **Common load discharge full bundle.** Shared by LD / LBU /
    LHU / LWU (all four use `transpile_<OP>` axioms with identical
    Main-row contracts on the bridged columns; the width difference
    is carried downstream on the memory-bus entry, not on Main).

    Inputs:
    * `main`, `r_main` — Main AIR validator + row;
    * `e1`, `e2` — load consumer + rd-write bus entries (already
      bound at `equiv_<OP>` parameter level);
    * `r1_val`, `imm`, `rd` — Sail-side load operand values
      (already bound via the `<op>_input` record);
    * `h_active`, `h_op_main` — Main row is internal (copyb), pinned
      via the relevant `transpile_<OP>` axiom in the equiv;
    * `h_e1_mult`, `h_e1_as_val`, `h_e2_mult`, `h_e2_as_val` — bus
      structural shape (already at the equiv).

    Returns the seven-tuple of `equiv_<OP>` promises:
    `(h_main_emit_b, h_main_emit_c, h_ptr_match, h_rd_zero_iff,
      h_rd_idx, h_copy0, h_copy1)`. -/
theorem load_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (h_e1_mult : e1.multiplicity = -1) (h_e1_as_val : e1.as.val = 2)
    (h_e2_mult : e2.multiplicity = 1) (h_e2_as_val : e2.as.val = 1) :
    -- `h_main_emit_b` shape:
    (main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    -- `h_main_emit_c` shape:
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2)
    -- `h_ptr_match`:
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    -- `h_rd_zero_iff` / `h_rd_idx`:
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val
    -- `h_copy0` / `h_copy1` (Main constraints 9/16, copyb passthrough):
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main := by
  obtain ⟨h_b0, h_b1, h_e1_as, h_e1_mult', h_c0, h_c1, h_ptr, h_rd_iff, h_rd_idx,
          h_cop0, h_cop1⟩ :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_load_emission_bundle
      main r_main e1 e2 r1_val imm rd h_active h_op_main
      h_e1_mult h_e1_as_val h_e2_mult h_e2_as_val
  exact ⟨⟨h_b0, h_b1, h_e1_as, h_e1_mult'⟩, ⟨h_c0, h_c1⟩, h_ptr,
         h_rd_iff, h_rd_idx, h_cop0, h_cop1⟩

/-- **Per-opcode load discharge — LD.** Synonym of
    `load_discharge_full`; named for downstream readability. -/
theorem ld_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (h_e1_mult : e1.multiplicity = -1) (h_e1_as_val : e1.as.val = 2)
    (h_e2_mult : e2.multiplicity = 1) (h_e2_as_val : e2.as.val = 1) :
    (main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2)
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main :=
  load_discharge_full main r_main e1 e2 r1_val imm rd
    h_active h_op_main h_e1_mult h_e1_as_val h_e2_mult h_e2_as_val

/-- **Per-opcode load discharge — LBU.** Same shape as LD; the
    width is downstream-irrelevant for the Main-row contract. -/
theorem lbu_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (h_e1_mult : e1.multiplicity = -1) (h_e1_as_val : e1.as.val = 2)
    (h_e2_mult : e2.multiplicity = 1) (h_e2_as_val : e2.as.val = 1) :
    (main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2)
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main :=
  load_discharge_full main r_main e1 e2 r1_val imm rd
    h_active h_op_main h_e1_mult h_e1_as_val h_e2_mult h_e2_as_val

/-- **Per-opcode load discharge — LHU.** Same shape as LBU. -/
theorem lhu_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (h_e1_mult : e1.multiplicity = -1) (h_e1_as_val : e1.as.val = 2)
    (h_e2_mult : e2.multiplicity = 1) (h_e2_as_val : e2.as.val = 1) :
    (main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2)
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main :=
  load_discharge_full main r_main e1 e2 r1_val imm rd
    h_active h_op_main h_e1_mult h_e1_as_val h_e2_mult h_e2_as_val

/-- **Per-opcode load discharge — LWU.** Same shape as LBU. -/
theorem lwu_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (h_e1_mult : e1.multiplicity = -1) (h_e1_as_val : e1.as.val = 2)
    (h_e2_mult : e2.multiplicity = 1) (h_e2_as_val : e2.as.val = 1) :
    (main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2)
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main :=
  load_discharge_full main r_main e1 e2 r1_val imm rd
    h_active h_op_main h_e1_mult h_e1_as_val h_e2_mult h_e2_as_val

/-! ## Signed-load discharge — LB / LH / LW

The sext-load family routes through the BinaryExtension AIR for
sign-extension (`is_external_op = 1`, `op = OP_SIGNEXTEND_{B,H,W}`)
rather than the copyb passthrough used by LD / LBU / LHU / LWU. The
Main row's memory-bus emission shape is identical (same b-side load
consumer + c-side rd-write entries) so the discharge produces the
same five lane / ptr / rd facts as the copyb loads, minus the
copyb passthrough constraints (which are conditioned on
`is_external_op = 0` and so vacuous here).

Consumes `MemBridge.main_sext_load_emission_bundle` (class #4). -/

/-- **Common signed-load discharge full bundle.** Shared by LB / LH
    / LW. Caller supplies the activation pins (transpile-derived in
    practice) and bus-shape pins; returns the lane / ptr / rd-routing
    bundle. -/
theorem sext_load_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (op_code : FGL)
    (h_ext : main.is_external_op r_main = 1)
    (h_op : main.op r_main = op_code)
    (h_op_sext : op_code = ZiskFv.Trusted.OP_SIGNEXTEND_B
                  ∨ op_code = ZiskFv.Trusted.OP_SIGNEXTEND_H
                  ∨ op_code = ZiskFv.Trusted.OP_SIGNEXTEND_W)
    (h_e1_mult : e1.multiplicity = -1) (h_e1_as_val : e1.as.val = 2)
    (h_e2_mult : e2.multiplicity = 1) (h_e2_as_val : e2.as.val = 1) :
    -- `h_main_emit_b` shape:
    (main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    -- `h_main_emit_c` shape:
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2)
    -- `h_ptr_match`:
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    -- `h_rd_zero_iff` / `h_rd_idx`:
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val := by
  obtain ⟨h_b0, h_b1, h_e1_as, h_e1_mult', h_c0, h_c1, h_ptr,
          h_rd_iff, h_rd_idx⟩ :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_sext_load_emission_bundle
      main r_main e1 e2 r1_val imm rd op_code
      h_ext h_op h_op_sext
      h_e1_mult h_e1_as_val h_e2_mult h_e2_as_val
  exact ⟨⟨h_b0, h_b1, h_e1_as, h_e1_mult'⟩, ⟨h_c0, h_c1⟩, h_ptr,
         h_rd_iff, h_rd_idx⟩

/-- **Per-opcode signed-load discharge — LB.** -/
theorem lb_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_ext : main.is_external_op r_main = 1)
    (h_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (h_e1_mult : e1.multiplicity = -1) (h_e1_as_val : e1.as.val = 2)
    (h_e2_mult : e2.multiplicity = 1) (h_e2_as_val : e2.as.val = 1) :
    (main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2)
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val :=
  sext_load_discharge_full main r_main e1 e2 r1_val imm rd
    ZiskFv.Trusted.OP_SIGNEXTEND_B h_ext h_op (Or.inl rfl)
    h_e1_mult h_e1_as_val h_e2_mult h_e2_as_val

/-- **Per-opcode signed-load discharge — LH.** -/
theorem lh_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_ext : main.is_external_op r_main = 1)
    (h_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_H)
    (h_e1_mult : e1.multiplicity = -1) (h_e1_as_val : e1.as.val = 2)
    (h_e2_mult : e2.multiplicity = 1) (h_e2_as_val : e2.as.val = 1) :
    (main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2)
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val :=
  sext_load_discharge_full main r_main e1 e2 r1_val imm rd
    ZiskFv.Trusted.OP_SIGNEXTEND_H h_ext h_op (Or.inr (Or.inl rfl))
    h_e1_mult h_e1_as_val h_e2_mult h_e2_as_val

/-- **Per-opcode signed-load discharge — LW.** -/
theorem lw_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_ext : main.is_external_op r_main = 1)
    (h_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_W)
    (h_e1_mult : e1.multiplicity = -1) (h_e1_as_val : e1.as.val = 2)
    (h_e2_mult : e2.multiplicity = 1) (h_e2_as_val : e2.as.val = 1) :
    (main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2)
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val :=
  sext_load_discharge_full main r_main e1 e2 r1_val imm rd
    ZiskFv.Trusted.OP_SIGNEXTEND_W h_ext h_op (Or.inr (Or.inr rfl))
    h_e1_mult h_e1_as_val h_e2_mult h_e2_as_val

/-! ## Store discharge — SD (the Mem-stores pilot)

The SD store discharge composes
`main_store_emission_bundle_sd` (NEW — Main row's store-side
memory-bus emission in byte-extracted form) with `transpile_SD`
(class #1) and the Sail-state `read_xreg` bridge
(`Bridge/SailStateBridge.lean`, pure Lean) to deliver the full
9-hypothesis promise bundle that `equiv_SD` consumes (ptr-match +
8 byte extracts).

Caller obligations after this discharge collapse to:
* `main : Valid_Main C FGL FGL`, `r_main : ℕ`;
* `h_main_active : main.is_external_op r_main = 0` and
  `h_main_op : main.op r_main = OP_COPYB` (Main row activation
  for the copyb store row — derivable from the Compliance theorem's
  ROM-handshake on the row hosting SD);
* `e_st : MemoryBusEntry FGL` (store entry, structural);
* `h_e_st_mult`, `h_e_st_as_val` (bus shape pins, already required
  by `equiv_SD`);
* the Sail-state `read_xreg` predicates for rs1/rs2 (SPEC-PRE,
  already at `equiv_SD`).
-/

/-- **SD-specific store discharge full bundle.** Composes
    `main_store_emission_bundle_sd` (class #4) with `transpile_SD`
    (class #1) — the latter discharges the bundle's
    `h_a_lo/hi`, `h_b_lo/hi` parameters from a Sail register-read
    pair (via `Bridge.SailStateBridge.sail_to_rv64`'s materialization
    of the universal-state `transpile_SD` to the Sail state). -/
theorem sd_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e_st : Interaction.MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32)
    (r1_val r2_val : BitVec 64) (imm : BitVec 12)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    -- ptr-match: store address = r1_val + signExt(imm)
    -- (in BitVec-sum form, matching `equiv_SD`).
    e_st.ptr.toNat = (r1_val + BitVec.signExtend 64 imm).toNat
    -- 8 byte extracts of r2_val.
    ∧ (e_st.x0 : BitVec 8) = BitVec.extractLsb 7 0 r2_val
    ∧ (e_st.x1 : BitVec 8) = BitVec.extractLsb 15 8 r2_val
    ∧ (e_st.x2 : BitVec 8) = BitVec.extractLsb 23 16 r2_val
    ∧ (e_st.x3 : BitVec 8) = BitVec.extractLsb 31 24 r2_val
    ∧ (e_st.x4 : BitVec 8) = BitVec.extractLsb 39 32 r2_val
    ∧ (e_st.x5 : BitVec 8) = BitVec.extractLsb 47 40 r2_val
    ∧ (e_st.x6 : BitVec 8) = BitVec.extractLsb 55 48 r2_val
    ∧ (e_st.x7 : BitVec 8) = BitVec.extractLsb 63 56 r2_val := by
  -- Materialize the universal-state `transpile_SD` axiom at the
  -- Sail-state-derived RV64 state to deliver `m.a/b lanes ↔
  -- lane_{lo,hi} (xreg rs)` facts. The `_imm_offset` placeholder
  -- is irrelevant to the lane equalities (transpile_SD only
  -- routes them through unused conjuncts).
  have h_tr := ZiskFv.Trusted.transpile_SD
    main r_main rs1 rs2 (0 : FGL)
    (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
    h_active h_op_main
  -- Extract the 4 lane equalities at the materialized RV64 state.
  obtain ⟨_, _, _, _, _, h_a_lo_state, h_a_hi_state, h_b_lo_state, h_b_hi_state⟩ :=
    h_tr
  -- Rewrite each lane equality from the materialized state's
  -- `xreg rs` to the Sail `r{1,2}_val` via the read_xreg bridge.
  rw [ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state rs1 r1_val h_read_r1] at h_a_lo_state h_a_hi_state
  rw [ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state rs2 r2_val h_read_r2] at h_b_lo_state h_b_hi_state
  -- Apply the store-emission bundle with the lane equalities now
  -- expressed in terms of `r1_val` / `r2_val`.
  exact ZiskFv.Airs.MemoryBus.MemBridge.main_store_emission_bundle_sd
    main r_main e_st r1_val r2_val imm
    h_active h_op_main h_e_st_mult h_e_st_as_val
    h_a_lo_state h_a_hi_state h_b_lo_state h_b_hi_state

end ZiskFv.Equivalence.Bridge.Mem
