import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.MemoryBus.MemAlignBridge
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Equivalence.Bridge.SailStateBridge
import ZiskFv.Sail.sb
import ZiskFv.Sail.sh
import ZiskFv.Sail.sw

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
lemma load_discharge
    (main : Valid_Main C FGL FGL) (mem : ZiskFv.Airs.Mem.Valid_Mem C FGL FGL)
    (r_main : ℕ) (e : Interaction.MemoryBusEntry FGL)
    (h_main_emit : main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e
                   ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e
                   ∧ e.as = 2
                   ∧ e.multiplicity = -1) :
    ZiskFv.Airs.MemoryBus.memory_load_lanes_match main r_main e
    ∧ ∃ r_mem, ZiskFv.Airs.MemoryBus.MemBridge.mem_row_matches_entry mem r_mem e ∧ mem.wr r_mem = 0 :=
  ZiskFv.Airs.MemoryBus.MemBridge.memory_load_lanes_match_of_mem_row main mem r_main e h_main_emit

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
lemma load_discharge_full
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
lemma ld_discharge_full
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
lemma lbu_discharge_full
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
lemma lhu_discharge_full
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
lemma lwu_discharge_full
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
lemma sext_load_discharge_full
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
lemma lb_discharge_full
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
lemma lh_discharge_full
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
lemma lw_discharge_full
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
lemma sd_discharge_full
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

/-! ## Narrow-store discharges — SB / SH / SW

For each narrow store, the helper consumes:
* `main_store_emission_bundle_{sb,sh,sw}` (class #4, NEW — byte-level
  RMW bundle producing low-N byte equalities + high-(8-N) `state.mem`
  preservations);
* `transpile_{SB,SH,SW}` (class #1, pre-existing) materialized at the
  Sail state via `Bridge/SailStateBridge.lean`'s `sail_to_rv64`;

and produces `h_mem_eq` (the single bundled hypothesis on
`equiv_SB / SH / SW`) directly. The closure uses the `ExtHashMap`
insert-equals-self pattern on the high-byte inserts: each of the
`8 - N` trailing inserts in the bus side's 8-insert chain becomes a
no-op because the axiom's RMW clause says
`state.mem[ptr+i]? = some e_st.x_i`, so `m.insert k v = m` for the
already-present `(k, v)` pair.
-/

/-- **SB-specific store discharge.** Returns `h_mem_eq` in the shape
    `equiv_SB` consumes (8-insert chain = 1-insert chain on `state.mem`). -/
lemma sb_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e_st : Interaction.MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (h_ind_width : main.ind_width r_main = 1)
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    (h_read_r1 : LeanRV64D.Functions.rX_bits (regidx.Regidx sb_input.r1) state
      = EStateM.Result.ok sb_input.r1_val state)
    (h_read_r2 : LeanRV64D.Functions.rX_bits (regidx.Regidx sb_input.r2) state
      = EStateM.Result.ok sb_input.r2_val state) :
    (((((((state.mem.insert e_st.ptr.toNat e_st.x0
        ).insert (e_st.ptr.toNat + 1) e_st.x1
        ).insert (e_st.ptr.toNat + 2) e_st.x2
        ).insert (e_st.ptr.toNat + 3) e_st.x3
        ).insert (e_st.ptr.toNat + 4) e_st.x4
        ).insert (e_st.ptr.toNat + 5) e_st.x5
        ).insert (e_st.ptr.toNat + 6) e_st.x6
        ).insert (e_st.ptr.toNat + 7) e_st.x7
      = state.mem.insert
          (PureSpec.execute_STOREB_pure sb_input).data0.1
          (PureSpec.execute_STOREB_pure sb_input).data0.2 := by
  -- Convert `rX_bits` reads to `read_xreg` form.
  have h_read_r1' :
      read_xreg (regidx_to_fin (regidx.Regidx sb_input.r1)) state
        = EStateM.Result.ok sb_input.r1_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sb_input.r1)
          (regidx_to_fin (regidx.Regidx sb_input.r1))
          (by simp [regidx_to_fin])]
    exact h_read_r1
  have h_read_r2' :
      read_xreg (regidx_to_fin (regidx.Regidx sb_input.r2)) state
        = EStateM.Result.ok sb_input.r2_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sb_input.r2)
          (regidx_to_fin (regidx.Regidx sb_input.r2))
          (by simp [regidx_to_fin])]
    exact h_read_r2
  -- Materialize `transpile_SB` at the Sail-derived RV64 state.
  have h_tr := ZiskFv.Trusted.transpile_SB
    main r_main (regidx_to_fin (regidx.Regidx sb_input.r1))
    (regidx_to_fin (regidx.Regidx sb_input.r2)) (0 : FGL)
    (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
    h_active h_op_main
  obtain ⟨_, _, _, _, _, h_a_lo_state, h_a_hi_state, h_b_lo_state, h_b_hi_state⟩ := h_tr
  rw [ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state _ sb_input.r1_val h_read_r1'] at h_a_lo_state h_a_hi_state
  rw [ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state _ sb_input.r2_val h_read_r2'] at h_b_lo_state h_b_hi_state
  -- Apply the SB emission bundle to get ptr-match + low byte + RMW high bytes.
  obtain ⟨h_ptr, h_b0, h_m1, h_m2, h_m3, h_m4, h_m5, h_m6, h_m7⟩ :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_store_emission_bundle_sb
      main r_main e_st state sb_input.r1_val sb_input.r2_val sb_input.imm
      h_active h_op_main h_ind_width h_e_st_mult h_e_st_as_val
      h_a_lo_state h_a_hi_state h_b_lo_state h_b_hi_state
  -- Reduce the Sail spec's data fields.
  simp only [PureSpec.execute_STOREB_pure]
  -- Rewrite the LHS using ptr-match + low byte (substitute into LHS).
  -- Goal: 8-insert chain = state.mem.insert ptr data0.2.
  -- After ptr-match (e_st.ptr.toNat = (r1_val + signExt imm).toNat),
  -- inner insert at e_st.ptr.toNat equals the RHS's insert key. The
  -- remaining 7 inserts at ptr+1..ptr+7 must be no-ops because
  -- state.mem[ptr+i]? = some e_st.x_i (RMW preservation).
  -- We rewrite the RHS's data fields using h_ptr (key) and h_b0 (value),
  -- then chain `insert_eq_self` on the 7 trailing inserts.
  rw [h_ptr]
  -- The RHS is now `state.mem.insert ptr (extractLsb 7 0 r2_val)`.
  -- Replace `e_st.x0` in LHS with that same value via h_b0.
  conv_lhs => rw [show (e_st.x0 : BitVec 8) = BitVec.extractLsb 7 0 sb_input.r2_val from h_b0]
  -- Now LHS = 8-insert chain at ptr+0..ptr+7 with first insert matching RHS.
  -- Each of the 7 trailing inserts at ptr+i (i = 1..7) is a no-op because
  -- state.mem[ptr+i]? = some e_st.x_i (RMW preservation).
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  grind

/-- **SH-specific store discharge.** Returns `h_mem_eq` for SH (2 bytes). -/
lemma sh_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e_st : Interaction.MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (h_ind_width : main.ind_width r_main = 2)
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    (h_read_r1 : LeanRV64D.Functions.rX_bits (regidx.Regidx sh_input.r1) state
      = EStateM.Result.ok sh_input.r1_val state)
    (h_read_r2 : LeanRV64D.Functions.rX_bits (regidx.Regidx sh_input.r2) state
      = EStateM.Result.ok sh_input.r2_val state) :
    (((((((state.mem.insert e_st.ptr.toNat e_st.x0
        ).insert (e_st.ptr.toNat + 1) e_st.x1
        ).insert (e_st.ptr.toNat + 2) e_st.x2
        ).insert (e_st.ptr.toNat + 3) e_st.x3
        ).insert (e_st.ptr.toNat + 4) e_st.x4
        ).insert (e_st.ptr.toNat + 5) e_st.x5
        ).insert (e_st.ptr.toNat + 6) e_st.x6
        ).insert (e_st.ptr.toNat + 7) e_st.x7
      = (state.mem.insert
            (PureSpec.execute_STOREH_pure sh_input).data0.1
            (PureSpec.execute_STOREH_pure sh_input).data0.2
          ).insert
            (PureSpec.execute_STOREH_pure sh_input).data1.1
            (PureSpec.execute_STOREH_pure sh_input).data1.2 := by
  have h_read_r1' :
      read_xreg (regidx_to_fin (regidx.Regidx sh_input.r1)) state
        = EStateM.Result.ok sh_input.r1_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sh_input.r1)
          (regidx_to_fin (regidx.Regidx sh_input.r1))
          (by simp [regidx_to_fin])]
    exact h_read_r1
  have h_read_r2' :
      read_xreg (regidx_to_fin (regidx.Regidx sh_input.r2)) state
        = EStateM.Result.ok sh_input.r2_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sh_input.r2)
          (regidx_to_fin (regidx.Regidx sh_input.r2))
          (by simp [regidx_to_fin])]
    exact h_read_r2
  have h_tr := ZiskFv.Trusted.transpile_SH
    main r_main (regidx_to_fin (regidx.Regidx sh_input.r1))
    (regidx_to_fin (regidx.Regidx sh_input.r2)) (0 : FGL)
    (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
    h_active h_op_main
  obtain ⟨_, _, _, _, _, h_a_lo_state, h_a_hi_state, h_b_lo_state, h_b_hi_state⟩ := h_tr
  rw [ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state _ sh_input.r1_val h_read_r1'] at h_a_lo_state h_a_hi_state
  rw [ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state _ sh_input.r2_val h_read_r2'] at h_b_lo_state h_b_hi_state
  obtain ⟨h_ptr, h_b0, h_b1, h_m2, h_m3, h_m4, h_m5, h_m6, h_m7⟩ :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_store_emission_bundle_sh
      main r_main e_st state sh_input.r1_val sh_input.r2_val sh_input.imm
      h_active h_op_main h_ind_width h_e_st_mult h_e_st_as_val
      h_a_lo_state h_a_hi_state h_b_lo_state h_b_hi_state
  simp only [PureSpec.execute_STOREH_pure]
  rw [h_ptr]
  conv_lhs => rw [show (e_st.x0 : BitVec 8) = BitVec.extractLsb 7 0 sh_input.r2_val from h_b0]
  conv_lhs => rw [show (e_st.x1 : BitVec 8) = BitVec.extractLsb 15 8 sh_input.r2_val from h_b1]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  grind

/-- **SW-specific store discharge.** Returns `h_mem_eq` for SW (4 bytes). -/
lemma sw_discharge_full
    (main : Valid_Main C FGL FGL)
    (r_main : ℕ)
    (e_st : Interaction.MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (h_ind_width : main.ind_width r_main = 4)
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    (h_read_r1 : LeanRV64D.Functions.rX_bits (regidx.Regidx sw_input.r1) state
      = EStateM.Result.ok sw_input.r1_val state)
    (h_read_r2 : LeanRV64D.Functions.rX_bits (regidx.Regidx sw_input.r2) state
      = EStateM.Result.ok sw_input.r2_val state) :
    (((((((state.mem.insert e_st.ptr.toNat e_st.x0
        ).insert (e_st.ptr.toNat + 1) e_st.x1
        ).insert (e_st.ptr.toNat + 2) e_st.x2
        ).insert (e_st.ptr.toNat + 3) e_st.x3
        ).insert (e_st.ptr.toNat + 4) e_st.x4
        ).insert (e_st.ptr.toNat + 5) e_st.x5
        ).insert (e_st.ptr.toNat + 6) e_st.x6
        ).insert (e_st.ptr.toNat + 7) e_st.x7
      = (((state.mem.insert
            (PureSpec.execute_STOREW_pure sw_input).data0.1
            (PureSpec.execute_STOREW_pure sw_input).data0.2
          ).insert
            (PureSpec.execute_STOREW_pure sw_input).data1.1
            (PureSpec.execute_STOREW_pure sw_input).data1.2
          ).insert
            (PureSpec.execute_STOREW_pure sw_input).data2.1
            (PureSpec.execute_STOREW_pure sw_input).data2.2
          ).insert
            (PureSpec.execute_STOREW_pure sw_input).data3.1
            (PureSpec.execute_STOREW_pure sw_input).data3.2 := by
  have h_read_r1' :
      read_xreg (regidx_to_fin (regidx.Regidx sw_input.r1)) state
        = EStateM.Result.ok sw_input.r1_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sw_input.r1)
          (regidx_to_fin (regidx.Regidx sw_input.r1))
          (by simp [regidx_to_fin])]
    exact h_read_r1
  have h_read_r2' :
      read_xreg (regidx_to_fin (regidx.Regidx sw_input.r2)) state
        = EStateM.Result.ok sw_input.r2_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sw_input.r2)
          (regidx_to_fin (regidx.Regidx sw_input.r2))
          (by simp [regidx_to_fin])]
    exact h_read_r2
  have h_tr := ZiskFv.Trusted.transpile_SW
    main r_main (regidx_to_fin (regidx.Regidx sw_input.r1))
    (regidx_to_fin (regidx.Regidx sw_input.r2)) (0 : FGL)
    (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
    h_active h_op_main
  obtain ⟨_, _, _, _, _, h_a_lo_state, h_a_hi_state, h_b_lo_state, h_b_hi_state⟩ := h_tr
  rw [ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state _ sw_input.r1_val h_read_r1'] at h_a_lo_state h_a_hi_state
  rw [ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state _ sw_input.r2_val h_read_r2'] at h_b_lo_state h_b_hi_state
  obtain ⟨h_ptr, h_b0, h_b1, h_b2, h_b3, h_m4, h_m5, h_m6, h_m7⟩ :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_store_emission_bundle_sw
      main r_main e_st state sw_input.r1_val sw_input.r2_val sw_input.imm
      h_active h_op_main h_ind_width h_e_st_mult h_e_st_as_val
      h_a_lo_state h_a_hi_state h_b_lo_state h_b_hi_state
  simp only [PureSpec.execute_STOREW_pure]
  rw [h_ptr]
  conv_lhs => rw [show (e_st.x0 : BitVec 8) = BitVec.extractLsb 7 0 sw_input.r2_val from h_b0]
  conv_lhs => rw [show (e_st.x1 : BitVec 8) = BitVec.extractLsb 15 8 sw_input.r2_val from h_b1]
  conv_lhs => rw [show (e_st.x2 : BitVec 8) = BitVec.extractLsb 23 16 sw_input.r2_val from h_b2]
  conv_lhs => rw [show (e_st.x3 : BitVec 8) = BitVec.extractLsb 31 24 sw_input.r2_val from h_b3]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  grind

end ZiskFv.Equivalence.Bridge.Mem
