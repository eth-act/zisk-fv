import Mathlib

import ZiskFv.Equivalence.Addi
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Tactics.ALUITypeArchetype

/-!
# `equiv_ADDI` Compliance wrapper — BinaryAdd ITYPE shape (Step 4.2r3.I)

> **Status:** Step 4.2 round 3.I (ITYPE constructibility bundles).
> Mirrors `AddExemplar.lean` for ADD, with the ITYPE-specific
> immediate-routing addition (`h_addi_subset`).
>
> Lives outside the canonical surface (under
> `Equivalence/Compliance/`) so V1 anti-laundering metrics on the
> canonical theorem are unaffected.

## Why ADDI

ADDI is the BinaryAdd ITYPE companion to ADD: the same Binary-SM
provider handles both, distinguished only by the transpiler's b-lane
routing — ADD reads `xreg(rs2)` onto Main's b-lanes; ADDI routes the
sign-extended 12-bit immediate. The Sail-level immediate must therefore
appear in the canonical equiv as a structural pin
(`itype_imm_subset_holds_main`) since `transpile_ADDI` leaves
`imm_b_lo`/`imm_b_hi` caller-routed. The wrapper passes this pin
through unchanged from caller; `Compliance.lean` will supply it from
a per-program universal invariant pinning every ADDI row's b-lanes
to the actual immediate of the originating RV64 instruction.

## 5-category discharge applied

* **Lane-match.** Internalized by `equiv_ADDI` via the existing
  `Bridge.BinaryAdd` discharge family (`chunk_ranges_at_holds` +
  matches_entry projection). The wrapper-level lane-match obligation
  on `e2` is currently caller-supplied (`h_lane_rd`).
* **Mode pins.** Main-side pins `m32 = 0`, `set_pc = 0` come from
  `transpile_ADDI` (class #1) — already consumed inside `equiv_ADDI`'s
  proof. Provider AIR (BinaryAdd) has no mode columns (N/A).
* **Sign-witness pins.** N/A.
* **Range/bound.** Discharged by `binary_add_columns_in_range`
  (class #5b) — internalized by `equiv_ADDI`. The 8 `e2` byte ranges
  are unpacked from `memory_bus_entry_byte_range_perm_sound` (class
  #5b) inside the wrapper.
* **Operand bridges.** The `h_input_r1_circuit` (Sail-input ↔ Main
  a-lane) bridge is internalized by `equiv_ADDI` via
  `Bridge.SailStateBridge.addi_input_r1_main_eq_of_read_xreg`. The
  immediate bridge (`h_addi_subset`) is the structural-unpacking
  pin — passed through as-is from caller.

## Anti-laundering report

* **No new axioms.** This wrapper consumes only `transpile_ADDI`
  (class #1, transitively via the canonical's closure),
  `op_bus_perm_sound_BinaryAdd` (class #4, consumed inside
  `equiv_ADDI`), `memory_bus_entry_byte_range_perm_sound` (class
  #5b), plus `equiv_ADDI`'s existing closure.
* **Caller-burden shrinks** (wrapper vs. canonical): the wrapper
  internalizes the 8 `e2` byte-range obligations via
  `memory_bus_entry_byte_range_perm_sound`. Net −8 binders.
* **Constructibility bundle.** `h_addi_subset` is a per-row
  pin delivered by `Compliance.lean` from a program-level universal
  — not a new caller-supplied promise hypothesis.

## Cross-shape lessons

The pattern transfers mechanically to ANDI/ORI/XORI (Binary provider
ITYPE variants):
* Swap `transpile_ADDI` → `transpile_<OP>I`.
* Swap `op_bus_perm_sound_BinaryAdd` → `op_bus_perm_sound_Binary`
  (with the larger opcode disjunction).
* The `itype_imm_subset_holds_main` predicate is reused verbatim —
  it's opcode-agnostic.
* The wrapper-level work for each is essentially copy of this file.
-/

namespace ZiskFv.Equivalence.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.MemoryBus
open ZiskFv.Circuit.Add
open ZiskFv.Circuit.Addi
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_ADDI`.**

    Caller obligations:
    1. Sail-side inputs (`state`, `addi_input`, `imm`, `r1`, `rd`).
    2. AIR validators + row index (`m`, `b`, `r_main`). Shared with
       ADD across the BinaryAdd shape.
    3. Structural bus rows (`exec_row`, `e0`, `e1`, `e2`).
    4. Activation + opcode pins (`h_main_active`, `h_main_op_addi`).
    5. Main-side constructibility bundles:
       * `h_main_subset : add_subset_holds m r_main` — universal-row
         ADD-subset constraints, shared with ADD via
         `∀ r, add_universal_row m r`.
       * `h_main_set_pc : m.set_pc r_main = 0` — ITYPE-specific pin
         (the canonical `main_row_in_addi_mode` uses `set_pc = 0` as
         its fourth pin instead of ADD's `flag = 0`). Derivable from
         `transpile_ADDI`.
       * `h_addi_subset : itype_imm_subset_holds_main m r_main
         addi_input.imm` — the constructibility pin tying Main's
         b-lanes to the actual RV64 immediate. Delivered by
         `Compliance.lean` from a per-program universal invariant.
       * `h_b_core` — universal BinaryAdd per-row validity, shared
         with ADD.
    6. `h_lane_rd` — rd-write lane-match, deferred to Mem pilot.
    7. Sail-state predicates + bus-shape obligations — pass-through.

    Derived internally (NOT caller-supplied):
    * `m.m32 r_main = 0` — from `transpile_ADDI` (class #1).
    * `main_row_in_addi_mode m r_main` — assembled from the four
      derived/caller-supplied pins.
    * `h_e2_0..h_e2_7 : e2.x{0..7}.val < 256` — unpacked from
      `memory_bus_entry_byte_range_perm_sound` (class #5b). -/
theorem equiv_ADDI_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Activation / opcode pins (Compliance.lean derives from ROM handshake).
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_addi : m.op r_main = OP_ADD)
    -- Main-side constructibility bundles.
    (h_main_subset : add_subset_holds m r_main)
    (h_b_core : ∀ r, ZiskFv.Airs.BinaryAdd.core_every_row b r)
    (h_addi_subset : itype_imm_subset_holds_main m r_main addi_input.imm)
    -- Lane-match for rd-write entry (deferred to Mem pilot).
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    -- Sail-side state predicates.
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addi_input.r1_val state)
    (h_input_imm : addi_input.imm = imm)
    (h_input_rd : addi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addi_input.PC)
    -- Bus-protocol structural hypotheses — pass-through.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addi_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- ============ Derive `m.m32 r_main = 0` and `m.set_pc r_main = 0`
  -- via `transpile_ADDI` ============
  have h_tr := ZiskFv.Trusted.transpile_ADDI
    m r_main (0 : Fin 32) (0 : Fin 32)
    (m.b_0 r_main) (m.b_1 r_main)
    ({ xreg := fun _ => 0#64, pc := 0#64 } : RV64State)
    h_main_active h_main_op_addi
  obtain ⟨_, h_m32, h_set_pc, _, _, _, _, _, _, _⟩ := h_tr
  -- ============ Assemble `main_row_in_addi_mode` ============
  have h_main_mode : main_row_in_addi_mode m r_main := by
    refine ⟨h_main_active, ?_, h_m32, h_set_pc⟩
    -- `OP_ADD := (10 : FGL)` definitionally.
    exact h_main_op_addi
  -- ============ Discharge the 8 e2 byte ranges ============
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    memory_bus_entry_byte_range_perm_sound e2
  -- ============ Delegate to canonical `equiv_ADDI` ============
  exact ZiskFv.Equivalence.Addi.equiv_ADDI
    state addi_input r1 rd imm m b r_main exec_row e0 e1 e2
    h_input_r1 h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_subset h_main_mode h_b_core h_addi_subset h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7

end ZiskFv.Equivalence.Compliance
