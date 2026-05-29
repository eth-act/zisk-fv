import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Binary.BinaryAddPackedCorrect
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.ZiskCircuit.Add
import ZiskFv.SailSpec.add
import ZiskFv.EquivCore.Bridge.SailStateBridge

/-!
# BinaryAdd discharge bridge

Implements *promise discharge* for the BinaryAdd-using opcode shape.

This bridge consumes pieces of the *trust ledger* —
`op_bus_perm_sound_BinaryAdd` (PLONK soundness on
`OPERATION_BUS_ID = 5000`), `binary_add_columns_in_range`
(range-check bus soundness on BinaryAdd's `bits(N)` columns), and
the `transpile_ADD` row contract (via
`Bridge.SailStateBridge.add_input_bridges_of_read_xreg`) — to
derive the `add_circuit_holds` + range facts + per-byte input
bridges that the canonical `equiv_ADD` would otherwise accept as
**promise hypotheses**. The result is a single existential delivering exactly
what the downstream `WriteValueProofs.Arith.h_rd_val_arith_add`
discharge lemma needs.

Per-opcode net effect (caller-burden ledger), measured against the
origin/main pre-pilot:

* drops `r_binary` (1)
* drops `h_circuit` (1) — split into 3 simpler pieces inside the
  bridge
* drops `h_a_range`, `h_b_range`, `h_c_range` (3) — derived from
  `binary_add_columns_in_range`
* drops `h_input_r{1,2}_main` (2) — derived inside the bridge from
  the caller's Sail-form `h_read_r{1,2}` facts via
  `transpile_ADD` (`SailStateBridge.add_input_bridges_of_read_xreg`).
  The Sail facts are already present at the canonical-theorem
  level for the `equiv_<OP>_sail` companion, so no new caller
  burden is introduced.
* adds `h_main_subset`, `h_main_mode`, `h_b_core` (3)

Net: −4 binders per BinaryAdd-shape opcode.

Per `docs/fv/known-gaps.md`'s Glossary and `CLAUDE.md`'s
*anti-laundering principle*: this bridge produces actual reduction
in the *anti-laundering metric* (verified at PR time via
`trust/scripts/check-hypothesis-count.sh` and
`trust/scripts/check-caller-burden.sh`). It is not just renaming or
splitting hypotheses.
-/

namespace ZiskFv.EquivCore.Bridge.BinaryAdd

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Add


/-- **BinaryAdd discharge bridge.** Replaces the per-opcode
    `h_circuit` + `h_a_range`/`h_b_range`/`h_c_range` +
    `h_input_r{1,2}_circuit` *promise hypotheses* with a single
    derivation chain rooted at `op_bus_perm_sound_BinaryAdd` (Phase A)
    and `binary_add_columns_in_range`.

    Caller obligations after this discharge:
    * `h_main_subset : add_subset_holds m r_main` (Main-row ADD subset
      constraints — currently caller-supplied; future work derives from
      `Valid_Main` universals).
    * `h_main_mode : main_row_in_add_mode m r_main` (activation +
      opcode pin + `m32 = 0` + `flag = 0`; currently caller-supplied,
      `transpile_ADD` covers all but `flag = 0` which matches_entry
      itself would derive — future work eliminates).
    * `h_b_core : ∀ r, core_every_row b r` (universal AIR-validity for
      BinaryAdd's per-row carry-chain constraints).
    * `h_input_r{1,2}_main` (Sail input ↔ Main lanes; in Main form).

    Outputs an existential row witness `r_binary` for BinaryAdd plus
    the full equation bundle `h_rd_val_arith_add` consumes. -/
-- add_discharge (op_bus_perm_sound route) deleted in T4-purge P3.10.

lemma add_discharge_with_match
    (m : Valid_Main FGL FGL) (b : Valid_BinaryAdd FGL FGL)
    (r_main r_binary : ℕ)
    (h_main_subset : add_subset_holds m r_main)
    (h_main_mode : main_row_in_add_mode m r_main)
    (h_b_core : core_every_row b r_binary)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryAdd b r_binary))
    (h_a_range : a_chunks_in_range b r_binary)
    (h_b_range : b_chunks_in_range b r_binary)
    (h_c_range : c_chunks_in_range b r_binary)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32) (r1_val r2_val : BitVec 64)
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
      add_circuit_holds m b r_main r_binary
      ∧ a_chunks_in_range b r_binary
      ∧ b_chunks_in_range b r_binary
      ∧ c_chunks_in_range b r_binary
      ∧ r1_val
        = BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296)
      ∧ r2_val
        = BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296) := by
  have h_active : m.is_external_op r_main = 1 := h_main_mode.1
  have h_op : m.op r_main = (10 : FGL) := h_main_mode.2.1
  have h_m32 : m.m32 r_main = 0 := h_main_mode.2.2.1
  have h_circuit : add_circuit_holds m b r_main r_binary :=
    ⟨h_main_subset, h_b_core, h_match, h_main_mode⟩
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryAdd]
    at h_lane_eqs
  obtain ⟨_, _, h_a_lo, h_a_hi, h_b_lo, h_b_hi, _, _, _, _, _, _⟩ := h_lane_eqs
  rw [h_m32] at h_a_hi h_b_hi
  simp only [one_sub_zero_mul] at h_a_hi h_b_hi
  have h_a0_val : (m.a_0 r_main).val = (b.a_0 r_binary).val :=
    congrArg Fin.val h_a_lo
  have h_a1_val : (m.a_1 r_main).val = (b.a_1 r_binary).val :=
    congrArg Fin.val h_a_hi
  have h_b0_val : (m.b_0 r_main).val = (b.b_0 r_binary).val :=
    congrArg Fin.val h_b_lo
  have h_b1_val : (m.b_1 r_main).val = (b.b_1 r_binary).val :=
    congrArg Fin.val h_b_hi
  obtain ⟨h_input_r1_main, h_input_r2_main⟩ :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.add_input_bridges_of_read_xreg
      m r_main state rs1 rs2 r1_val r2_val h_active h_op h_read_r1 h_read_r2
  have h_input_r1_circuit : r1_val
      = BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296) := by
    rw [h_input_r1_main, h_a0_val, h_a1_val]
  have h_input_r2_circuit : r2_val
      = BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296) := by
    rw [h_input_r2_main, h_b0_val, h_b1_val]
  exact ⟨h_circuit, h_a_range, h_b_range, h_c_range,
         h_input_r1_circuit, h_input_r2_circuit⟩

end ZiskFv.EquivCore.Bridge.BinaryAdd
