import Mathlib

import ZiskFv.Circuit
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Binary.BinaryAddRanges
import ZiskFv.Airs.Binary.BinaryAddPackedCorrect
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.ZiskCircuit.Add
import ZiskFv.SailSpec.add
import ZiskFv.Equivalence_v1.Bridge.SailStateBridge

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

namespace ZiskFv.Equivalence_v1.Bridge.BinaryAdd

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Add

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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
lemma add_discharge
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main : ℕ)
    (h_main_subset : add_subset_holds m r_main)
    (h_main_mode : main_row_in_add_mode m r_main)
    (h_b_core : ∀ r, ZiskFv.Airs.BinaryAdd.core_every_row b r)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32) (r1_val r2_val : BitVec 64)
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    ∃ r_binary,
      add_circuit_holds m b r_main r_binary
      ∧ a_chunks_in_range b r_binary
      ∧ b_chunks_in_range b r_binary
      ∧ c_chunks_in_range b r_binary
      ∧ r1_val
        = BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296)
      ∧ r2_val
        = BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296) := by
  -- Project main_row_in_add_mode for the OpBus axiom call.
  have h_active : m.is_external_op r_main = 1 := h_main_mode.1
  have h_op : m.op r_main = (10 : FGL) := h_main_mode.2.1
  have h_m32 : m.m32 r_main = 0 := h_main_mode.2.2.1
  -- Phase A's OpBus permutation axiom delivers the existential
  -- BinaryAdd row witness with matches_entry.
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryAdd m b r_main h_active h_op
  -- Reconstruct add_circuit_holds at the existential row.
  have h_circuit : add_circuit_holds m b r_main r_binary :=
    ⟨h_main_subset, h_b_core r_binary, h_match, h_main_mode⟩
  -- Range facts come from binary_add_columns_in_range
  -- axiom (range-check bus lookup soundness, no caller hypothesis).
  have h_a_range : a_chunks_in_range b r_binary :=
    ⟨ba_a_lo_lt_2_32 b r_binary, ba_a_hi_lt_2_32 b r_binary⟩
  have h_b_range : b_chunks_in_range b r_binary :=
    ⟨ba_b_lo_lt_2_32 b r_binary, ba_b_hi_lt_2_32 b r_binary⟩
  have h_c_range : c_chunks_in_range b r_binary :=
    ⟨ba_c_chunk_0_lt_2_16 b r_binary,
     ba_c_chunk_1_lt_2_16 b r_binary,
     ba_c_chunk_2_lt_2_16 b r_binary,
     ba_c_chunk_3_lt_2_16 b r_binary⟩
  -- Lane equalities from matches_entry's a_lo/a_hi/b_lo/b_hi
  -- conjuncts. The (1 - m.m32) factor on the high lanes collapses
  -- once `h_m32 : m.m32 r_main = 0` is rewritten in.
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
  -- Derive Main-form input bridges from transpile_ADD via
  -- SailStateBridge. The Sail-form `read_xreg` facts the caller
  -- supplies (already present in every `equiv_<OP>` for the
  -- `equiv_<OP>_sail` companion) are sufficient.
  obtain ⟨h_input_r1_main, h_input_r2_main⟩ :=
    ZiskFv.Equivalence_v1.Bridge.SailStateBridge.add_input_bridges_of_read_xreg
      m r_main state rs1 rs2 r1_val r2_val h_active h_op h_read_r1 h_read_r2
  -- Translate the Main-form input bridges to BinaryAdd-row form.
  have h_input_r1_circuit : r1_val
      = BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296) := by
    rw [h_input_r1_main, h_a0_val, h_a1_val]
  have h_input_r2_circuit : r2_val
      = BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296) := by
    rw [h_input_r2_main, h_b0_val, h_b1_val]
  exact ⟨r_binary, h_circuit, h_a_range, h_b_range, h_c_range,
         h_input_r1_circuit, h_input_r2_circuit⟩

/-! ## Narrow helper for the discharge path (keeps `r_binary`
    as caller-supplied) — analogue of `Bridge.Binary.byte_ranges_at_holds`

The 3 BinaryAdd chunk-range predicates (`a_chunks_in_range`,
`b_chunks_in_range`, `c_chunks_in_range`) at any caller-supplied
`r_binary` are all derivable from `binary_add_columns_in_range`
(axiom). This helper packages exactly that for the
discharge of ADDI and other BinaryAdd-shape opcodes
that retain `r_binary` as a parameter.
-/

/-- Discharge the 3 BinaryAdd chunk-range *promise hypotheses* at any
    caller-supplied row. Pure derivation from
    `binary_add_columns_in_range`; no caller hypothesis needed. -/
lemma chunk_ranges_at_holds (b : Valid_BinaryAdd C FGL FGL) (r : ℕ) :
    a_chunks_in_range b r ∧ b_chunks_in_range b r ∧ c_chunks_in_range b r :=
  ⟨⟨ba_a_lo_lt_2_32 b r, ba_a_hi_lt_2_32 b r⟩,
   ⟨ba_b_lo_lt_2_32 b r, ba_b_hi_lt_2_32 b r⟩,
   ⟨ba_c_chunk_0_lt_2_16 b r, ba_c_chunk_1_lt_2_16 b r,
    ba_c_chunk_2_lt_2_16 b r, ba_c_chunk_3_lt_2_16 b r⟩⟩

end ZiskFv.Equivalence_v1.Bridge.BinaryAdd
