import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.Airs.Tables.BinaryExtensionTable
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.Bits.PackedBitVec
import ZiskFv.EquivCore.Bridge.SailStateBridge

/-!
# BinaryExtension discharge bridge

Implements *promise discharge* for the BinaryExtension-AIR-shape
opcodes (the shift family `SLL` / `SLLI` / `SRL` / `SRLI` / `SRA` /
`SRAI` and the 32-bit W variants `SLLW` / `SRLW` / `SRAW` /
`SLLIW` / `SRLIW` / `SRAIW`; plus `SEXT_B` / `SEXT_H` / `SEXT_W`
used internally by the signed-load family `LB` / `LH` / `LW`).

This bridge consumes Phase A's `op_bus_perm_sound_BinaryExtension`
(PLONK soundness on `OPERATION_BUS_ID = 5000`) and produces the
existential row witness `r_e` for the BinaryExtension AIR plus the
`matches_entry` cross-AIR consistency conjunct. The matches_entry
conjunct is what downstream `equiv_<OP>` proofs consume to
discharge their `h_match_clo` / `h_match_chi` *promise hypotheses*
without caller commitment.

What remains caller-supplied (this pass):

* The per-byte `consumer_byte_match` lookups against the
  BinaryExtension table (no `binary_extension_columns_in_range`
  range-check axiom in the trust ledger yet — adding one is a
  separate trust-ledger decision).
* The per-opcode shift-amount and signed/unsigned mode pins; the
  downstream `equiv_<OP>` proofs project these from `matches_entry`.

Per-opcode net effect (caller-burden ledger), once a downstream
`equiv_<OP>` consumes this bridge: the `h_match_clo` / `h_match_chi`
*promise hypotheses* become derivable inside the proof body rather
than caller-supplied.

(— the BinaryExtension layout cascade fix renaming
column-major reads to row-major — is the prerequisite for any
downstream consumer to project `matches_entry`'s `c_lo` / `c_hi`
conjuncts into the form `equiv_<OP>` expects. This bridge itself
is independent of that cascade because it only delivers
`matches_entry` opaque; the projection step happens at the
consumer.)
-/

namespace ZiskFv.EquivCore.Bridge.BinaryExtension

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus

/-! ## Per-opcode partial *promise discharge*

For each BinaryExtension shift opcode we expose a `<op>_discharge_partial`
entry point. Composes:

* `op_bus_perm_sound_BinaryExtension` (Phase A axiom) to *existentially*
  introduce the `r_binary` row witness plus the `matches_entry` conjunct.
* Projects `matches_entry`'s `op` / `c_lo` / `c_hi` conjuncts and rewrites
  using the caller's `h_main_op` to obtain
  `(v.op r_binary).val = OP_<op>_nat` plus the `h_match_clo` / `h_match_chi`
  sums.
* `memory_bus_entry_byte_range_perm_sound` (trust ledger) to deliver the
  8 `h_e2_*` byte ranges on the rd-write memory entry `e2`.

What this **does not** deliver (still caller-burden on the equivs):
`h_bytes` (per-byte lookup chain — needs `op_is_shift` linkage which is
not yet on `ByteLookupHypotheses`), `hc_lo_sum_lt` / `hc_hi_sum_lt`
(sum-bound — needs `main_columns_in_range`), `h_input_r1_circuit` /
`h_shift_pin` (need `op_is_shift = 1` linkage; same gap as above),
`h_lane_rd` (needs `Valid_Mem` threading).

Net effect per opcode (caller-burden ledger): drops
{`r_binary`, `h_op`, `h_match_clo`, `h_match_chi`,
 `h_e2_0..h_e2_7`} = 12 binders, adds {`h_main_active`, `h_main_op`}
= 2 binders. Net **−10 binders** per opcode. -/

section perOpcodeDischarge


-- binext_shift_discharge_partial (op_bus_perm_sound route) deleted in T4-purge P3.10.

end perOpcodeDischarge

/-! ## Per-row matches_entry → (op, c_lo, c_hi) projection helper

A consumer of `op_bus_perm_sound_BinaryExtension` (or any equivalent
delivery of a matches_entry conjunct) at a specific Main↔BinExt row
pair `(r_main, r_binary)` can use the helper below to project the
three specific equations its proof body needs (`h_op`, `h_match_clo`,
`h_match_chi`) without re-deriving them per-call.

Use this when the equiv keeps `r_binary` as a caller-supplied
parameter and a single `h_match : matches_entry ...` precondition
replaces three more-specific `h_op` / `h_match_clo` / `h_match_chi`
parameters. The replacement is a net **−2 binders** per opcode.
-/

/-- Project a single `matches_entry` predicate into its `op` /
    `c_lo` / `c_hi` conjuncts in the forms consumed by per-opcode
    `equiv_<OP>` proofs. -/
lemma project_match_op_clo_chi
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary)) :
    m.op r_main = v.op r_binary
    ∧ m.c_0 r_main = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
                     + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
                     + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
                     + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
    ∧ m.c_1 r_main = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
                     + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
                     + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
                     + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary := by
  -- Unfold matches_entry + opBus_row_Main + opBus_row_BinaryExtension once
  -- so the conjunctions are explicit, then project. Using `simp only` to
  -- prevent runaway elaboration.
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_match
  exact ⟨h_match.2.1, h_match.2.2.2.2.2.2.1, h_match.2.2.2.2.2.2.2.1⟩

/-! ## C-lane sum-bound discharge

Drops the caller-supplied `hc_lo_sum_lt` / `hc_hi_sum_lt` *promise
hypotheses* from per-opcode `equiv_<OP>` shifts. These bounds follow
mechanically from:

* `h_match_clo` / `h_match_chi` — the c-lane match equations
  (delivered by `project_match_op_clo_chi`).
* `main_columns_in_range` (trust ledger) — `(m.c_{0,1} r_main).val < 2^32`.
* `binary_extension_columns_in_range` (trust ledger) — each
  `free_in_c_{i} r_binary).val < 2^32` (the per-byte range gives the
  total < 8 * 2^32 = 2^35 < GL_prime, so the FGL sum's `.val` equals
  the Nat sum).

No new trust-ledger axiom; helper is pure derivation.
-/

private theorem c_lo_sum_eq_nat_sum_of_match
    (v : Valid_BinaryExtension FGL FGL) (r_binary : ℕ)
    (hc0 hc2 hc4 hc6 hc8 hc10 hc12 hc14 : ℕ) -- spell out positional bounds
    (h0 : (v.free_in_c_0  r_binary).val = hc0)
    (h2 : (v.free_in_c_2  r_binary).val = hc2)
    (h4 : (v.free_in_c_4  r_binary).val = hc4)
    (h6 : (v.free_in_c_6  r_binary).val = hc6)
    (h8 : (v.free_in_c_8  r_binary).val = hc8)
    (h10 : (v.free_in_c_10 r_binary).val = hc10)
    (h12 : (v.free_in_c_12 r_binary).val = hc12)
    (h14 : (v.free_in_c_14 r_binary).val = hc14)
    (hb0 : hc0 < 4294967296) (hb2 : hc2 < 4294967296)
    (hb4 : hc4 < 4294967296) (hb6 : hc6 < 4294967296)
    (hb8 : hc8 < 4294967296) (hb10 : hc10 < 4294967296)
    (hb12 : hc12 < 4294967296) (hb14 : hc14 < 4294967296) :
    (v.free_in_c_0 r_binary + v.free_in_c_2 r_binary + v.free_in_c_4 r_binary
     + v.free_in_c_6 r_binary + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
     + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary : FGL).val
      = hc0 + hc2 + hc4 + hc6 + hc8 + hc10 + hc12 + hc14 := by
  have h_cast :
      v.free_in_c_0 r_binary + v.free_in_c_2 r_binary + v.free_in_c_4 r_binary
       + v.free_in_c_6 r_binary + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
       = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
            + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
            + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
            + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val : ℕ) : FGL)) := by
    push_cast; ring
  rw [h_cast, Fin.val_natCast, h0, h2, h4, h6, h8, h10, h12, h14]
  apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega

/-! ## Input bridge / shift-pin discharge (shift family, m32 = 0)

For the 64-bit register-variant shifts (SLL / SRL / SRA) and their
immediate siblings (SLLI / SRLI / SRAI), all of which have m32 = 0 on
the Main row, derive the packed-a-byte form of `r1_val` and the
shift-pin `r2_val.toNat % 64 = (v.free_in_b).val % 64` (or the
immediate analogue) from:

* `transpile_<OP>`'s lane equalities (callable at `sail_to_rv64 state`).
* `matches_entry` (caller-supplied or projected).
* `binary_extension_op_is_shift_pin` (trust ledger) → `v.op_is_shift = 1`.
* `binary_extension_columns_in_range` (trust ledger) → per-a-byte
  ranges < 256, so the FGL packed 4-byte sum's `.val` equals the Nat
  packed sum.

No new trust-ledger axioms. -/

private theorem packed_a_lo_val_eq_of_match
    (v : Valid_BinaryExtension FGL FGL) (r_binary : ℕ)
    (ha0 : (v.free_in_a_0 r_binary).val < 256)
    (ha1 : (v.free_in_a_1 r_binary).val < 256)
    (ha2 : (v.free_in_a_2 r_binary).val < 256)
    (ha3 : (v.free_in_a_3 r_binary).val < 256) :
    (v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
      + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary : FGL).val
      = (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
        + (v.free_in_a_2 r_binary).val * 65536 + (v.free_in_a_3 r_binary).val * 16777216 := by
  have h_cast :
      v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
        + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary
        = ((((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
              + (v.free_in_a_2 r_binary).val * 65536
              + (v.free_in_a_3 r_binary).val * 16777216 : ℕ) : FGL)) := by
    push_cast; ring
  rw [h_cast, Fin.val_natCast]
  apply Nat.mod_eq_of_lt
  show _ < 18446744069414584321; omega

private theorem packed_a_hi_val_eq_of_match
    (v : Valid_BinaryExtension FGL FGL) (r_binary : ℕ)
    (ha4 : (v.free_in_a_4 r_binary).val < 256)
    (ha5 : (v.free_in_a_5 r_binary).val < 256)
    (ha6 : (v.free_in_a_6 r_binary).val < 256)
    (ha7 : (v.free_in_a_7 r_binary).val < 256) :
    (v.free_in_a_4 r_binary + 256 * v.free_in_a_5 r_binary
      + 65536 * v.free_in_a_6 r_binary + 16777216 * v.free_in_a_7 r_binary : FGL).val
      = (v.free_in_a_4 r_binary).val + (v.free_in_a_5 r_binary).val * 256
        + (v.free_in_a_6 r_binary).val * 65536 + (v.free_in_a_7 r_binary).val * 16777216 := by
  have h_cast :
      v.free_in_a_4 r_binary + 256 * v.free_in_a_5 r_binary
        + 65536 * v.free_in_a_6 r_binary + 16777216 * v.free_in_a_7 r_binary
        = ((((v.free_in_a_4 r_binary).val + (v.free_in_a_5 r_binary).val * 256
              + (v.free_in_a_6 r_binary).val * 65536
              + (v.free_in_a_7 r_binary).val * 16777216 : ℕ) : FGL)) := by
    push_cast; ring
  rw [h_cast, Fin.val_natCast]
  apply Nat.mod_eq_of_lt
  show _ < 18446744069414584321; omega

lemma packed_a_eq_of_shift_match_m32_0_of_a_range
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ) (rs1 : Fin 32) (r1_val : BitVec 64)
    (h_m32 : m.m32 r_main = 0)
    (h_a_lo_t : m.a_0 r_main = lane_lo ((SailStateBridge.sail_to_rv64 state).xreg rs1))
    (h_a_hi_t : m.a_1 r_main = lane_hi ((SailStateBridge.sail_to_rv64 state).xreg rs1))
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary))
    (h_a_range : ZiskFv.Airs.BinaryExtension.a_bytes_in_range v r_binary) :
    r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936) := by
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := h_a_range
  have h_r1_main :=
    SailStateBridge.packed_lane_eq_of_read_xreg
      state rs1 r1_val (m.a_0 r_main) (m.a_1 r_main) h_a_lo_t h_a_hi_t h_read_r1
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, h_a_lo_m, h_a_hi_m, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
  rw [h_m32] at h_a_hi_m
  simp only [one_sub_zero_mul] at h_a_hi_m
  rw [h_op_is_shift] at h_a_lo_m h_a_hi_m
  have h_a0_fgl : m.a_0 r_main
      = v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
        + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary := by
    rw [h_a_lo_m]; ring
  have h_a1_fgl : m.a_1 r_main
      = v.free_in_a_4 r_binary + 256 * v.free_in_a_5 r_binary
        + 65536 * v.free_in_a_6 r_binary + 16777216 * v.free_in_a_7 r_binary := by
    rw [h_a_hi_m]; ring
  have h_a0_val : (m.a_0 r_main).val =
      (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
      + (v.free_in_a_2 r_binary).val * 65536 + (v.free_in_a_3 r_binary).val * 16777216 := by
    rw [h_a0_fgl]
    exact packed_a_lo_val_eq_of_match v r_binary ha0 ha1 ha2 ha3
  have h_a1_val : (m.a_1 r_main).val =
      (v.free_in_a_4 r_binary).val + (v.free_in_a_5 r_binary).val * 256
      + (v.free_in_a_6 r_binary).val * 65536 + (v.free_in_a_7 r_binary).val * 16777216 := by
    rw [h_a1_fgl]
    exact packed_a_hi_val_eq_of_match v r_binary ha4 ha5 ha6 ha7
  rw [h_r1_main]
  apply congrArg (BitVec.ofNat 64)
  rw [h_a0_val, h_a1_val]
  ring

/-- Variant of `shift_pin_eq_of_shift_match_m32_0` whose no-wrap bound for
    the BinaryExtension-local `b_0` column is supplied by the shift-specific
    Clean range witness rather than by `binary_extension_columns_in_range`.
    The `free_in_b < 256` fact comes from the exact static
    BinaryExtensionTable row witnesses. -/
lemma shift_pin_eq_of_shift_match_m32_0_of_b0_range
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ) (rs2 : Fin 32) (r2_val : BitVec 64)
    (h_m32 : m.m32 r_main = 0)
    (h_b_lo_t : m.b_0 r_main = lane_lo ((SailStateBridge.sail_to_rv64 state).xreg rs2))
    (h_b_hi_t : m.b_1 r_main = lane_hi ((SailStateBridge.sail_to_rv64 state).xreg rs2))
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary))
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes)
    (h_b0_lt : (v.b_0 r_binary).val < 2 ^ 24) :
    r2_val.toNat % 64 = (v.free_in_b r_binary).val % 64 := by
  have h_b_main : (v.free_in_b r_binary).val < 256 := by
    have h := h_wfs.1.1.2.2
    simpa [h_bytes.h0.2.2.2.2.1] using h
  have h_r2_main :=
    SailStateBridge.packed_lane_eq_of_read_xreg
      state rs2 r2_val (m.b_0 r_main) (m.b_1 r_main) h_b_lo_t h_b_hi_t h_read_r2
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_lane_eqs
  rw [h_op_is_shift] at h_b_lo_m
  have h_b0_fgl : m.b_0 r_main = v.free_in_b r_binary + 256 * v.b_0 r_binary := by
    rw [h_b_lo_m]; ring
  rw [h_r2_main]
  rw [BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : (64 : ℕ) ∣ 2^64)]
  have h_step : ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) % 64
              = (m.b_0 r_main).val % 64 := by omega
  rw [h_step]
  have h_b0_val : (m.b_0 r_main).val
      = (v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val := by
    rw [h_b0_fgl]
    have h_cast : v.free_in_b r_binary + 256 * v.b_0 r_binary
        = ((((v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    show _ < 18446744069414584321
    omega
  rw [h_b0_val]
  omega

/-- Variant of `shift_pin_immediate_eq_of_shift_match` whose no-wrap bound
    for the BinaryExtension-local `b_0` column is supplied by the
    shift-specific Clean range witness, while `free_in_b < 256` comes from
    the exact static BinaryExtensionTable byte witnesses. -/
lemma shift_pin_immediate_eq_of_shift_match_of_b0_range
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ) (shamt : BitVec 6)
    (h_b_lo_t : m.b_0 r_main = shamt_b_lo shamt)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary))
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes)
    (h_b0_lt : (v.b_0 r_binary).val < 2 ^ 24) :
    shamt.toNat = (v.free_in_b r_binary).val % 64 := by
  have h_b_main : (v.free_in_b r_binary).val < 256 := by
    have h := h_wfs.1.1.2.2
    simpa [h_bytes.h0.2.2.2.2.1] using h
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_lane_eqs
  rw [h_op_is_shift] at h_b_lo_m
  have h_b0_fgl : m.b_0 r_main = v.free_in_b r_binary + 256 * v.b_0 r_binary := by
    rw [h_b_lo_m]; ring
  have h_shamt_eq : shamt_b_lo shamt = v.free_in_b r_binary + 256 * v.b_0 r_binary := by
    rw [← h_b_lo_t, h_b0_fgl]
  have h_lhs_val : (shamt_b_lo shamt : FGL).val = shamt.toNat := by
    simp [shamt_b_lo]
  have h_rhs_val : (v.free_in_b r_binary + 256 * v.b_0 r_binary : FGL).val
      = (v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val := by
    have h_cast : v.free_in_b r_binary + 256 * v.b_0 r_binary
        = ((((v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    show _ < 18446744069414584321
    omega
  have h_shamt_val : shamt.toNat
      = (v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val := by
    have h := congr_arg Fin.val h_shamt_eq
    rw [h_lhs_val, h_rhs_val] at h
    exact h
  have h_shamt_lt : shamt.toNat < 64 := shamt.isLt
  have : shamt.toNat = shamt.toNat % 64 := (Nat.mod_eq_of_lt h_shamt_lt).symm
  rw [this, h_shamt_val]
  omega

/-! ## Input bridge / shift-pin discharge (shift family, m32 = 1, W variants)

For the 32-bit W-variant shifts (SLLW/SRLW/SRAW/SLLIW/SRLIW/SRAIW),
m32 = 1 collapses `(1 - m32) * m.a_1` to 0 on the matches_entry a_hi
conjunct, pinning `e.b_1 = 0` (since with op_is_shift = 1 the RHS is
`a1`). The 4-byte lo-half packed form is what the W-variant equivs
consume (as `h_input_r1_extract`). -/

/-- Variant of `packed_a_lo32_eq_of_shift_match_m32_1` whose a-byte
    bounds are supplied by the exact static BinaryExtensionTable witness. -/
lemma packed_a_lo32_eq_of_shift_match_m32_1_of_a_range
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ) (rs1 : Fin 32) (r1_val : BitVec 64)
    (h_m32 : m.m32 r_main = 1)
    (h_a_lo_t : m.a_0 r_main = lane_lo ((SailStateBridge.sail_to_rv64 state).xreg rs1))
    (h_a_hi_t : m.a_1 r_main = lane_hi ((SailStateBridge.sail_to_rv64 state).xreg rs1))
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary))
    (h_a_range : ZiskFv.Airs.BinaryExtension.a_bytes_in_range v r_binary) :
    (Sail.BitVec.extractLsb r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
          + (v.free_in_a_2 r_binary).val * 65536
          + (v.free_in_a_3 r_binary).val * 16777216) % 2^32 := by
  obtain ⟨ha0, ha1, ha2, ha3, _, _, _, _⟩ := h_a_range
  have h_r1_main :=
    SailStateBridge.packed_lane_eq_of_read_xreg
      state rs1 r1_val (m.a_0 r_main) (m.a_1 r_main) h_a_lo_t h_a_hi_t h_read_r1
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, h_a_lo_m, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
  rw [h_op_is_shift] at h_a_lo_m
  have h_a0_fgl : m.a_0 r_main
      = v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
        + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary := by
    rw [h_a_lo_m]; ring
  have h_a0_val : (m.a_0 r_main).val =
      (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
      + (v.free_in_a_2 r_binary).val * 65536 + (v.free_in_a_3 r_binary).val * 16777216 := by
    rw [h_a0_fgl]
    exact packed_a_lo_val_eq_of_match v r_binary ha0 ha1 ha2 ha3
  rw [h_r1_main]
  have h_extract_eq :
      (Sail.BitVec.extractLsb
        (BitVec.ofNat 64
          ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296)) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) % 2^32 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
          BitVec.toNat_ofNat]
  rw [h_extract_eq, h_a0_val]
  have h_a0_lt : (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
        + (v.free_in_a_2 r_binary).val * 65536 + (v.free_in_a_3 r_binary).val * 16777216
        < 4294967296 := by omega
  omega

/-- Variant of `shift_pin_w_eq_of_shift_match` whose no-wrap bound for
    `b_0` is supplied by the shift-specific Clean range witness. -/
lemma shift_pin_w_eq_of_shift_match_of_b0_range
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ) (rs2 : Fin 32) (r2_val : BitVec 64)
    (h_b_lo_t : m.b_0 r_main = lane_lo ((SailStateBridge.sail_to_rv64 state).xreg rs2))
    (h_b_hi_t : m.b_1 r_main = lane_hi ((SailStateBridge.sail_to_rv64 state).xreg rs2))
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary))
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes)
    (h_b0_lt : (v.b_0 r_binary).val < 2 ^ 24) :
    (Sail.BitVec.extractLsb r2_val 31 0 : BitVec (31 - 0 + 1)).toNat % 32
      = (v.free_in_b r_binary).val % 32 := by
  have h_b_main : (v.free_in_b r_binary).val < 256 := by
    have h := h_wfs.1.1.2.2
    simpa [h_bytes.h0.2.2.2.2.1] using h
  have h_r2_main :=
    SailStateBridge.packed_lane_eq_of_read_xreg
      state rs2 r2_val (m.b_0 r_main) (m.b_1 r_main) h_b_lo_t h_b_hi_t h_read_r2
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_lane_eqs
  rw [h_op_is_shift] at h_b_lo_m
  have h_b0_fgl : m.b_0 r_main = v.free_in_b r_binary + 256 * v.b_0 r_binary := by
    rw [h_b_lo_m]; ring
  have h_b0_val : (m.b_0 r_main).val
      = (v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val := by
    rw [h_b0_fgl]
    have h_cast : v.free_in_b r_binary + 256 * v.b_0 r_binary
        = ((((v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    show _ < 18446744069414584321
    omega
  rw [h_r2_main]
  have h_extract_eq :
      (Sail.BitVec.extractLsb
        (BitVec.ofNat 64
          ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296)) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) % 2^32 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
          BitVec.toNat_ofNat]
  rw [h_extract_eq, h_b0_val]
  omega

/-- Variant of `shift_pin_w_immediate_eq_of_shift_match` whose no-wrap
    bound for `b_0` is supplied by the shift-specific Clean range witness. -/
lemma shift_pin_w_immediate_eq_of_shift_match_of_b0_range
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ) (shamt : BitVec 5)
    (h_b_lo_t : m.b_0 r_main = shamt_w_b_lo shamt)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary))
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes)
    (h_b0_lt : (v.b_0 r_binary).val < 2 ^ 24) :
    shamt.toNat = (v.free_in_b r_binary).val % 32 := by
  have h_b_main : (v.free_in_b r_binary).val < 256 := by
    have h := h_wfs.1.1.2.2
    simpa [h_bytes.h0.2.2.2.2.1] using h
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_lane_eqs
  rw [h_op_is_shift] at h_b_lo_m
  have h_b0_fgl : m.b_0 r_main = v.free_in_b r_binary + 256 * v.b_0 r_binary := by
    rw [h_b_lo_m]; ring
  have h_shamt_eq : shamt_w_b_lo shamt = v.free_in_b r_binary + 256 * v.b_0 r_binary := by
    rw [← h_b_lo_t, h_b0_fgl]
  have h_lhs_val : (shamt_w_b_lo shamt : FGL).val = shamt.toNat := by
    simp [shamt_w_b_lo]
  have h_rhs_val : (v.free_in_b r_binary + 256 * v.b_0 r_binary : FGL).val
      = (v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val := by
    have h_cast : v.free_in_b r_binary + 256 * v.b_0 r_binary
        = ((((v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    show _ < 18446744069414584321
    omega
  have h_shamt_val : shamt.toNat
      = (v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val := by
    have h := congr_arg Fin.val h_shamt_eq
    rw [h_lhs_val, h_rhs_val] at h
    exact h
  have h_shamt_lt : shamt.toNat < 32 := shamt.isLt
  have : shamt.toNat = shamt.toNat % 32 := (Nat.mod_eq_of_lt h_shamt_lt).symm
  rw [this, h_shamt_val]
  omega

/-! ## SEXT-mode lane-match bridge (signed loads LB / LH / LW)

For the three sign-extend opcodes `SEXT_B` / `SEXT_H` / `SEXT_W`
consumed by the signed-load family, the BinaryExtension AIR has
`op_is_shift = 0` (pinned by `binary_extension_op_is_shift_pin`).
Under that flag, the BinExt bus row's `b_lo` lane reduces to
`a0 = free_in_a_0 + 256 * free_in_a_1 + 65536 * free_in_a_2 + 16777216 *
free_in_a_3` (per `opBus_row_BinaryExtension`'s definition).

Composing with `main_sext_load_emission_bundle`'s
`m.b_0 r_main = memory_entry_lo e1 = e1.value_0`, the op-bus
permutation handshake `m.b_0 r_main = BinExt.b_lo = a0_packed`
yields the FGL equation
`free_in_a_0 + 256*free_in_a_1 + 65536*free_in_a_2 + 16777216*free_in_a_3
 = e1.value_0`.

Both sides have all bytes < 256: BinExt cells from
`binary_extension_columns_in_range`; the chunk side decomposes via
`bytes_of_chunk_packing` under `e1.value_0.val < 2^32` (chunk-range
from `memory_bus_entry_chunks_range_perm_sound`). The FGL equation
lifts to ℕ, and base-256 uniqueness extracts the per-byte equalities
`(v.free_in_a_i r_binary).val = (byteAt e1 i).val` for
i ∈ {0, 1, 2, 3} — the exact promise hypotheses
(`h_a0_match`..`h_a3_match`) consumed by `equiv_LW`. LB consumes
only `h_a0_match`; LH consumes `h_a0_match` and `h_a1_match`; LW
consumes all four.

No new trust-ledger axioms. Pure-Lean composition of:
* `op_bus_perm_sound_BinaryExtension` (class #4)
* `main_sext_load_emission_bundle` (class #4)
* `binary_extension_op_is_shift_pin` (class #6)
* `binary_extension_columns_in_range` (class #6)
* `memory_bus_entry_chunks_range_perm_sound` (class #5b).
-/

/-- **Base-256 four-byte uniqueness.** A Nat-valued base-256
    pack-of-four uniquely decomposes when all eight bytes are
    `< 256`. -/
private theorem byte_pack4_inj
    (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ)
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (h : a0 + a1 * 256 + a2 * 65536 + a3 * 16777216
       = b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Static-table variant of `sext_lane_match_bytes_eq_of_match`.

The BinExt byte ranges come from the exact `BinaryExtensionTable`
provider rows in `h_wfs`. The memory chunk range needed for the byte-pack
identity is derived after the op-bus equality pins `e1.value_0` to the
packed four-byte BinExt input, so this route does not consume
`binary_extension_columns_in_range` or memory-bus chunk range soundness. -/
lemma sext_lane_match_bytes_eq_of_match_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ) (e1 : Interaction.MemoryBusEntry FGL)
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes)
    (h_main_b0_eq : m.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1)
    (h_op_is_shift_zero : v.op_is_shift r_binary = 0)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary)) :
    (v.free_in_a_0 r_binary).val = (ZiskFv.Channels.MemoryBusBytes.byteAt e1 0).val
    ∧ (v.free_in_a_1 r_binary).val = (ZiskFv.Channels.MemoryBusBytes.byteAt e1 1).val
    ∧ (v.free_in_a_2 r_binary).val = (ZiskFv.Channels.MemoryBusBytes.byteAt e1 2).val
    ∧ (v.free_in_a_3 r_binary).val = (ZiskFv.Channels.MemoryBusBytes.byteAt e1 3).val := by
  obtain ⟨e0, ⟨_, _, _, ha0_eq, _, _, _⟩,
         e1b, ⟨_, _, _, ha1_eq, _, _, _⟩,
         e2, ⟨_, _, _, ha2_eq, _, _, _⟩,
         e3, ⟨_, _, _, ha3_eq, _, _, _⟩,
         _, _, _, _, _, _, _, _⟩ := h_bytes
  have ha0 : (v.free_in_a_0 r_binary).val < 256 := by
    have h := h_wfs.1.1.1
    simpa [ha0_eq] using h
  have ha1 : (v.free_in_a_1 r_binary).val < 256 := by
    have h := h_wfs.2.1.1.1
    simpa [ha1_eq] using h
  have ha2 : (v.free_in_a_2 r_binary).val < 256 := by
    have h := h_wfs.2.2.1.1.1
    simpa [ha2_eq] using h
  have ha3 : (v.free_in_a_3 r_binary).val < 256 := by
    have h := h_wfs.2.2.2.1.1.1
    simpa [ha3_eq] using h
  have he0 : (ZiskFv.Channels.MemoryBusBytes.byteAt e1 0).val < 256 := by
    unfold ZiskFv.Channels.MemoryBusBytes.byteAt
    simp only [show (0 : ℕ) < 4 from by decide, if_true]
    exact ZiskFv.Channels.MemoryBusBytes.byteOf_val_lt_256 _ _
  have he1 : (ZiskFv.Channels.MemoryBusBytes.byteAt e1 1).val < 256 := by
    unfold ZiskFv.Channels.MemoryBusBytes.byteAt
    simp only [show (1 : ℕ) < 4 from by decide, if_true]
    exact ZiskFv.Channels.MemoryBusBytes.byteOf_val_lt_256 _ _
  have he2 : (ZiskFv.Channels.MemoryBusBytes.byteAt e1 2).val < 256 := by
    unfold ZiskFv.Channels.MemoryBusBytes.byteAt
    simp only [show (2 : ℕ) < 4 from by decide, if_true]
    exact ZiskFv.Channels.MemoryBusBytes.byteOf_val_lt_256 _ _
  have he3 : (ZiskFv.Channels.MemoryBusBytes.byteAt e1 3).val < 256 := by
    unfold ZiskFv.Channels.MemoryBusBytes.byteAt
    simp only [show (3 : ℕ) < 4 from by decide, if_true]
    exact ZiskFv.Channels.MemoryBusBytes.byteOf_val_lt_256 _ _
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_lane_eqs
  rw [h_op_is_shift_zero] at h_b_lo_m
  have h_b0_fgl : m.b_0 r_main
      = v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
        + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary := by
    rw [h_b_lo_m]; ring
  have h_eq_chunk :
      (v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
        + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary : FGL)
      = e1.value_0 := by
    rw [← h_b0_fgl, h_main_b0_eq]
    rfl
  have h_lhs_val :
      (v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
        + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary : FGL).val
      = (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
        + (v.free_in_a_2 r_binary).val * 65536
        + (v.free_in_a_3 r_binary).val * 16777216 :=
    packed_a_lo_val_eq_of_match v r_binary ha0 ha1 ha2 ha3
  have h_value_eq := congr_arg Fin.val h_eq_chunk
  rw [h_lhs_val] at h_value_eq
  have h_v0_lt : e1.value_0.val < 4294967296 := by
    rw [← h_value_eq]
    omega
  have h_eq_fgl :
      (v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
        + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary : FGL)
      = ZiskFv.Channels.MemoryBusBytes.byteAt e1 0
        + ZiskFv.Channels.MemoryBusBytes.byteAt e1 1 * 256
        + ZiskFv.Channels.MemoryBusBytes.byteAt e1 2 * 65536
        + ZiskFv.Channels.MemoryBusBytes.byteAt e1 3 * 16777216 := by
    rw [h_eq_chunk]
    have hpack := ZiskFv.Channels.MemoryBusBytes.bytes_of_chunk_packing
                    e1.value_0 h_v0_lt
    have hb0 : ZiskFv.Channels.MemoryBusBytes.byteAt e1 0
              = ZiskFv.Channels.MemoryBusBytes.byteOf e1.value_0 0 := by
      unfold ZiskFv.Channels.MemoryBusBytes.byteAt
      simp only [show (0 : ℕ) < 4 from by decide, if_true]
    have hb1 : ZiskFv.Channels.MemoryBusBytes.byteAt e1 1
              = ZiskFv.Channels.MemoryBusBytes.byteOf e1.value_0 1 := by
      unfold ZiskFv.Channels.MemoryBusBytes.byteAt
      simp only [show (1 : ℕ) < 4 from by decide, if_true]
    have hb2 : ZiskFv.Channels.MemoryBusBytes.byteAt e1 2
              = ZiskFv.Channels.MemoryBusBytes.byteOf e1.value_0 2 := by
      unfold ZiskFv.Channels.MemoryBusBytes.byteAt
      simp only [show (2 : ℕ) < 4 from by decide, if_true]
    have hb3 : ZiskFv.Channels.MemoryBusBytes.byteAt e1 3
              = ZiskFv.Channels.MemoryBusBytes.byteOf e1.value_0 3 := by
      unfold ZiskFv.Channels.MemoryBusBytes.byteAt
      simp only [show (3 : ℕ) < 4 from by decide, if_true]
    rw [hb0, hb1, hb2, hb3]
    exact hpack
  have h_rhs_val :
      (ZiskFv.Channels.MemoryBusBytes.byteAt e1 0
        + ZiskFv.Channels.MemoryBusBytes.byteAt e1 1 * 256
        + ZiskFv.Channels.MemoryBusBytes.byteAt e1 2 * 65536
        + ZiskFv.Channels.MemoryBusBytes.byteAt e1 3 * 16777216 : FGL).val
      = (ZiskFv.Channels.MemoryBusBytes.byteAt e1 0).val
        + (ZiskFv.Channels.MemoryBusBytes.byteAt e1 1).val * 256
        + (ZiskFv.Channels.MemoryBusBytes.byteAt e1 2).val * 65536
        + (ZiskFv.Channels.MemoryBusBytes.byteAt e1 3).val * 16777216 :=
    ZiskFv.PackedBitVec.fgl_packed_4bytes_val_of_byte_range _ _ _ _ he0 he1 he2 he3
  have h_val_eq := congr_arg Fin.val h_eq_fgl
  rw [h_lhs_val, h_rhs_val] at h_val_eq
  exact byte_pack4_inj _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3
    he0 he1 he2 he3 h_val_eq

end ZiskFv.EquivCore.Bridge.BinaryExtension
