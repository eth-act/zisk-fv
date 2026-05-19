import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Main.Ranges
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.Tables.BinaryExtensionTable
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Equivalence_v1.Bridge.SailStateBridge

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

namespace ZiskFv.Equivalence_v1.Bridge.BinaryExtension

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **BinaryExtension discharge bridge.** Replaces
    the per-opcode `r_e` row-index parameter + `h_match` cross-AIR
    *promise hypothesis* with a derivation rooted at
    `op_bus_perm_sound_BinaryExtension` (Phase A).

    Caller obligations after this discharge:
    * `h_main_active : m.is_external_op r_main = 1`
    * `h_main_op_in_set` (the 9-way disjunction in the OpBus axiom;
      each call site pins a specific shift / sign-extend literal).

    Outputs: existential `r_e` + `matches_entry`. -/
lemma binext_discharge
    (m : Valid_Main C FGL FGL) (e : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = 0x21 ∨ m.op r_main = 0x22 ∨ m.op r_main = 0x23
               ∨ m.op r_main = 0x24 ∨ m.op r_main = 0x25 ∨ m.op r_main = 0x26
               ∨ m.op r_main = 0x27 ∨ m.op r_main = 0x28 ∨ m.op r_main = 0x29) :
    ∃ r_e,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension e r_e) :=
  op_bus_perm_sound_BinaryExtension m e r_main h_main_active h_main_op

/-- **BinaryExtension byte-range discharge at a specific row.**
    Derived from `binary_extension_columns_in_range` — no caller
    hypothesis needed. Mirrors `Bridge.Binary.byte_ranges_at_holds`.
    Consumed by downstream `equiv_<OP>` proofs that have already
    obtained a concrete `r_e` row index from `binext_discharge`
    (or from caller-supplied existential witnessing). -/
lemma byte_ranges_at_holds (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_a_0 r).val < 256 ∧ (e.free_in_a_1 r).val < 256
  ∧ (e.free_in_a_2 r).val < 256 ∧ (e.free_in_a_3 r).val < 256
  ∧ (e.free_in_a_4 r).val < 256 ∧ (e.free_in_a_5 r).val < 256
  ∧ (e.free_in_a_6 r).val < 256 ∧ (e.free_in_a_7 r).val < 256
  ∧ (e.free_in_b r).val < 256 :=
  ⟨be_a_0_lt_256 e r, be_a_1_lt_256 e r, be_a_2_lt_256 e r, be_a_3_lt_256 e r,
   be_a_4_lt_256 e r, be_a_5_lt_256 e r, be_a_6_lt_256 e r, be_a_7_lt_256 e r,
   be_b_lt_256 e r⟩

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

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- Shared partial discharge: existential `r_binary` + op-pin (in `.val`
    form) + `c_lo`/`c_hi` match equations + 8 e2 byte ranges. -/
private theorem binext_shift_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (op_nat : ℕ) (op_fgl : FGL)
    (h_op_val : op_fgl.val = op_nat)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = op_fgl)
    (h_main_op_in_set : m.op r_main = 0x21 ∨ m.op r_main = 0x22 ∨ m.op r_main = 0x23
                     ∨ m.op r_main = 0x24 ∨ m.op r_main = 0x25 ∨ m.op r_main = 0x26
                     ∨ m.op r_main = 0x27 ∨ m.op r_main = 0x28 ∨ m.op r_main = 0x29) :
    ∃ r_binary,
      (v.op r_binary).val = op_nat
      ∧ m.c_0 r_main = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
                       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
                       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
                       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
      ∧ m.c_1 r_main = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
                       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
                       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
                       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
      ∧ e2.x0.val < 256 ∧ e2.x1.val < 256 ∧ e2.x2.val < 256 ∧ e2.x3.val < 256
      ∧ e2.x4.val < 256 ∧ e2.x5.val < 256 ∧ e2.x6.val < 256 ∧ e2.x7.val < 256 := by
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryExtension m v r_main h_main_active h_main_op_in_set
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  refine ⟨r_binary, ?_, ?_, ?_, h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5,
          h_e2_6, h_e2_7⟩
  · -- op match: (v.op r_binary).val = op_nat
    have h_op_eq : m.op r_main = v.op r_binary := by
      simpa using h_match.2.1
    have h_op_fgl : v.op r_binary = op_fgl := by rw [← h_op_eq, h_main_op]
    rw [h_op_fgl]; exact h_op_val
  · -- c_lo match
    have h := h_match.2.2.2.2.2.2.1
    simpa using h
  · -- c_hi match
    have h := h_match.2.2.2.2.2.2.2.1
    simpa using h

/-- **SLL partial discharge.** `op = 0x21`. -/
lemma sll_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL
      ∧ m.c_0 r_main = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
                       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
                       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
                       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
      ∧ m.c_1 r_main = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
                       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
                       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
                       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
      ∧ e2.x0.val < 256 ∧ e2.x1.val < 256 ∧ e2.x2.val < 256 ∧ e2.x3.val < 256
      ∧ e2.x4.val < 256 ∧ e2.x5.val < 256 ∧ e2.x6.val < 256 ∧ e2.x7.val < 256 :=
  binext_shift_discharge_partial m v r_main e2
    ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL ZiskFv.Trusted.OP_SLL
    (by decide) h_main_active h_main_op (Or.inl h_main_op)

/-- **SRL partial discharge.** `op = 0x22`. -/
lemma srl_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL
      ∧ m.c_0 r_main = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
                       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
                       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
                       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
      ∧ m.c_1 r_main = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
                       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
                       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
                       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
      ∧ e2.x0.val < 256 ∧ e2.x1.val < 256 ∧ e2.x2.val < 256 ∧ e2.x3.val < 256
      ∧ e2.x4.val < 256 ∧ e2.x5.val < 256 ∧ e2.x6.val < 256 ∧ e2.x7.val < 256 :=
  binext_shift_discharge_partial m v r_main e2
    ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL ZiskFv.Trusted.OP_SRL
    (by decide) h_main_active h_main_op (Or.inr (Or.inl h_main_op))

/-- **SRA partial discharge.** `op = 0x23`. -/
lemma sra_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA
      ∧ m.c_0 r_main = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
                       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
                       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
                       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
      ∧ m.c_1 r_main = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
                       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
                       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
                       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
      ∧ e2.x0.val < 256 ∧ e2.x1.val < 256 ∧ e2.x2.val < 256 ∧ e2.x3.val < 256
      ∧ e2.x4.val < 256 ∧ e2.x5.val < 256 ∧ e2.x6.val < 256 ∧ e2.x7.val < 256 :=
  binext_shift_discharge_partial m v r_main e2
    ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA ZiskFv.Trusted.OP_SRA
    (by decide) h_main_active h_main_op (Or.inr (Or.inr (Or.inl h_main_op)))

/-- **SLLW (SLL_W) partial discharge.** `op = 0x24`. -/
lemma sllw_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL_W) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W
      ∧ m.c_0 r_main = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
                       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
                       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
                       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
      ∧ m.c_1 r_main = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
                       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
                       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
                       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
      ∧ e2.x0.val < 256 ∧ e2.x1.val < 256 ∧ e2.x2.val < 256 ∧ e2.x3.val < 256
      ∧ e2.x4.val < 256 ∧ e2.x5.val < 256 ∧ e2.x6.val < 256 ∧ e2.x7.val < 256 :=
  binext_shift_discharge_partial m v r_main e2
    ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W ZiskFv.Trusted.OP_SLL_W
    (by decide) h_main_active h_main_op
    (Or.inr (Or.inr (Or.inr (Or.inl h_main_op))))

/-- **SRLW (SRL_W) partial discharge.** `op = 0x25`. -/
lemma srlw_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL_W) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL_W
      ∧ m.c_0 r_main = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
                       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
                       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
                       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
      ∧ m.c_1 r_main = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
                       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
                       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
                       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
      ∧ e2.x0.val < 256 ∧ e2.x1.val < 256 ∧ e2.x2.val < 256 ∧ e2.x3.val < 256
      ∧ e2.x4.val < 256 ∧ e2.x5.val < 256 ∧ e2.x6.val < 256 ∧ e2.x7.val < 256 :=
  binext_shift_discharge_partial m v r_main e2
    ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL_W ZiskFv.Trusted.OP_SRL_W
    (by decide) h_main_active h_main_op
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op)))))

/-- **SRAW (SRA_W) partial discharge.** `op = 0x26`. -/
lemma sraw_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA_W
      ∧ m.c_0 r_main = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
                       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
                       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
                       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
      ∧ m.c_1 r_main = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
                       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
                       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
                       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
      ∧ e2.x0.val < 256 ∧ e2.x1.val < 256 ∧ e2.x2.val < 256 ∧ e2.x3.val < 256
      ∧ e2.x4.val < 256 ∧ e2.x5.val < 256 ∧ e2.x6.val < 256 ∧ e2.x7.val < 256 :=
  binext_shift_discharge_partial m v r_main e2
    ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA_W ZiskFv.Trusted.OP_SRA_W
    (by decide) h_main_active h_main_op
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op))))))

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
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
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
    (v : Valid_BinaryExtension C FGL FGL) (r_binary : ℕ)
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

/-- **C-lo sum bound discharge.** From the c-lo bus-match equation
    (delivered by `project_match_op_clo_chi`), the `main_columns_in_range`
    bound on `m.c_0`, and the `binary_extension_columns_in_range` bounds
    on each `free_in_c_{even}`, conclude the BinExt c-lo Nat sum is
    `< 2^32`. -/
lemma hc_lo_sum_lt_of_match
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary) :
    (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
      + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
      + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
      + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val
      < 4294967296 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc0, _, hc2, _, hc4, _, hc6, _,
          hc8, _, hc10, _, hc12, _, hc14, _, _, _⟩ :=
    binary_extension_columns_in_range v r_binary
  have h_main_clo : (m.c_0 r_main).val < 4294967296 :=
    ZiskFv.Airs.Main.main_c_lo_lt_2_32 m r_main
  have h_val := congr_arg Fin.val h_match_clo
  have h_sum_eq :=
    c_lo_sum_eq_nat_sum_of_match v r_binary
      (v.free_in_c_0 r_binary).val (v.free_in_c_2 r_binary).val
      (v.free_in_c_4 r_binary).val (v.free_in_c_6 r_binary).val
      (v.free_in_c_8 r_binary).val (v.free_in_c_10 r_binary).val
      (v.free_in_c_12 r_binary).val (v.free_in_c_14 r_binary).val
      rfl rfl rfl rfl rfl rfl rfl rfl hc0 hc2 hc4 hc6 hc8 hc10 hc12 hc14
  rw [h_sum_eq] at h_val
  omega

private theorem c_hi_sum_eq_nat_sum_of_match
    (v : Valid_BinaryExtension C FGL FGL) (r_binary : ℕ)
    (hc1 hc3 hc5 hc7 hc9 hc11 hc13 hc15 : ℕ)
    (h1 : (v.free_in_c_1  r_binary).val = hc1)
    (h3 : (v.free_in_c_3  r_binary).val = hc3)
    (h5 : (v.free_in_c_5  r_binary).val = hc5)
    (h7 : (v.free_in_c_7  r_binary).val = hc7)
    (h9 : (v.free_in_c_9  r_binary).val = hc9)
    (h11 : (v.free_in_c_11 r_binary).val = hc11)
    (h13 : (v.free_in_c_13 r_binary).val = hc13)
    (h15 : (v.free_in_c_15 r_binary).val = hc15)
    (hb1 : hc1 < 4294967296) (hb3 : hc3 < 4294967296)
    (hb5 : hc5 < 4294967296) (hb7 : hc7 < 4294967296)
    (hb9 : hc9 < 4294967296) (hb11 : hc11 < 4294967296)
    (hb13 : hc13 < 4294967296) (hb15 : hc15 < 4294967296) :
    (v.free_in_c_1 r_binary + v.free_in_c_3 r_binary + v.free_in_c_5 r_binary
     + v.free_in_c_7 r_binary + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
     + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary : FGL).val
      = hc1 + hc3 + hc5 + hc7 + hc9 + hc11 + hc13 + hc15 := by
  have h_cast :
      v.free_in_c_1 r_binary + v.free_in_c_3 r_binary + v.free_in_c_5 r_binary
       + v.free_in_c_7 r_binary + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
       = ((((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
            + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
            + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
            + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
    push_cast; ring
  rw [h_cast, Fin.val_natCast, h1, h3, h5, h7, h9, h11, h13, h15]
  apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega

/-- **C-hi sum bound discharge.** Mirror of `hc_lo_sum_lt_of_match`. -/
lemma hc_hi_sum_lt_of_match
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary) :
    (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
      + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
      + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
      + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val
      < 4294967296 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hc1, _, hc3, _, hc5, _, hc7,
          _, hc9, _, hc11, _, hc13, _, hc15, _, _⟩ :=
    binary_extension_columns_in_range v r_binary
  have h_main_chi : (m.c_1 r_main).val < 4294967296 :=
    ZiskFv.Airs.Main.main_c_hi_lt_2_32 m r_main
  have h_val := congr_arg Fin.val h_match_chi
  have h_sum_eq :=
    c_hi_sum_eq_nat_sum_of_match v r_binary
      (v.free_in_c_1 r_binary).val (v.free_in_c_3 r_binary).val
      (v.free_in_c_5 r_binary).val (v.free_in_c_7 r_binary).val
      (v.free_in_c_9 r_binary).val (v.free_in_c_11 r_binary).val
      (v.free_in_c_13 r_binary).val (v.free_in_c_15 r_binary).val
      rfl rfl rfl rfl rfl rfl rfl rfl hc1 hc3 hc5 hc7 hc9 hc11 hc13 hc15
  rw [h_sum_eq] at h_val
  omega

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
    (v : Valid_BinaryExtension C FGL FGL) (r_binary : ℕ)
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
    (v : Valid_BinaryExtension C FGL FGL) (r_binary : ℕ)
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

/-- **Packed-a bridge for 64-bit shifts (m32 = 0).** Given the
    `transpile_<OP>` lane equalities (`m.a_0 = lane_lo (state.xreg rs1)`
    / `m.a_1 = lane_hi …`), the row-level `op_is_shift = 1` pin, the
    Sail register read, and the matches_entry hypothesis, derive
    `r1_val = BitVec.ofNat 64 (8-byte packed sum)`. The `m32` hypothesis
    (with `m32 = 0`) collapses the `(1 - m32) * m.a_1` factor on the
    matches_entry a_hi conjunct. -/
lemma packed_a_eq_of_shift_match_m32_0
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ) (rs1 : Fin 32) (r1_val : BitVec 64)
    (h_m32 : m.m32 r_main = 0)
    (h_a_lo_t : m.a_0 r_main = lane_lo ((SailStateBridge.sail_to_rv64 state).xreg rs1))
    (h_a_hi_t : m.a_1 r_main = lane_hi ((SailStateBridge.sail_to_rv64 state).xreg rs1))
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary)) :
    r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936) := by
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _⟩ :=
    binary_extension_columns_in_range v r_binary
  -- Sail packed form from read_xreg + transpile lanes.
  have h_r1_main :=
    SailStateBridge.packed_lane_eq_of_read_xreg
      state rs1 r1_val (m.a_0 r_main) (m.a_1 r_main) h_a_lo_t h_a_hi_t h_read_r1
  -- Project a-lane match equations.
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, h_a_lo_m, h_a_hi_m, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
  -- m32 = 0 collapses `(1 - m32) * m.a_1 = m.a_1`.
  rw [h_m32] at h_a_hi_m
  simp only [one_sub_zero_mul] at h_a_hi_m
  -- op_is_shift = 1 collapses the a_lo/a_hi RHS to the packed form.
  rw [h_op_is_shift] at h_a_lo_m h_a_hi_m
  -- Simplify `1 * (x - y) + y = x`.
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

/-- **Shift-pin bridge for 64-bit register shifts (SLL/SRL/SRA, m32 = 0).**
    Derives `r2_val.toNat % 64 = (v.free_in_b r_binary).val % 64` from
    transpile lanes (`m.b_0 = lane_lo (xreg rs2)`, `m.b_1 = lane_hi …`),
    the Sail register read, `op_is_shift = 1`, and `matches_entry`.

    Proof sketch: the packed-lane form `r2_val = BV.ofNat 64 ((m.b_0).val
    + (m.b_1).val * 2^32)` gives `r2_val.toNat = (m.b_0).val + (m.b_1).val
    * 2^32`. Since 2^32 ≡ 0 (mod 64), `r2_val.toNat % 64 = (m.b_0).val % 64`.
    From `matches_entry`'s b_lo with `op_is_shift = 1` we get
    `m.b_0 = e.free_in_b + 256 * e.b_0`. The free_in_b and b_0 byte ranges
    bound the FGL sum's `.val` so it equals `(free_in_b).val + 256 *
    (b_0).val`. Taking `% 64` and observing `256 ≡ 0 (mod 64)` finishes. -/
lemma shift_pin_eq_of_shift_match_m32_0
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ) (rs2 : Fin 32) (r2_val : BitVec 64)
    (h_m32 : m.m32 r_main = 0)
    (h_b_lo_t : m.b_0 r_main = lane_lo ((SailStateBridge.sail_to_rv64 state).xreg rs2))
    (h_b_hi_t : m.b_1 r_main = lane_hi ((SailStateBridge.sail_to_rv64 state).xreg rs2))
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary)) :
    r2_val.toNat % 64 = (v.free_in_b r_binary).val % 64 := by
  have h_b_main : (v.free_in_b r_binary).val < 256 := be_b_lt_256 v r_binary
  have h_main_b0 : (m.b_0 r_main).val < 4294967296 :=
    ZiskFv.Airs.Main.main_b_lo_lt_2_32 m r_main
  -- Sail packed form from read_xreg + transpile lanes.
  have h_r2_main :=
    SailStateBridge.packed_lane_eq_of_read_xreg
      state rs2 r2_val (m.b_0 r_main) (m.b_1 r_main) h_b_lo_t h_b_hi_t h_read_r2
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_lane_eqs
  -- op_is_shift = 1 collapses b_lo RHS.
  rw [h_op_is_shift] at h_b_lo_m
  -- Now h_b_lo_m: m.b_0 r_main = 1 * (free_in_b + 256*b_0 - a0) + a0.
  -- Simplify to free_in_b + 256 * b_0.
  have h_b0_fgl : m.b_0 r_main = v.free_in_b r_binary + 256 * v.b_0 r_binary := by
    rw [h_b_lo_m]; ring
  -- Take r2_val.toNat: from packed-lane equation r2_val = BV.ofNat 64 (m.b_0.val + m.b_1.val * 2^32).
  rw [h_r2_main]
  rw [BitVec.toNat_ofNat]
  -- Goal: ((m.b_0).val + (m.b_1).val * 2^32) % 2^64 % 64 = (v.free_in_b r_binary).val % 64
  -- 2^64 % 64 = 0 and 2^32 % 64 = 0, so the modular cascade reduces to (m.b_0).val % 64.
  -- Cleanest: `Nat.mod_mod_of_dvd` (64 | 2^64).
  rw [Nat.mod_mod_of_dvd _ (by decide : (64 : ℕ) ∣ 2^64)]
  -- Now goal: ((m.b_0).val + (m.b_1).val * 2^32) % 64 = (v.free_in_b).val % 64.
  -- 2^32 = 64 * 2^26, so (m.b_1).val * 2^32 ≡ 0 (mod 64); omega handles it.
  have h_step : ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) % 64
              = (m.b_0 r_main).val % 64 := by omega
  rw [h_step]
  -- Now goal: (m.b_0 r_main).val % 64 = (v.free_in_b r_binary).val % 64.
  -- From h_b0_fgl: m.b_0 r_main = free_in_b + 256 * b_0.
  have h_b0_val : (m.b_0 r_main).val
      = (v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val := by
    rw [h_b0_fgl]
    have h_cast : v.free_in_b r_binary + 256 * v.b_0 r_binary
        = ((((v.free_in_b r_binary).val + 256 * (v.b_0 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    -- (free_in_b).val < 256, (b_0).val < 2^32 (from binary_extension_columns_in_range)
    have h_b0_lt : (v.b_0 r_binary).val < 4294967296 := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb0, _⟩ :=
        binary_extension_columns_in_range v r_binary
      exact hb0
    show _ < 18446744069414584321
    -- (free_in_b).val < 256, (b_0).val < 2^32, so total < 256 + 256 * 2^32 < GL_prime
    omega
  rw [h_b0_val]
  omega

/-- **Shift-pin bridge for 64-bit immediate shifts (SLLI/SRLI/SRAI).**
    Derives `shamt.toNat = (v.free_in_b r_binary).val % 64` from
    `transpile_<OPI>`'s `m.b_0 = shamt_b_lo shamt`, op_is_shift = 1,
    and `matches_entry`'s `b_lo` conjunct. The shamt is a 6-bit BitVec
    so `shamt.toNat < 64`; the b_lo equation pins
    `(v.free_in_b).val + 256 * (v.b_0).val = shamt.toNat`, which
    bounds both addends and gives the mod-64 equation directly. -/
lemma shift_pin_immediate_eq_of_shift_match
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ) (shamt : BitVec 6)
    (h_b_lo_t : m.b_0 r_main = shamt_b_lo shamt)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary)) :
    shamt.toNat = (v.free_in_b r_binary).val % 64 := by
  have h_b_main : (v.free_in_b r_binary).val < 256 := be_b_lt_256 v r_binary
  have h_b0_lt : (v.b_0 r_binary).val < 4294967296 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb0, _⟩ :=
      binary_extension_columns_in_range v r_binary
    exact hb0
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_lane_eqs
  rw [h_op_is_shift] at h_b_lo_m
  have h_b0_fgl : m.b_0 r_main = v.free_in_b r_binary + 256 * v.b_0 r_binary := by
    rw [h_b_lo_m]; ring
  -- Combine with transpile: shamt_b_lo shamt = free_in_b + 256 * b_0.
  have h_shamt_eq : shamt_b_lo shamt = v.free_in_b r_binary + 256 * v.b_0 r_binary := by
    rw [← h_b_lo_t, h_b0_fgl]
  -- Take .val of both sides. `shamt_b_lo shamt = ⟨shamt.toNat, ...⟩`,
  -- so `.val = shamt.toNat`. The RHS .val = (free_in_b).val + 256 * (b_0).val.
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
  -- shamt.toNat < 64, so % 64 is identity. RHS mod 64: 256 * b_0 ≡ 0.
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

/-- **Packed-a 32-bit (extracted-lsb) bridge for W-variant shifts (m32 = 1).**
    Given transpile lanes + read_xreg + op_is_shift = 1 + matches_entry,
    derive `(extractLsb r1_val 31 0).toNat = (4 lo a-bytes packed) % 2^32`. -/
lemma packed_a_lo32_eq_of_shift_match_m32_1
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ) (rs1 : Fin 32) (r1_val : BitVec 64)
    (h_m32 : m.m32 r_main = 1)
    (h_a_lo_t : m.a_0 r_main = lane_lo ((SailStateBridge.sail_to_rv64 state).xreg rs1))
    (h_a_hi_t : m.a_1 r_main = lane_hi ((SailStateBridge.sail_to_rv64 state).xreg rs1))
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary)) :
    (Sail.BitVec.extractLsb r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
          + (v.free_in_a_2 r_binary).val * 65536
          + (v.free_in_a_3 r_binary).val * 16777216) % 2^32 := by
  obtain ⟨ha0, ha1, ha2, ha3, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _⟩ :=
    binary_extension_columns_in_range v r_binary
  -- Sail packed form from read_xreg + transpile lanes.
  have h_r1_main :=
    SailStateBridge.packed_lane_eq_of_read_xreg
      state rs1 r1_val (m.a_0 r_main) (m.a_1 r_main) h_a_lo_t h_a_hi_t h_read_r1
  -- Project a-lane match equations.
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
  -- Now: extractLsb r1 31 0 toNat = r1_val.toNat % 2^32 = (m.a_0).val.
  rw [h_r1_main]
  -- (BitVec.ofNat 64 N).extractLsb 31 0 = BitVec.ofNat 32 (N % 2^32).
  -- Actually: extractLsb _ 31 0 = ofNat 32 (toNat % 2^32) since width = 32.
  -- And (ofNat 64 N).toNat = N % 2^64. So (extractLsb (ofNat 64 N) 31 0).toNat
  -- = N % 2^64 % 2^32 = N % 2^32.
  -- We just need N = a0_val + a1_val * 2^32 and then % 2^32 = a0_val % 2^32 = a0_val.
  -- a0_val < 2^32 (from packed_a_lo_val_eq_of_match's image — 4 bytes < 2^32).
  have h_extract_eq :
      (Sail.BitVec.extractLsb
        (BitVec.ofNat 64
          ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296)) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) % 2^32 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
          BitVec.toNat_ofNat]
  rw [h_extract_eq]
  rw [h_a0_val]
  -- The sum (m.a_1).val * 2^32 mod 2^32 = 0.
  -- And ((a0_val) + (m.a_1).val * 2^32) % 2^32 = a0_val % 2^32 = a0_val (as a0_val < 2^32).
  have h_a0_lt : (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
        + (v.free_in_a_2 r_binary).val * 65536 + (v.free_in_a_3 r_binary).val * 16777216
        < 4294967296 := by omega
  omega

/-- **W-variant register shift-pin bridge.** Derives
    `(extractLsb r2_val 31 0).toNat % 32 = (v.free_in_b).val % 32` from
    transpile lanes (`m.b_0 = lane_lo (xreg rs2)`, …), read_xreg,
    op_is_shift = 1, and matches_entry. Form consumed by SLLW/SRLW/SRAW
    `equiv_<OP>` proofs as `h_shift_pin`. -/
lemma shift_pin_w_eq_of_shift_match
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ) (rs2 : Fin 32) (r2_val : BitVec 64)
    (h_b_lo_t : m.b_0 r_main = lane_lo ((SailStateBridge.sail_to_rv64 state).xreg rs2))
    (h_b_hi_t : m.b_1 r_main = lane_hi ((SailStateBridge.sail_to_rv64 state).xreg rs2))
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary)) :
    (Sail.BitVec.extractLsb r2_val 31 0 : BitVec (31 - 0 + 1)).toNat % 32
      = (v.free_in_b r_binary).val % 32 := by
  have h_b_main : (v.free_in_b r_binary).val < 256 := be_b_lt_256 v r_binary
  have h_main_b0 : (m.b_0 r_main).val < 4294967296 :=
    ZiskFv.Airs.Main.main_b_lo_lt_2_32 m r_main
  have h_b0_lt : (v.b_0 r_binary).val < 4294967296 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb0, _⟩ :=
      binary_extension_columns_in_range v r_binary
    exact hb0
  -- Sail packed form.
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
    show _ < 18446744069414584321; omega
  -- (extractLsb (ofNat 64 N) 31 0).toNat = N % 2^32.
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
  -- ((free_in_b.val + 256 * b_0.val) + m.b_1.val * 2^32) % 2^32 % 32 = free_in_b.val % 32.
  -- Both 256 * b_0.val and m.b_1.val * 2^32 are multiples of 32 (256 = 8*32).
  omega

/-- **W-variant immediate shift-pin bridge (SLLIW/SRLIW/SRAIW).**
    Derives `shamt.toNat = (v.free_in_b).val % 32` where `shamt : BitVec 5`.
    Mirrors `shift_pin_immediate_eq_of_shift_match` but for the 5-bit
    immediate W-variants. -/
lemma shift_pin_w_immediate_eq_of_shift_match
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ) (shamt : BitVec 5)
    (h_b_lo_t : m.b_0 r_main = shamt_w_b_lo shamt)
    (h_op_is_shift : v.op_is_shift r_binary = 1)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary)) :
    shamt.toNat = (v.free_in_b r_binary).val % 32 := by
  have h_b_main : (v.free_in_b r_binary).val < 256 := be_b_lt_256 v r_binary
  have h_b0_lt : (v.b_0 r_binary).val < 4294967296 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb0, _⟩ :=
      binary_extension_columns_in_range v r_binary
    exact hb0
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
    show _ < 18446744069414584321; omega
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
`m.b_0 r_main = memory_entry_lo e1 = e1.x0 + 256 * e1.x1 + 65536 *
e1.x2 + 16777216 * e1.x3`, the op-bus permutation handshake
`m.b_0 r_main = BinExt.b_lo = a0_packed` yields the FGL equation
`free_in_a_0 + 256*free_in_a_1 + 65536*free_in_a_2 + 16777216*free_in_a_3
 = e1.x0 + 256*e1.x1 + 65536*e1.x2 + 16777216*e1.x3`.

Both sides have all bytes < 256 (BinExt side from
`binary_extension_columns_in_range`; e1 side from
`memory_bus_entry_byte_range_perm_sound`), so the FGL equation lifts
to ℕ, and base-256 uniqueness extracts the per-byte equalities
`(v.free_in_a_i r_binary).val = e1.x_i.val` for i ∈ {0, 1, 2, 3} —
the exact promise hypotheses (`h_a0_match`..`h_a3_match`) consumed
by `equiv_LW`. LB consumes only `h_a0_match`; LH consumes `h_a0_match`
and `h_a1_match`; LW consumes all four.

No new trust-ledger axioms. Pure-Lean composition of:
* `op_bus_perm_sound_BinaryExtension` (class #4)
* `main_sext_load_emission_bundle` (class #4)
* `binary_extension_op_is_shift_pin` (class #6)
* `binary_extension_columns_in_range` (class #6)
* `memory_bus_entry_byte_range_perm_sound` (class #5b).
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

/-- **SEXT-mode 4-byte lane-match bridge.** From the Main↔BinExt
    op-bus handshake `h_match`, the Main b-lo bundle equation
    `m.b_0 r_main = memory_entry_lo e1`, the SEXT-family flag
    `v.op_is_shift r_binary = 0`, and byte ranges (derived
    internally), produce the per-byte equalities
    `(v.free_in_a_i r_binary).val = e1.x_i.val` for i ∈ {0, 1, 2, 3}. -/
lemma sext_lane_match_bytes_eq_of_match
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ) (e1 : Interaction.MemoryBusEntry FGL)
    (h_main_b0_eq : m.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1)
    (h_op_is_shift_zero : v.op_is_shift r_binary = 0)
    (h_match : matches_entry (opBus_row_Main m r_main)
                              (opBus_row_BinaryExtension v r_binary)) :
    (v.free_in_a_0 r_binary).val = e1.x0.val
    ∧ (v.free_in_a_1 r_binary).val = e1.x1.val
    ∧ (v.free_in_a_2 r_binary).val = e1.x2.val
    ∧ (v.free_in_a_3 r_binary).val = e1.x3.val := by
  -- Byte ranges (BinExt side).
  obtain ⟨ha0, ha1, ha2, ha3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    binary_extension_columns_in_range v r_binary
  -- Byte ranges (e1 side).
  obtain ⟨he0, he1, he2, he3, _, _, _, _⟩ :=
    ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e1
  -- Project the b_lo conjunct from matches_entry.
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryExtension] at h_lane_eqs
  obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_lane_eqs
  -- op_is_shift = 0 collapses the b_lo RHS to `a0 = packed4 a-bytes`.
  rw [h_op_is_shift_zero] at h_b_lo_m
  have h_b0_fgl : m.b_0 r_main
      = v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
        + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary := by
    rw [h_b_lo_m]; ring
  -- Combine: packed4 a-bytes = memory_entry_lo e1.
  have h_eq_fgl :
      (v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
        + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary : FGL)
      = e1.x0 + e1.x1 * 256 + e1.x2 * 65536 + e1.x3 * 16777216 := by
    rw [← h_b0_fgl, h_main_b0_eq]
    simp only [ZiskFv.Airs.MemoryBus.memory_entry_lo]
  -- Take .val of both sides; both lift to ℕ since byte sums < 2^32 < GL_prime.
  have h_lhs_val :
      (v.free_in_a_0 r_binary + 256 * v.free_in_a_1 r_binary
        + 65536 * v.free_in_a_2 r_binary + 16777216 * v.free_in_a_3 r_binary : FGL).val
      = (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
        + (v.free_in_a_2 r_binary).val * 65536
        + (v.free_in_a_3 r_binary).val * 16777216 :=
    packed_a_lo_val_eq_of_match v r_binary ha0 ha1 ha2 ha3
  have h_rhs_val :
      (e1.x0 + e1.x1 * 256 + e1.x2 * 65536 + e1.x3 * 16777216 : FGL).val
      = e1.x0.val + e1.x1.val * 256 + e1.x2.val * 65536 + e1.x3.val * 16777216 := by
    have h_cast :
        e1.x0 + e1.x1 * 256 + e1.x2 * 65536 + e1.x3 * 16777216
        = ((((e1.x0.val + e1.x1.val * 256 + e1.x2.val * 65536
              + e1.x3.val * 16777216 : ℕ) : FGL))) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    show _ < 18446744069414584321; omega
  -- Equate the Nat packs and apply base-256 uniqueness.
  have h_val_eq := congr_arg Fin.val h_eq_fgl
  rw [h_lhs_val, h_rhs_val] at h_val_eq
  exact byte_pack4_inj _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3
    he0 he1 he2 he3 h_val_eq

end ZiskFv.Equivalence_v1.Bridge.BinaryExtension
