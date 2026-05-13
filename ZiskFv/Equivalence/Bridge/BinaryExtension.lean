import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.BinaryExtensionTable
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.EntryRanges

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
conjunct is what downstream `equiv_<OP>` proofs (Step 3) consume to
discharge their `h_match_clo` / `h_match_chi` *promise hypotheses*
without caller commitment.

What remains caller-supplied (this conservative pass):

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

(Step 0b — the BinaryExtension layout cascade fix renaming
column-major reads to row-major — is the prerequisite for any
downstream consumer to project `matches_entry`'s `c_lo` / `c_hi`
conjuncts into the form `equiv_<OP>` expects. This bridge itself
is independent of that cascade because it only delivers
`matches_entry` opaque; the projection step happens at the
consumer.)
-/

namespace ZiskFv.Equivalence.Bridge.BinaryExtension

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **BinaryExtension discharge bridge (conservative).** Replaces
    the per-opcode `r_e` row-index parameter + `h_match` cross-AIR
    *promise hypothesis* with a derivation rooted at
    `op_bus_perm_sound_BinaryExtension` (Phase A).

    Caller obligations after this discharge:
    * `h_main_active : m.is_external_op r_main = 1`
    * `h_main_op_in_set` (the 9-way disjunction in the OpBus axiom;
      each call site pins a specific shift / sign-extend literal).

    Outputs: existential `r_e` + `matches_entry`. -/
theorem binext_discharge_conservative
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
    obtained a concrete `r_e` row index from `binext_discharge_conservative`
    (or from caller-supplied existential witnessing). -/
theorem byte_ranges_at_holds (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
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
theorem sll_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.BinaryExtensionTable.OP_SLL
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
    ZiskFv.Airs.BinaryExtensionTable.OP_SLL ZiskFv.Trusted.OP_SLL
    (by decide) h_main_active h_main_op (Or.inl h_main_op)

/-- **SRL partial discharge.** `op = 0x22`. -/
theorem srl_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.BinaryExtensionTable.OP_SRL
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
    ZiskFv.Airs.BinaryExtensionTable.OP_SRL ZiskFv.Trusted.OP_SRL
    (by decide) h_main_active h_main_op (Or.inr (Or.inl h_main_op))

/-- **SRA partial discharge.** `op = 0x23`. -/
theorem sra_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.BinaryExtensionTable.OP_SRA
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
    ZiskFv.Airs.BinaryExtensionTable.OP_SRA ZiskFv.Trusted.OP_SRA
    (by decide) h_main_active h_main_op (Or.inr (Or.inr (Or.inl h_main_op)))

/-- **SLLW (SLL_W) partial discharge.** `op = 0x24`. -/
theorem sllw_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL_W) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.BinaryExtensionTable.OP_SLL_W
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
    ZiskFv.Airs.BinaryExtensionTable.OP_SLL_W ZiskFv.Trusted.OP_SLL_W
    (by decide) h_main_active h_main_op
    (Or.inr (Or.inr (Or.inr (Or.inl h_main_op))))

/-- **SRLW (SRL_W) partial discharge.** `op = 0x25`. -/
theorem srlw_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL_W) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.BinaryExtensionTable.OP_SRL_W
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
    ZiskFv.Airs.BinaryExtensionTable.OP_SRL_W ZiskFv.Trusted.OP_SRL_W
    (by decide) h_main_active h_main_op
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op)))))

/-- **SRAW (SRA_W) partial discharge.** `op = 0x26`. -/
theorem sraw_discharge_partial
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ) (e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
    ∃ r_binary,
      (v.op r_binary).val = ZiskFv.Airs.BinaryExtensionTable.OP_SRA_W
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
    ZiskFv.Airs.BinaryExtensionTable.OP_SRA_W ZiskFv.Trusted.OP_SRA_W
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
theorem project_match_op_clo_chi
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

end ZiskFv.Equivalence.Bridge.BinaryExtension
