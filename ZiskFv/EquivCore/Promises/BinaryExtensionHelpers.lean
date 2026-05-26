import Mathlib

import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.Airs.Tables.BinaryExtensionTable
import ZiskFv.Airs.MemoryBus
import ZiskFv.EquivCore.Bridge.Mem
import ZiskFv.EquivCore.Bridge.BinaryExtension

/-!
# BinaryExtension-family wrapper helpers

Per-AIR helper lemmas hoisted from the 15 BinaryExtension-family
`Compliance/Wrappers/<Op>.lean` wrappers (SLL, SRL, SRA, SLLW, SRLW,
SRAW, SLLI, SRLI, SRAI, SLLIW, SRLIW, SRAIW, LB, LH, LW).

**Audit outcome:** Outcome B (mostly different from Binary). The
shift wrappers (12 of 15) are already extremely thin pass-throughs:
their entire active body is a 4-line `obtain bus / obtain pins /
op_bus_perm_sound_BinaryExtension / exact` block. There is no analog
of Binary's massive `binary_consumer_byte_match_chain_pin`
destructure here — the BinaryExtension canonical theorems
pre-discharge the row-byte lookup pipeline internally via
`binary_extension_row_byte_lookups`, `project_match_op_clo_chi`, and
the c-lane-sum-bound bridges.

Helpers provided:

1. **Op-bus handshake helpers** (`binexec_op_bus_handshake_<OP>`) —
   one per opcode literal (SLL, SRL, SRA, SLL_W, SRL_W, SRA_W,
   SIGNEXTEND_B, SIGNEXTEND_H, SIGNEXTEND_W). Each hides the
   `Or.inr (Or.inr ... (Or.inl h_main_op) ...)` selector ladder
   behind a per-opcode name. Saves ~2-3 lines per wrapper while
   improving readability.

2. **Signed-load full-discharge helper** (`load_full_discharge`) —
   bundles the ~40-line BinExt-side discharge pipeline that LB, LH,
   and LW each apply (op-bus handshake + `project_match_op_clo_chi`
   + `op_binary` derivation + `hc_{lo,hi}_sum_lt` + `h_bytes` +
   `op_is_shift_zero` + `lX_discharge_full` +
   `sext_lane_match_bytes_eq_of_match`) into a single call that
   returns a `LoadFullDischarge` aggregate.

**Trust footprint:** These helpers are `lemma` / `def` only — they
CONSUME existing trust-ledger axioms
(`op_bus_perm_sound_BinaryExtension`,
`binary_extension_op_is_shift_pin`,
`binary_extension_row_byte_lookups`) without adding any new axioms.
The `baseline-equiv-axiom-deps.txt` closure is preserved.

**Naming convention:** `binexec_<predicate>_<of|from>_<inputs>`
following the `BranchHelpers.lean` / `StoreHelpers.lean` /
`BinaryHelpers.lean` precedent.
-/

namespace ZiskFv.EquivCore.Promises

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus


/-! ## Section 1: Op-bus handshake helpers (one per opcode literal)

Each shift wrapper applies `op_bus_perm_sound_BinaryExtension` with
the selected disjunct (e.g. `Or.inr (Or.inr (Or.inl h_main_op))` for
`OP_SRA`). These nine helpers hide the disjunct-selector ladder
behind a per-opcode name.

The disjunction in `op_bus_perm_sound_BinaryExtension` covers nine
opcode literals in order: 0x21 (SLL), 0x22 (SRL), 0x23 (SRA), 0x24
(SLL_W), 0x25 (SRL_W), 0x26 (SRA_W), 0x27 (SEXT_B), 0x28 (SEXT_H),
0x29 (SEXT_W). Each helper builds the matching disjunct.
-/

/-- Op-bus handshake helper for `OP_SLL = 0x21` (disjunct #1). -/
lemma binexec_op_bus_handshake_SLL
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL) :
    ∃ r_binary : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension v r_binary) :=
  op_bus_perm_sound_BinaryExtension m v r_main h_main_active (Or.inl h_main_op)

/-- Op-bus handshake helper for `OP_SRL = 0x22` (disjunct #2). -/
lemma binexec_op_bus_handshake_SRL
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL) :
    ∃ r_binary : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension v r_binary) :=
  op_bus_perm_sound_BinaryExtension m v r_main h_main_active
    (Or.inr (Or.inl h_main_op))

/-- Op-bus handshake helper for `OP_SRA = 0x23` (disjunct #3). -/
lemma binexec_op_bus_handshake_SRA
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA) :
    ∃ r_binary : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension v r_binary) :=
  op_bus_perm_sound_BinaryExtension m v r_main h_main_active
    (Or.inr (Or.inr (Or.inl h_main_op)))

/-- Op-bus handshake helper for `OP_SLL_W = 0x24` (disjunct #4). -/
lemma binexec_op_bus_handshake_SLL_W
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL_W) :
    ∃ r_binary : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension v r_binary) :=
  op_bus_perm_sound_BinaryExtension m v r_main h_main_active
    (Or.inr (Or.inr (Or.inr (Or.inl h_main_op))))

/-- Op-bus handshake helper for `OP_SRL_W = 0x25` (disjunct #5). -/
lemma binexec_op_bus_handshake_SRL_W
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL_W) :
    ∃ r_binary : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension v r_binary) :=
  op_bus_perm_sound_BinaryExtension m v r_main h_main_active
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op)))))

/-- Op-bus handshake helper for `OP_SRA_W = 0x26` (disjunct #6). -/
lemma binexec_op_bus_handshake_SRA_W
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
    ∃ r_binary : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension v r_binary) :=
  op_bus_perm_sound_BinaryExtension m v r_main h_main_active
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op))))))

/-- Op-bus handshake helper for `OP_SIGNEXTEND_B = 0x27` (disjunct #7). -/
lemma binexec_op_bus_handshake_SIGNEXTEND_B
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_B) :
    ∃ r_binary : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension v r_binary) :=
  op_bus_perm_sound_BinaryExtension m v r_main h_main_active
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op)))))))

/-- Op-bus handshake helper for `OP_SIGNEXTEND_H = 0x28` (disjunct #8). -/
lemma binexec_op_bus_handshake_SIGNEXTEND_H
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_H) :
    ∃ r_binary : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension v r_binary) :=
  op_bus_perm_sound_BinaryExtension m v r_main h_main_active
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op))))))))

/-- Op-bus handshake helper for `OP_SIGNEXTEND_W = 0x29` (disjunct #9). -/
lemma binexec_op_bus_handshake_SIGNEXTEND_W
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_W) :
    ∃ r_binary : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension v r_binary) :=
  op_bus_perm_sound_BinaryExtension m v r_main h_main_active
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_main_op))))))))

/-! ## Section 2: Signed-load full-discharge helper

The signed-load wrappers (LB, LH, LW) each apply a ~40-line pipeline
that derives every BinExt-side promise hypothesis the canonical
`equiv_L{B,H,W}` consumes. The pipeline is near-identical between
the three wrappers; the differences are only:

* opcode literal (`OP_SIGNEXTEND_B/H/W`),
* op-table constant (`OP_SEXT_B/H/W`),
* `binary_extension_op_is_shift_pin` branch selector,
* `lX_discharge_full` variant.

This helper bundles the pipeline. It returns a `LoadFullDischarge`
record with all 4 byte lane-matches; the wrappers project the
1/2/4 they actually need.
-/

/-- Aggregate `Prop` bundle of every BinExt-side promise hypothesis
    a signed-load canonical theorem (`equiv_LB` / `equiv_LH` /
    `equiv_LW`) consumes, for a specific `r_binary` row index. The 4
    byte lane-matches are all included; LB uses only `a0_match`, LH
    uses `a0/a1`, LW uses all four.

    `h_bytes` is omitted because `ByteLookupHypotheses` is a `Type`
    (not a `Prop`) and cannot live inside a `Prop`-valued struct.
    Each wrapper calls `binary_extension_row_byte_lookups v r_binary`
    on its own — a 1-line invocation. -/
structure LoadFullDischargeAt
    (main : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ) (e1 : Interaction.MemoryBusEntry FGL)
    (op_sext_table : ℕ) : Prop where
  h_match :
    matches_entry (opBus_row_Main main r_main) (opBus_row_BinaryExtension v r_binary)
  h_op_binary : (v.op r_binary).val = op_sext_table
  hc_lo_sum_lt :
    (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
      + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
      + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
      + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val
      < 4294967296
  hc_hi_sum_lt :
    (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
      + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
      + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
      + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val
      < 4294967296
  h_match_clo :
    main.c_0 r_main = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
                     + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
                     + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
                     + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
  h_match_chi :
    main.c_1 r_main = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
                     + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
                     + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
                     + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
  h_a0_match : (v.free_in_a_0 r_binary).val = e1.x0.val
  h_a1_match : (v.free_in_a_1 r_binary).val = e1.x1.val
  h_a2_match : (v.free_in_a_2 r_binary).val = e1.x2.val
  h_a3_match : (v.free_in_a_3 r_binary).val = e1.x3.val

/-- **Signed-load full-discharge helper for LB.** Bundles the entire
    ~40-line BinExt-side pipeline that `equiv_LB` applies.

    Inputs:
    * `main`, `v` — Main + BinExt validators with selected row indices
    * `r_main`, `e1`, `e2` — the load's main row and memory entries
    * `r1_val`, `imm`, `rd` — the Sail-side operand values
    * `h_main_active`, `h_main_op` — Main row activation + opcode pin
    * `h_m1_mult`, `h_m1_as`, `h_m2_mult`, `h_m2_as` — bus-protocol
      structural hypotheses on e1/e2 (typically projected from a
      `LoadPromises` bundle).

    Output: a `LoadFullDischarge` containing every BinExt-side
    promise hypothesis the canonical `equiv_LB` consumes (only
    `h_a0_match` is actually used by `equiv_LB`; the helper still
    returns all four for uniformity with LH/LW). -/
lemma load_full_discharge_LB
    (main : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ) (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1) :
    ∃ r_binary : ℕ,
      LoadFullDischargeAt main v r_main r_binary e1
        ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_B := by
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SIGNEXTEND_B main v r_main h_main_active h_main_op
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main r_binary h_match
  have h_op_binary : (v.op r_binary).val
      = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_B := by
    rw [← h_op_fgl, h_main_op]; decide
  have hc_lo_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      main v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      main v r_main r_binary h_match_chi
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SIGNEXTEND_B := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift_zero : v.op_is_shift r_binary = 0 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin v r_binary).2
      (Or.inl h_op_v_eq)
  obtain ⟨h_main_emit_b, _h_main_emit_c, _h_ptr_match,
          _h_rd_zero_iff, _h_rd_idx⟩ :=
    ZiskFv.EquivCore.Bridge.Mem.lb_discharge_full
      main r_main e1 e2 r1_val imm rd
      h_main_active h_main_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  have h_main_b0_eq : main.b_0 r_main
      = ZiskFv.Airs.MemoryBus.memory_entry_lo e1 := h_main_emit_b.1
  obtain ⟨h_a0_match, h_a1_match, h_a2_match, h_a3_match⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.sext_lane_match_bytes_eq_of_match
      main v r_main r_binary e1 h_main_b0_eq h_op_is_shift_zero h_match
  exact ⟨r_binary,
    { h_match := h_match
      h_op_binary := h_op_binary
      hc_lo_sum_lt := hc_lo_sum_lt
      hc_hi_sum_lt := hc_hi_sum_lt
      h_match_clo := h_match_clo
      h_match_chi := h_match_chi
      h_a0_match := h_a0_match
      h_a1_match := h_a1_match
      h_a2_match := h_a2_match
      h_a3_match := h_a3_match }⟩

/-- Row-explicit + static-lookup variant of `load_full_discharge_LB`.
    Takes the BinaryExtension row witness `r_binary` and the cross-AIR
    `matches_entry` directly as parameters, bypassing
    `op_bus_perm_sound_BinaryExtension`. The dispatcher-side
    `Compliance.equiv_LB_via_static_binary_extension` derives `r_binary +
    h_match` from a Clean BinaryFamily ensemble balance witness and feeds
    them in. `op_is_shift = 0` is derived from the static lookup soundness
    witness (same as `_of_static_lookup`). -/
lemma load_full_discharge_LB_of_match
    (main : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary offset : ℕ) (env : Environment FGL)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      matches_entry (opBus_row_Main main r_main) (opBus_row_BinaryExtension v r_binary))
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1) :
    LoadFullDischargeAt main v r_main r_binary e1
      ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_B := by
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main r_binary h_match
  have h_op_binary : (v.op r_binary).val
      = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_B := by
    rw [← h_op_fgl, h_main_op]; decide
  have hc_lo_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      main v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      main v r_main r_binary h_match_chi
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SIGNEXTEND_B := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift_zero : v.op_is_shift r_binary = 0 :=
    ZiskFv.Airs.BinaryExtension.op_is_shift_zero_SIGNEXTEND_B_of_static_lookup
      v r_binary offset env h_static h_op_v_eq
  obtain ⟨h_main_emit_b, _h_main_emit_c, _h_ptr_match,
          _h_rd_zero_iff, _h_rd_idx⟩ :=
    ZiskFv.EquivCore.Bridge.Mem.lb_discharge_full
      main r_main e1 e2 r1_val imm rd
      h_main_active h_main_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  have h_main_b0_eq : main.b_0 r_main
      = ZiskFv.Airs.MemoryBus.memory_entry_lo e1 := h_main_emit_b.1
  obtain ⟨h_a0_match, h_a1_match, h_a2_match, h_a3_match⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.sext_lane_match_bytes_eq_of_match
      main v r_main r_binary e1 h_main_b0_eq h_op_is_shift_zero h_match
  exact
    { h_match := h_match
      h_op_binary := h_op_binary
      hc_lo_sum_lt := hc_lo_sum_lt
      hc_hi_sum_lt := hc_hi_sum_lt
      h_match_clo := h_match_clo
      h_match_chi := h_match_chi
      h_a0_match := h_a0_match
      h_a1_match := h_a1_match
      h_a2_match := h_a2_match
      h_a3_match := h_a3_match }

/-- Static-lookup variant of `load_full_discharge_LB`. This has the same
    output shape, but derives `op_is_shift = 0` from the shared C7
    BinaryExtension static lookup witness rather than from
    `binary_extension_op_is_shift_pin`. -/
lemma load_full_discharge_LB_of_static_lookup
    (main : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main offset : ℕ) (env : Environment FGL)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1) :
    ∃ r_binary : ℕ,
      LoadFullDischargeAt main v r_main r_binary e1
        ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_B := by
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SIGNEXTEND_B main v r_main h_main_active h_main_op
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main r_binary h_match
  have h_op_binary : (v.op r_binary).val
      = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_B := by
    rw [← h_op_fgl, h_main_op]; decide
  have hc_lo_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      main v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      main v r_main r_binary h_match_chi
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SIGNEXTEND_B := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift_zero : v.op_is_shift r_binary = 0 :=
    ZiskFv.Airs.BinaryExtension.op_is_shift_zero_SIGNEXTEND_B_of_static_lookup
      v r_binary offset env h_static h_op_v_eq
  obtain ⟨h_main_emit_b, _h_main_emit_c, _h_ptr_match,
          _h_rd_zero_iff, _h_rd_idx⟩ :=
    ZiskFv.EquivCore.Bridge.Mem.lb_discharge_full
      main r_main e1 e2 r1_val imm rd
      h_main_active h_main_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  have h_main_b0_eq : main.b_0 r_main
      = ZiskFv.Airs.MemoryBus.memory_entry_lo e1 := h_main_emit_b.1
  obtain ⟨h_a0_match, h_a1_match, h_a2_match, h_a3_match⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.sext_lane_match_bytes_eq_of_match
      main v r_main r_binary e1 h_main_b0_eq h_op_is_shift_zero h_match
  exact ⟨r_binary,
    { h_match := h_match
      h_op_binary := h_op_binary
      hc_lo_sum_lt := hc_lo_sum_lt
      hc_hi_sum_lt := hc_hi_sum_lt
      h_match_clo := h_match_clo
      h_match_chi := h_match_chi
      h_a0_match := h_a0_match
      h_a1_match := h_a1_match
      h_a2_match := h_a2_match
      h_a3_match := h_a3_match }⟩

/-- **Signed-load full-discharge helper for LH.** See
    `load_full_discharge_LB` for description; only the opcode literal
    + `binary_extension_op_is_shift_pin` branch + `lh_discharge_full`
    variant differ. -/
lemma load_full_discharge_LH
    (main : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ) (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_H)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1) :
    ∃ r_binary : ℕ,
      LoadFullDischargeAt main v r_main r_binary e1
        ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_H := by
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SIGNEXTEND_H main v r_main h_main_active h_main_op
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main r_binary h_match
  have h_op_binary : (v.op r_binary).val
      = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_H := by
    rw [← h_op_fgl, h_main_op]; decide
  have hc_lo_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      main v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      main v r_main r_binary h_match_chi
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SIGNEXTEND_H := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift_zero : v.op_is_shift r_binary = 0 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin v r_binary).2
      (Or.inr (Or.inl h_op_v_eq))
  obtain ⟨h_main_emit_b, _h_main_emit_c, _h_ptr_match,
          _h_rd_zero_iff, _h_rd_idx⟩ :=
    ZiskFv.EquivCore.Bridge.Mem.lh_discharge_full
      main r_main e1 e2 r1_val imm rd
      h_main_active h_main_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  have h_main_b0_eq : main.b_0 r_main
      = ZiskFv.Airs.MemoryBus.memory_entry_lo e1 := h_main_emit_b.1
  obtain ⟨h_a0_match, h_a1_match, h_a2_match, h_a3_match⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.sext_lane_match_bytes_eq_of_match
      main v r_main r_binary e1 h_main_b0_eq h_op_is_shift_zero h_match
  exact ⟨r_binary,
    { h_match := h_match
      h_op_binary := h_op_binary
      hc_lo_sum_lt := hc_lo_sum_lt
      hc_hi_sum_lt := hc_hi_sum_lt
      h_match_clo := h_match_clo
      h_match_chi := h_match_chi
      h_a0_match := h_a0_match
      h_a1_match := h_a1_match
      h_a2_match := h_a2_match
      h_a3_match := h_a3_match }⟩

/-- Static-lookup variant of `load_full_discharge_LH`. This mirrors the
    old helper but derives `op_is_shift = 0` from the shared C7
    BinaryExtension static lookup witness. -/
lemma load_full_discharge_LH_of_static_lookup
    (main : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main offset : ℕ) (env : Environment FGL)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_H)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1) :
    ∃ r_binary : ℕ,
      LoadFullDischargeAt main v r_main r_binary e1
        ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_H := by
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SIGNEXTEND_H main v r_main h_main_active h_main_op
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main r_binary h_match
  have h_op_binary : (v.op r_binary).val
      = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_H := by
    rw [← h_op_fgl, h_main_op]; decide
  have hc_lo_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      main v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      main v r_main r_binary h_match_chi
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SIGNEXTEND_H := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift_zero : v.op_is_shift r_binary = 0 :=
    ZiskFv.Airs.BinaryExtension.op_is_shift_zero_SIGNEXTEND_H_of_static_lookup
      v r_binary offset env h_static h_op_v_eq
  obtain ⟨h_main_emit_b, _h_main_emit_c, _h_ptr_match,
          _h_rd_zero_iff, _h_rd_idx⟩ :=
    ZiskFv.EquivCore.Bridge.Mem.lh_discharge_full
      main r_main e1 e2 r1_val imm rd
      h_main_active h_main_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  have h_main_b0_eq : main.b_0 r_main
      = ZiskFv.Airs.MemoryBus.memory_entry_lo e1 := h_main_emit_b.1
  obtain ⟨h_a0_match, h_a1_match, h_a2_match, h_a3_match⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.sext_lane_match_bytes_eq_of_match
      main v r_main r_binary e1 h_main_b0_eq h_op_is_shift_zero h_match
  exact ⟨r_binary,
    { h_match := h_match
      h_op_binary := h_op_binary
      hc_lo_sum_lt := hc_lo_sum_lt
      hc_hi_sum_lt := hc_hi_sum_lt
      h_match_clo := h_match_clo
      h_match_chi := h_match_chi
      h_a0_match := h_a0_match
      h_a1_match := h_a1_match
      h_a2_match := h_a2_match
      h_a3_match := h_a3_match }⟩

/-- **Signed-load full-discharge helper for LW.** See
    `load_full_discharge_LB` for description; only the opcode literal
    + `binary_extension_op_is_shift_pin` branch + `lw_discharge_full`
    variant differ. -/
lemma load_full_discharge_LW
    (main : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ) (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_W)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1) :
    ∃ r_binary : ℕ,
      LoadFullDischargeAt main v r_main r_binary e1
        ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_W := by
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SIGNEXTEND_W main v r_main h_main_active h_main_op
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main r_binary h_match
  have h_op_binary : (v.op r_binary).val
      = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_W := by
    rw [← h_op_fgl, h_main_op]; decide
  have hc_lo_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      main v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      main v r_main r_binary h_match_chi
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SIGNEXTEND_W := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift_zero : v.op_is_shift r_binary = 0 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin v r_binary).2
      (Or.inr (Or.inr h_op_v_eq))
  obtain ⟨h_main_emit_b, _h_main_emit_c, _h_ptr_match,
          _h_rd_zero_iff, _h_rd_idx⟩ :=
    ZiskFv.EquivCore.Bridge.Mem.lw_discharge_full
      main r_main e1 e2 r1_val imm rd
      h_main_active h_main_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  have h_main_b0_eq : main.b_0 r_main
      = ZiskFv.Airs.MemoryBus.memory_entry_lo e1 := h_main_emit_b.1
  obtain ⟨h_a0_match, h_a1_match, h_a2_match, h_a3_match⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.sext_lane_match_bytes_eq_of_match
      main v r_main r_binary e1 h_main_b0_eq h_op_is_shift_zero h_match
  exact ⟨r_binary,
    { h_match := h_match
      h_op_binary := h_op_binary
      hc_lo_sum_lt := hc_lo_sum_lt
      hc_hi_sum_lt := hc_hi_sum_lt
      h_match_clo := h_match_clo
      h_match_chi := h_match_chi
      h_a0_match := h_a0_match
      h_a1_match := h_a1_match
      h_a2_match := h_a2_match
      h_a3_match := h_a3_match }⟩

/-- Static-lookup variant of `load_full_discharge_LW`. This mirrors the
    old helper but derives `op_is_shift = 0` from the shared C7
    BinaryExtension static lookup witness. -/
lemma load_full_discharge_LW_of_static_lookup
    (main : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main offset : ℕ) (env : Environment FGL)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_W)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1) :
    ∃ r_binary : ℕ,
      LoadFullDischargeAt main v r_main r_binary e1
        ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_W := by
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SIGNEXTEND_W main v r_main h_main_active h_main_op
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main r_binary h_match
  have h_op_binary : (v.op r_binary).val
      = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_W := by
    rw [← h_op_fgl, h_main_op]; decide
  have hc_lo_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      main v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      main v r_main r_binary h_match_chi
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SIGNEXTEND_W := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift_zero : v.op_is_shift r_binary = 0 :=
    ZiskFv.Airs.BinaryExtension.op_is_shift_zero_SIGNEXTEND_W_of_static_lookup
      v r_binary offset env h_static h_op_v_eq
  obtain ⟨h_main_emit_b, _h_main_emit_c, _h_ptr_match,
          _h_rd_zero_iff, _h_rd_idx⟩ :=
    ZiskFv.EquivCore.Bridge.Mem.lw_discharge_full
      main r_main e1 e2 r1_val imm rd
      h_main_active h_main_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  have h_main_b0_eq : main.b_0 r_main
      = ZiskFv.Airs.MemoryBus.memory_entry_lo e1 := h_main_emit_b.1
  obtain ⟨h_a0_match, h_a1_match, h_a2_match, h_a3_match⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.sext_lane_match_bytes_eq_of_match
      main v r_main r_binary e1 h_main_b0_eq h_op_is_shift_zero h_match
  exact ⟨r_binary,
    { h_match := h_match
      h_op_binary := h_op_binary
      hc_lo_sum_lt := hc_lo_sum_lt
      hc_hi_sum_lt := hc_hi_sum_lt
      h_match_clo := h_match_clo
      h_match_chi := h_match_chi
      h_a0_match := h_a0_match
      h_a1_match := h_a1_match
      h_a2_match := h_a2_match
      h_a3_match := h_a3_match }⟩

end ZiskFv.EquivCore.Promises
