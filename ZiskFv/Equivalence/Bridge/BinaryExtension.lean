import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge

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

end ZiskFv.Equivalence.Bridge.BinaryExtension
