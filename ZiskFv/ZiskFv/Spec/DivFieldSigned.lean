import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.CarryChain
import ZiskFv.Airs.Arith.Bridge1
import ZiskFv.Airs.OperationBus
import ZiskFv.Spec.Add
import ZiskFv.Spec.Mul
import ZiskFv.Tactics.ArithSMArchetype

/-!
**Track N K4 — Bridge 2 (signed variant): Main ↔ Arith signed-DIV/REM
field composition.**

Mirrors `Spec/MulField.lean`'s composition pattern for the **signed**
DIV/REM family (DIV, REM with signed operands), and also provides the
unsigned analogue for completeness (since no `Spec/DivField.lean` exists).

## Context

`Spec/MulField.lean` comment line 39-41 planned DIV/REM unsigned field
theorems in-file, but they were never written. This file provides both:
1. The **unsigned** DIV / REM field-correctness theorems
   (`main_div_unsigned_field_correct`, `main_rem_unsigned_field_correct`)
   as the first implementation of this bridge.
2. The **signed** DIV / REM field-correctness theorems
   (`main_div_signed_field_correct`, `main_rem_signed_field_correct`)
   for the Track N K4 use case.

## DIV bus layout

For Arith DIV rows:
- **Dividend** (`a` input → bus `a` lane): packed from Arith's `c[]` chunks
  (because `div = 1` routes the dividend through `c[]` at arith.pil:247).
- **Divisor** (`b` input → bus `b` lane): packed from Arith's `b[]` chunks.
- **Quotient** (primary output → bus `c` lane): packed from Arith's `a[]` chunks;
  Bridge 1 (`div_bus_res1_eq_a_hi`) normalizes `bus_res1` to `a[2] + a[3]*65536`.
- **Remainder** (secondary output → bus `c` lane on secondary rows):
  packed from Arith's `d[]` chunks; Bridge 1 (`rem_bus_res1_eq_d_hi`) normalizes.

So the signed DIV identity (for `na`, `nb`, `np`, `nr` free):

    fab * a_chunks * b_chunks
    + (1 - 2*nr) * d_chunks
    + (nb_fa * a_chunks + na_fb * b_chunks) * B^4
    + (nr - np) * B^4 + na*nb * B^8
    = (1 - 2*np) * c_chunks

where:
- `a_chunks = a_chunks_packed_div v r_arith` (quotient)
- `b_chunks = b_chunks_packed_div v r_arith` (divisor)
- `c_chunks = c_chunks_packed_div v r_arith` (dividend, RHS)
- `d_chunks = d_chunks_packed_div v r_arith` (remainder)

maps to Main level:
- `main_a_packed = c_chunks_packed_div` (dividend → Arith c[])
- `main_b_packed = b_chunks_packed_div` (divisor → Arith b[])
- `main_c_packed = a_chunks_packed_div` (quotient → Arith a[], Bridge 1)
  or on secondary rows: `main_c_packed = d_chunks_packed_div` (remainder, Bridge 1)

## Namespace note

`main_c_packed` here refers to `ZiskFv.Spec.Mul.main_c_packed` (from the
`open ZiskFv.Spec.Mul`). This is the same definition as
`ZiskFv.Spec.Add.main_c_packed` (`m.c_0 r + m.c_1 r * 4294967296`), but
the two are syntactically distinct to Lean's elaborator.

## Usage

Phase 2 N-MDR-signed derivation lemmas for DIV, REM consume these
theorems plus:
- `arith_table_lookup_sound_div` (for sign-witness pinning)
- `Fundamentals/PackedBitVec/Signed.lean` (for BitVec.toInt lift)
- `Fundamentals/PackedBitVec.lean` (for byte-sum bridge)
-/

namespace ZiskFv.Spec.DivFieldSigned

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.ArithBridge1
open ZiskFv.Airs.ArithCarryChain
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Mul
open ZiskFv.Tactics.ArithSMArchetype
open Arith.extraction

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Bundled circuit-holds predicates -/

/-- **Bundled DIV (primary) field hypotheses.** Adds the carry-chain
    bundle (`div_carry_chain_holds`) and constraint 46 to the base
    `div_primary_circuit_holds` needed for bus matching. -/
@[simp]
def div_field_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL) : Prop :=
  div_primary_circuit_holds m v r_main r_arith opcode_lit
  ∧ div_carry_chain_holds v r_arith
  ∧ constraint_46_every_row v.circuit r_arith

/-- **Bundled REM (secondary) field hypotheses.** Adds the carry-chain
    bundle and constraint 46 to the base `rem_secondary_circuit_holds`. -/
@[simp]
def rem_field_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL) : Prop :=
  rem_secondary_circuit_holds m v r_main r_arith opcode_lit
  ∧ div_carry_chain_holds v r_arith
  ∧ constraint_46_every_row v.circuit r_arith

/-! ## Bridge 2 lemmas for DIV/REM

These mirror `main_a_eq_chunks_mul` / `main_b_eq_chunks_mul` /
`main_c_eq_chunks_mul` from `Spec/MulField.lean`, but for the DIV bus
layout where the dividend is in `c[]`, divisor in `b[]`, and outputs
in `a[]` (quotient) / `d[]` (remainder). -/

/-- **Bridge 2 (DIV): Main-side packed dividend equals Arith `c` chunks.**
    On DIV rows, the dividend goes on the bus as `a_lo / a_hi`, which maps
    to Arith's `c[0..3]` chunks. Under m32 = 0, this gives
    `main_a_packed = c_chunks_packed_div`. -/
lemma main_dividend_eq_chunks_div
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : div_primary_circuit_holds m v r_main r_arith opcode_lit) :
    Spec.Add.main_a_packed m r_main = c_chunks_packed_div v r_arith := by
  obtain ⟨_, _, h_bus, h_mode, h_arith_mode⟩ := h
  obtain ⟨_, _, h_match_alo, h_match_ahi, _, _, _, _, _, _, _, _⟩ := h_bus
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  simp only [opBus_row_Main, opBus_row_ArithDiv] at h_match_alo h_match_ahi
  rw [h_m32] at h_match_ahi
  simp only [one_sub_zero_mul] at h_match_ahi
  unfold Spec.Add.main_a_packed c_chunks_packed_div
  rw [h_match_alo, h_match_ahi]
  ring

/-- **Bridge 2 (DIV): Main-side packed divisor equals Arith `b` chunks.** -/
lemma main_divisor_eq_chunks_div
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : div_primary_circuit_holds m v r_main r_arith opcode_lit) :
    Spec.Add.main_b_packed m r_main = b_chunks_packed_div v r_arith := by
  obtain ⟨_, _, h_bus, h_mode, _⟩ := h
  obtain ⟨_, _, _, _, h_match_blo, h_match_bhi, _, _, _, _, _, _⟩ := h_bus
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  simp only [opBus_row_Main, opBus_row_ArithDiv] at h_match_blo h_match_bhi
  rw [h_m32] at h_match_bhi
  simp only [one_sub_zero_mul] at h_match_bhi
  unfold Spec.Add.main_b_packed b_chunks_packed_div
  rw [h_match_blo, h_match_bhi]
  ring

/-- **Bridge 1 + 2 (DIV): Main-side packed c equals Arith quotient chunks.**
    Combines the bus-match (→ `main_c_packed = arith_quotient_packed`) with
    Bridge 1 (→ `bus_res1 = a[2] + a[3]*65536` under DIV-primary mode),
    yielding `main_c_packed = a_chunks_packed_div`. -/
lemma main_quotient_eq_chunks_div
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : div_field_circuit_holds m v r_main r_arith opcode_lit) :
    main_c_packed m r_main = a_chunks_packed_div v r_arith := by
  have h_primary := h.1
  have h_c46 := h.2.2
  have h_arith_mode := h_primary.2.2.2.2
  have h_sext := h_arith_mode.2.2.2.1
  have h_m32 := h_arith_mode.2.2.2.2
  have h_main_mul := h_arith_mode.2.1
  have h_main_div := h_arith_mode.1
  -- Bridge 1: bus_res1 = a[2] + a[3]*65536
  have h_bridge1 := div_bus_res1_eq_a_hi v r_arith h_c46 h_sext h_m32 h_main_mul h_main_div
  -- Bus match: main_c_packed = arith_quotient_packed = (a_0 + a_1*65536) + bus_res1 * 2^32
  have h_compositional := arith_archetype_div_bus_match m v r_main r_arith opcode_lit h_primary
  -- Now: main_c_packed = arith_quotient_packed and bus_res1 = a_2 + a_3*65536
  --     so arith_quotient_packed = a_chunks_packed_div
  rw [h_compositional]
  simp only [arith_quotient_packed]
  rw [h_bridge1]
  unfold a_chunks_packed_div
  ring

/-- **Bridge 2 (REM): Main-side packed dividend equals Arith `c` chunks.**
    On REM rows (secondary), the dividend is still on the same Arith row
    as the quotient — it goes on the bus as `a_lo / a_hi`, mapping to
    Arith's `c[0..3]`. Under m32 = 0, `main_a_packed = c_chunks_packed_div`. -/
lemma main_dividend_eq_chunks_rem
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : rem_secondary_circuit_holds m v r_main r_arith opcode_lit) :
    Spec.Add.main_a_packed m r_main = c_chunks_packed_div v r_arith := by
  obtain ⟨_, _, h_bus, h_mode, _⟩ := h
  obtain ⟨_, _, h_match_alo, h_match_ahi, _, _, _, _, _, _, _, _⟩ := h_bus
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  simp only [opBus_row_Main, opBus_row_ArithDivSecondary] at h_match_alo h_match_ahi
  rw [h_m32] at h_match_ahi
  simp only [one_sub_zero_mul] at h_match_ahi
  unfold Spec.Add.main_a_packed c_chunks_packed_div
  rw [h_match_alo, h_match_ahi]
  ring

/-- **Bridge 2 (REM): Main-side packed divisor equals Arith `b` chunks.** -/
lemma main_divisor_eq_chunks_rem
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : rem_secondary_circuit_holds m v r_main r_arith opcode_lit) :
    Spec.Add.main_b_packed m r_main = b_chunks_packed_div v r_arith := by
  obtain ⟨_, _, h_bus, h_mode, _⟩ := h
  obtain ⟨_, _, _, _, h_match_blo, h_match_bhi, _, _, _, _, _, _⟩ := h_bus
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  simp only [opBus_row_Main, opBus_row_ArithDivSecondary] at h_match_blo h_match_bhi
  rw [h_m32] at h_match_bhi
  simp only [one_sub_zero_mul] at h_match_bhi
  unfold Spec.Add.main_b_packed b_chunks_packed_div
  rw [h_match_blo, h_match_bhi]
  ring

/-- **Bridge 1 + 2 (REM): Main-side packed c equals Arith remainder chunks.**
    Combines bus-match (→ `main_c_packed = arith_remainder_packed`) with
    Bridge 1 (→ `bus_res1 = d[2] + d[3]*65536` under REM-secondary mode),
    yielding `main_c_packed = d_chunks_packed_div`. -/
lemma main_remainder_eq_chunks_rem
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : rem_field_circuit_holds m v r_main r_arith opcode_lit) :
    main_c_packed m r_main = d_chunks_packed_div v r_arith := by
  have h_secondary := h.1
  have h_c46 := h.2.2
  have h_arith_mode := h_secondary.2.2.2.2
  have h_sext := h_arith_mode.2.2.2.1
  have h_m32 := h_arith_mode.2.2.2.2
  have h_main_mul := h_arith_mode.2.1
  have h_main_div := h_arith_mode.1
  -- Bridge 1: bus_res1 = d[2] + d[3]*65536 on secondary rows
  have h_bridge1 := rem_bus_res1_eq_d_hi v r_arith h_c46 h_sext h_m32 h_main_mul h_main_div
  -- Bus match: main_c_packed = arith_remainder_packed = (d_0 + d_1*65536) + bus_res1 * 2^32
  have h_compositional := arith_archetype_rem_bus_match m v r_main r_arith opcode_lit h_secondary
  rw [h_compositional]
  simp only [arith_remainder_packed]
  rw [h_bridge1]
  unfold d_chunks_packed_div
  ring

/-! ## Field-correctness theorems -/

/-- **DIV-unsigned field correctness.** For `na = nb = np = nr = 0`,
    the field identity reduces to:

        quotient * divisor + remainder = dividend

    i.e. `a_chunks * b_chunks + d_chunks = c_chunks` at the Arith chunk
    level. At Main level: `main_c_packed * main_b_packed + d_chunks = main_a_packed`
    (quotient = main_c, divisor = main_b, dividend = main_a, remainder = d_chunks). -/
theorem main_div_unsigned_field_correct
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : div_field_circuit_holds m v r_main r_arith opcode_lit)
    (h_na : v.na r_arith = 0) (h_nb : v.nb r_arith = 0)
    (h_np : v.np r_arith = 0) (h_nr : v.nr r_arith = 0) :
    main_c_packed m r_main * Spec.Add.main_b_packed m r_main
      + d_chunks_packed_div v r_arith
      = Spec.Add.main_a_packed m r_main := by
  -- Establish bridge equalities
  have h_a_eq := main_dividend_eq_chunks_div m v r_main r_arith opcode_lit h.1
  have h_b_eq := main_divisor_eq_chunks_div m v r_main r_arith opcode_lit h.1
  have h_c_eq := main_quotient_eq_chunks_div m v r_main r_arith opcode_lit h
  -- Carry chain
  have h_chain := h.2.1
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  have h_primary := h.1
  have h_arith_mode := h_primary.2.2.2.2
  have h_sext := h_arith_mode.2.2.2.1
  have h_m32 := h_arith_mode.2.2.2.2
  have h_div := h_arith_mode.2.2.1
  -- h_packed: a_chunks * b_chunks + d_chunks = c_chunks (quotient * divisor + rem = dividend)
  have h_packed := arith_div_unsigned_packed_correct v r_arith
    h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
    h_na h_nb h_np h_nr h_sext h_m32 h_div
  -- Rewrite using bridges, then close
  rw [h_c_eq, h_b_eq, h_a_eq]
  exact h_packed

/-- **DIV-signed field correctness (Arith chunk level).** The signed-DIV
    packed identity at the Arith chunk level. Takes `na`, `nb`, `np`, `nr`
    as **free** witnesses.

    The conclusion:
        (1 - 2*na - 2*nb + 4*na*nb) * a_chunks * b_chunks
        + (1 - 2*nr) * d_chunks
        + (nb*(1-2*na)*a_chunks + na*(1-2*nb)*b_chunks) * B^4
        + (nr - np) * B^4
        + na*nb * B^8
        = (1 - 2*np) * c_chunks

    where `a_chunks = a_chunks_packed_div` (quotient absolute value),
    `b_chunks = b_chunks_packed_div` (divisor absolute value),
    `c_chunks = c_chunks_packed_div` (dividend absolute value),
    `d_chunks = d_chunks_packed_div` (remainder absolute value). -/
theorem main_div_signed_field_correct
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : div_field_circuit_holds m v r_main r_arith opcode_lit) :
    (1 - 2 * v.na r_arith - 2 * v.nb r_arith + 4 * v.na r_arith * v.nb r_arith)
        * a_chunks_packed_div v r_arith * b_chunks_packed_div v r_arith
      + (1 - 2 * v.nr r_arith) * d_chunks_packed_div v r_arith
      + (v.nb r_arith * (1 - 2 * v.na r_arith) * a_chunks_packed_div v r_arith
          + v.na r_arith * (1 - 2 * v.nb r_arith) * b_chunks_packed_div v r_arith)
          * (65536 * 65536 * 65536 * 65536)
      + (v.nr r_arith - v.np r_arith) * (65536 * 65536 * 65536 * 65536)
      + v.na r_arith * v.nb r_arith
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * v.np r_arith) * c_chunks_packed_div v r_arith := by
  -- Unpack hypotheses
  have h_primary := h.1
  have h_chain := h.2.1
  have h_arith_mode := h_primary.2.2.2.2
  have h_sext := h_arith_mode.2.2.2.1
  have h_m32 := h_arith_mode.2.2.2.2
  have h_div := h_arith_mode.2.2.1
  -- Unpack carry chain
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  -- Apply the signed carry-chain identity directly
  exact arith_div_signed_packed_correct v r_arith
    h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
    h_sext h_m32 h_div

/-- **DIV-signed field correctness (Main-level operands).** Lifts
    `main_div_signed_field_correct` from Arith chunk-level to Main operand
    level, using bridges 1+2 for the dividend, divisor, and quotient.

    The conclusion expresses the identity in terms of Main AIR packed values:
    - `main_a_packed = dividend` (c_chunks_packed_div)
    - `main_b_packed = divisor` (b_chunks_packed_div)
    - `main_c_packed = quotient` (a_chunks_packed_div)
    - `d_chunks = remainder` (d_chunks_packed_div)

        (1 - 2*na - 2*nb + 4*na*nb) * main_c * main_b
        + (1 - 2*nr) * d_chunks
        + (nb*(1-2*na)*main_c + na*(1-2*nb)*main_b) * B^4
        + (nr - np) * B^4 + na*nb * B^8
        = (1 - 2*np) * main_a -/
theorem main_div_signed_field_correct_main_level
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : div_field_circuit_holds m v r_main r_arith opcode_lit) :
    (1 - 2 * v.na r_arith - 2 * v.nb r_arith + 4 * v.na r_arith * v.nb r_arith)
        * main_c_packed m r_main * Spec.Add.main_b_packed m r_main
      + (1 - 2 * v.nr r_arith) * d_chunks_packed_div v r_arith
      + (v.nb r_arith * (1 - 2 * v.na r_arith) * main_c_packed m r_main
          + v.na r_arith * (1 - 2 * v.nb r_arith) * Spec.Add.main_b_packed m r_main)
          * (65536 * 65536 * 65536 * 65536)
      + (v.nr r_arith - v.np r_arith) * (65536 * 65536 * 65536 * 65536)
      + v.na r_arith * v.nb r_arith
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * v.np r_arith) * Spec.Add.main_a_packed m r_main := by
  -- Bridge 2: main_a = dividend chunks, main_b = divisor chunks, main_c = quotient chunks
  have h_a_eq := main_dividend_eq_chunks_div m v r_main r_arith opcode_lit h.1
  have h_b_eq := main_divisor_eq_chunks_div m v r_main r_arith opcode_lit h.1
  have h_c_eq := main_quotient_eq_chunks_div m v r_main r_arith opcode_lit h
  -- Core signed identity at chunk level
  have h_core := main_div_signed_field_correct m v r_main r_arith opcode_lit h
  -- Rewrite h_core: replace a_chunks → main_c, b_chunks → main_b, c_chunks → main_a
  rw [← h_c_eq, ← h_b_eq, ← h_a_eq] at h_core
  exact h_core

/-- **REM-unsigned field correctness.** For `na = nb = np = nr = 0`,
    the remainder identity at the Arith chunk level:

        a_chunks * b_chunks + d_chunks = c_chunks

    i.e. quotient * divisor + remainder = dividend. Identical to the DIV
    identity — the same Arith row is used; only the bus output (Main c lane)
    differs (REM rows output the remainder via `d[]`). -/
theorem main_rem_unsigned_field_correct
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : rem_field_circuit_holds m v r_main r_arith opcode_lit)
    (h_na : v.na r_arith = 0) (h_nb : v.nb r_arith = 0)
    (h_np : v.np r_arith = 0) (h_nr : v.nr r_arith = 0) :
    a_chunks_packed_div v r_arith * b_chunks_packed_div v r_arith
      + d_chunks_packed_div v r_arith
      = c_chunks_packed_div v r_arith := by
  -- This is exactly arith_div_unsigned_packed_correct (the DIV Euclidean identity)
  have h_secondary := h.1
  have h_chain := h.2.1
  have h_arith_mode := h_secondary.2.2.2.2
  have h_sext := h_arith_mode.2.2.2.1
  have h_m32 := h_arith_mode.2.2.2.2
  have h_div := h_arith_mode.2.2.1
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  exact arith_div_unsigned_packed_correct v r_arith
    h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
    h_na h_nb h_np h_nr h_sext h_m32 h_div

/-- **REM-signed field correctness (Arith chunk level).** The signed-REM
    identity at the Arith chunk level. Same identity as DIV-signed
    (both use the same Arith row), just presenting it for the REM context.

    For Phase 2 N-MDR-signed: this theorem plus `main_remainder_eq_chunks_rem`
    gives `main_c_packed = d_chunks_packed_div` and the Euclidean signed
    identity for the remainder. -/
theorem main_rem_signed_field_correct
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : rem_field_circuit_holds m v r_main r_arith opcode_lit) :
    (1 - 2 * v.na r_arith - 2 * v.nb r_arith + 4 * v.na r_arith * v.nb r_arith)
        * a_chunks_packed_div v r_arith * b_chunks_packed_div v r_arith
      + (1 - 2 * v.nr r_arith) * d_chunks_packed_div v r_arith
      + (v.nb r_arith * (1 - 2 * v.na r_arith) * a_chunks_packed_div v r_arith
          + v.na r_arith * (1 - 2 * v.nb r_arith) * b_chunks_packed_div v r_arith)
          * (65536 * 65536 * 65536 * 65536)
      + (v.nr r_arith - v.np r_arith) * (65536 * 65536 * 65536 * 65536)
      + v.na r_arith * v.nb r_arith
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * v.np r_arith) * c_chunks_packed_div v r_arith := by
  have h_secondary := h.1
  have h_chain := h.2.1
  have h_arith_mode := h_secondary.2.2.2.2
  have h_sext := h_arith_mode.2.2.2.1
  have h_m32 := h_arith_mode.2.2.2.2
  have h_div := h_arith_mode.2.2.1
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  exact arith_div_signed_packed_correct v r_arith
    h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
    h_sext h_m32 h_div

/-- **REM-signed field correctness (Main-level operands).** Lifts the
    signed-REM chunk identity to Main operand level. The remainder is
    `main_c_packed` (via `main_remainder_eq_chunks_rem`), divisor is
    `main_b_packed`, dividend is `main_a_packed`.

        (1 - 2*na - 2*nb + 4*na*nb) * a_chunks * main_b
        + (1 - 2*nr) * main_c
        + (nb*(1-2*na)*a_chunks + na*(1-2*nb)*main_b) * B^4
        + (nr - np) * B^4 + na*nb * B^8
        = (1 - 2*np) * main_a -/
theorem main_rem_signed_field_correct_main_level
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : rem_field_circuit_holds m v r_main r_arith opcode_lit) :
    (1 - 2 * v.na r_arith - 2 * v.nb r_arith + 4 * v.na r_arith * v.nb r_arith)
        * a_chunks_packed_div v r_arith * Spec.Add.main_b_packed m r_main
      + (1 - 2 * v.nr r_arith) * main_c_packed m r_main
      + (v.nb r_arith * (1 - 2 * v.na r_arith) * a_chunks_packed_div v r_arith
          + v.na r_arith * (1 - 2 * v.nb r_arith) * Spec.Add.main_b_packed m r_main)
          * (65536 * 65536 * 65536 * 65536)
      + (v.nr r_arith - v.np r_arith) * (65536 * 65536 * 65536 * 65536)
      + v.na r_arith * v.nb r_arith
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * v.np r_arith) * Spec.Add.main_a_packed m r_main := by
  -- Bridge 2: main_a = dividend = c_chunks, main_b = divisor = b_chunks,
  --           main_c = remainder = d_chunks
  have h_a_eq := main_dividend_eq_chunks_rem m v r_main r_arith opcode_lit h.1
  have h_b_eq := main_divisor_eq_chunks_rem m v r_main r_arith opcode_lit h.1
  have h_c_eq := main_remainder_eq_chunks_rem m v r_main r_arith opcode_lit h
  -- Core signed identity at chunk level
  have h_core := main_rem_signed_field_correct m v r_main r_arith opcode_lit h
  -- Rewrite h_core: replace b_chunks → main_b, d_chunks → main_c, c_chunks → main_a
  rw [← h_b_eq, ← h_c_eq, ← h_a_eq] at h_core
  exact h_core

end ZiskFv.Spec.DivFieldSigned
