import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.ZiskCircuit.Mul

/-!
**Arith state-machine archetype — DIV/REM subfamily.**

The DIV family (DIV, DIVU, REM, REMU) all share the same Zisk
microinstruction shape — `create_register_op(..., <op_str>, 4)` at
`zisk/core/src/riscv2zisk_context.rs:248-253`. The only
per-opcode differences are:

* The Zisk opcode literal:
    * DIVU → `OP_DIVU = 184` (`0xb8`),
    * REMU → `OP_REMU = 185` (`0xb9`),
    * DIV  → `OP_DIV  = 186` (`0xba`),
    * REM  → `OP_REM  = 187` (`0xbb`).
* Which Arith-side output lane encodes the bus result:
    * DIV / DIVU (**primary**, `main_div = 1`): quotient in `a[]` →
      `bus_res0 = a[0] + a[1]*2^16`, `bus_res1_64 = a[2] + a[3]*2^16`.
    * REM / REMU (**secondary**, `main_mul = main_div = 0`): remainder
      in `d[]` → `bus_res0 = d[0] + d[1]*2^16`,
      `bus_res1_64 = d[2] + d[3]*2^16`.
* The sign witnesses (`na` / `nb` / `np` / `nr`). From the compositional
  proof's perspective these are uniform: the bus-match identity + mode
  witnesses give Main's `c` = Arith's packed result (quotient or
  remainder per selector).

As with MUL archetype, the Arith-internal correctness — "the `a[]` /
`d[]` chunks are the correct quotient/remainder of `a*b + d = c` with
the division carry chains" — is a separate audit obligation; it
enters the end-to-end proof as an axiomatic hypothesis. This archetype
only proves the bus-match identity.

Two archetype lemmas:

* `arith_archetype_div_bus_match` — for DIV/DIVU (primary). Main's
  packed c matches Arith's packed `(a[0] + a[1]*2^16) + bus_res1 * 2^32`.
* `arith_archetype_rem_bus_match` — for REM/REMU (secondary). Main's
  packed c matches Arith's packed `(d[0] + d[1]*2^16) + bus_res1 * 2^32`.

Both mirror `Tactics.MulArchetype.mul_archetype_bus_match` structurally.
-/

namespace ZiskFv.Tactics.ArithSMArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.ZiskCircuit.Mul


/-- **Archetype mode predicate (Main side).** A Main row is in DIV-family
    execution mode when `is_external_op = 1`, `op = opcode_lit`,
    `m32 = 0` (64-bit operands — divu_w/div_w out of scope), `flag = 0`
    (div_by_zero = 0 — non-div-by-zero case is our archetype scope),
    and `set_pc = 0`.

    `opcode_lit` is one of `OP_DIVU`, `OP_REMU`, `OP_DIV`, `OP_REM`. -/
@[simp]
def main_row_in_div_archetype_mode
    (m : Valid_Main FGL FGL) (r_main : ℕ) (opcode_lit : FGL) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- **Archetype Arith-primary mode predicate (DIV / DIVU).** For DIV
    rows driving a primary bus emission (`main_div = 1`): `div = 1`
    marks the row as a division (vs. multiplication), `main_div = 1`
    selects quotient (`a[]`) as the bus `c` lane, `main_mul = 0`,
    `sext = 0` (64-bit non-sign-extending), `m32 = 0` (64-bit). -/
@[simp]
def arith_row_in_div_primary_mode (v : Valid_ArithDiv FGL FGL) (r_arith : ℕ) : Prop :=
  v.main_div r_arith = 1
  ∧ v.main_mul r_arith = 0
  ∧ v.div r_arith = 1
  ∧ v.sext r_arith = 0
  ∧ v.m32 r_arith = 0

/-- **Archetype Arith-secondary mode predicate (REM / REMU).** For DIV
    rows driving a secondary bus emission (`secondary = 1`, i.e.
    `main_div = main_mul = 0`): `div = 1`, `main_div = 0`, `main_mul = 0`,
    `sext = 0`, `m32 = 0`. -/
@[simp]
def arith_row_in_rem_secondary_mode (v : Valid_ArithDiv FGL FGL) (r_arith : ℕ) : Prop :=
  v.main_div r_arith = 0
  ∧ v.main_mul r_arith = 0
  ∧ v.div r_arith = 1
  ∧ v.sext r_arith = 0
  ∧ v.m32 r_arith = 0

/-- **Archetype circuit-holds — DIV/DIVU (primary).** Packs the Main
    ADD-subset constraints + Arith DIV-mode booleans + bus match
    (using `opBus_row_ArithDiv`, the primary projection) + mode
    witnesses on both sides. -/
@[simp]
def div_primary_circuit_holds
    (m : Valid_Main FGL FGL) (v : Valid_ArithDiv FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL) : Prop :=
  add_subset_holds m r_main
  ∧ div_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_ArithDiv v r_arith)
  ∧ main_row_in_div_archetype_mode m r_main opcode_lit
  ∧ arith_row_in_div_primary_mode v r_arith

/-- **Archetype circuit-holds — REM/REMU (secondary).** Same as the
    primary version except the bus match uses
    `opBus_row_ArithDivSecondary` (remainder in `d[]`) and the mode
    predicate is `arith_row_in_rem_secondary_mode`. -/
@[simp]
def rem_secondary_circuit_holds
    (m : Valid_Main FGL FGL) (v : Valid_ArithDiv FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL) : Prop :=
  add_subset_holds m r_main
  ∧ div_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_ArithDivSecondary v r_arith)
  ∧ main_row_in_div_archetype_mode m r_main opcode_lit
  ∧ arith_row_in_rem_secondary_mode v r_arith

/-- The 64-bit value packed into Arith's `(a[0], a[1], a[2], a[3])`
    chunks, treated as a single Goldilocks element. For DIV/DIVU
    primary rows this is the quotient `a DIV b`.

    The `bus_res1` column is the range-checked 32-bit view of the high
    half — on non-sign-extending 64-bit rows (sext = 0, m32 = 0) it
    equals `a[2] + a[3]*2^16` per constraint 46. -/
@[simp]
def arith_quotient_packed (v : Valid_ArithDiv FGL FGL) (r : ℕ) : FGL :=
  (v.a_0 r + v.a_1 r * 65536) + v.bus_res1 r * 4294967296

/-- The 64-bit value packed into Arith's `(d[0], d[1], d[2], d[3])`
    chunks. For REM/REMU secondary rows this is the remainder.

    `bus_res1` at sext = 0, m32 = 0 equals `d[2] + d[3]*2^16` — on
    secondary rows constraint 46 reduces to
    `bus_res1 = (1 - main_mul - main_div) * (d[2] + d[3]*2^16)` = d-high. -/
@[simp]
def arith_remainder_packed (v : Valid_ArithDiv FGL FGL) (r : ℕ) : FGL :=
  (v.d_0 r + v.d_1 r * 65536) + v.bus_res1 r * 4294967296

/-- **Archetype bus-match theorem — primary (DIV/DIVU).** Parametric
    version of the compositional bus-match identity for the DIV
    subfamily's primary path. Same proof skeleton as
    `Tactics.MulArchetype.mul_archetype_bus_match` — destruct the
    bus-match equalities, substitute into Main's packed `c`, close. -/
lemma arith_archetype_div_bus_match
    (m : Valid_Main FGL FGL) (v : Valid_ArithDiv FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : div_primary_circuit_holds m v r_main r_arith opcode_lit) :
    main_c_packed m r_main = arith_quotient_packed v r_arith := by
  obtain ⟨_h_main_subset, _h_arith_bool, h_bus, _h_mode_main, _h_mode_arith⟩ := h
  obtain ⟨_, _, _, _, _, _, h_match_clo, h_match_chi, _, _, _, _⟩ := h_bus
  simp only [opBus_row_Main, opBus_row_ArithDiv] at h_match_clo h_match_chi
  unfold main_c_packed arith_quotient_packed
  rw [h_match_clo, h_match_chi]

/-- **Archetype bus-match theorem — secondary (REM/REMU).** Same proof
    skeleton as the primary theorem, but binds Main's packed `c` to
    the remainder lanes (Arith's `d[]`). -/
lemma arith_archetype_rem_bus_match
    (m : Valid_Main FGL FGL) (v : Valid_ArithDiv FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : rem_secondary_circuit_holds m v r_main r_arith opcode_lit) :
    main_c_packed m r_main = arith_remainder_packed v r_arith := by
  obtain ⟨_h_main_subset, _h_arith_bool, h_bus, _h_mode_main, _h_mode_arith⟩ := h
  obtain ⟨_, _, _, _, _, _, h_match_clo, h_match_chi, _, _, _, _⟩ := h_bus
  simp only [opBus_row_Main, opBus_row_ArithDivSecondary] at h_match_clo h_match_chi
  unfold main_c_packed arith_remainder_packed
  rw [h_match_clo, h_match_chi]

end ZiskFv.Tactics.ArithSMArchetype
