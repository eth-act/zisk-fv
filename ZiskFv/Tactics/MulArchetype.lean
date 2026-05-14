import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.ZiskCircuit.Mul

/-!
**Arith archetype macros / generic lemmas — MUL family.**

The MUL family (MUL, MULH, MULHU, MULHSU) all share the same Zisk
microinstruction shape — `create_register_op(..., <op_str>, 4)` at
`zisk/core/src/riscv2zisk_context.rs:243-246`. The only
per-opcode differences are:

* The Zisk opcode literal:
    * MUL     → `OP_MUL = 180` (`0xb4`),
    * MULH    → `OP_MULH = 181` (`0xb5`),
    * MULHU   → `OP_MULUH = 177` (`0xb1`, renamed by the transpiler),
    * MULHSU  → `OP_MULSUH = 179` (`0xb3`, renamed).
* The Arith-side output lane — low 64 bits for MUL, high 64 bits for the
  MULH variants. Both land on `c_lo = c[0] + c[1]*2^16`, `c_hi =
  bus_res1` on the bus, so the bus projection is identical; the
  difference lives in the result-selector (`main_mul` / secondary) and
  the sign witnesses (`na` / `nb` / `np` / `nr`) that the underlying
  carry-chain constraints consume. From the compositional proof's
  perspective these are all uniform: the bus match + mode witnesses
  give Main's `c` = Arith's packed result; the Arith-internal
  correctness (low vs. high half, signed vs. unsigned) is a separate
  audit obligation.
* The Sail-side `execute_MUL` match arm: RV64's `instruction.MUL`
  discriminant carries the `result_part` and `signed_rs1`/`signed_rs2`
  fields that dispatch in `execute_MUL_pure`. Per-opcode equivalence
  proofs fix these fields (`.Low` vs. `.High`, `.Signed` vs.
  `.Unsigned`).

This module packages the reusable circuit-side piece as an archetype
lemma (`mul_archetype_bus_match`) parameterized by an `opcode_lit : FGL`.
MUL currently uses `Circuit.Mul.mul_compositional` directly; MULH / MULHU
/ MULHSU call `mul_archetype_bus_match` with their own `opcode_lit`.

## Usage pattern

```
-- MULH case (op = OP_MULH = 181):
theorem equiv_MULH (...) := by
  have h_bus_match :=
    mul_archetype_bus_match m v r_main r_arith OP_MULH h_circuit_mulh
  ...
```

The `mul_archetype_proof` tactic macro below is a convenience wrapper
that produces the bus-match identity given a
`mul_archetype_circuit_holds`-shaped hypothesis in scope.
-/

namespace ZiskFv.Tactics.MulArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.ZiskCircuit.Mul

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Archetype mode predicate (Main side).** A Main row is in MUL-family
    execution mode when `is_external_op = 1`, `op = opcode_lit`,
    `m32 = 0` (64-bit operands — MULW is out of scope and uses
    `m32 = 1`), `flag = 0` (div_by_zero = 0), and `set_pc = 0`.

    `opcode_lit` is one of `OP_MUL`, `OP_MULH`, `OP_MULUH`, `OP_MULSUH`
    — parameterizing the archetype over the exact Zisk opcode literal. -/
@[simp]
def main_row_in_mul_archetype_mode
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (opcode_lit : FGL) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- **Archetype circuit-holds (parametric over opcode).** Packs the
    ADD-subset Main constraints + Arith MUL-mode booleans + bus match
    + Main mode witnesses + Arith mode witnesses. `Circuit.Mul.mul_circuit_holds`
    is a specialization at `opcode_lit = OP_MUL`. -/
@[simp]
def mul_archetype_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL) : Prop :=
  add_subset_holds m r_main
  ∧ mul_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_Arith v r_arith)
  ∧ main_row_in_mul_archetype_mode m r_main opcode_lit
  ∧ arith_row_in_mul_mode v r_arith

/-- **Archetype bus-match theorem.** Parametric version of
    `Circuit.Mul.mul_compositional`. Same proof skeleton: destruct the
    bus-match equalities, substitute into Main's packed `c`, close.

    Result: Main's packed `c` equals Arith's packed result lanes,
    independent of which MUL-family opcode is on the Main row. -/
lemma mul_archetype_bus_match
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ) (opcode_lit : FGL)
    (h : mul_archetype_circuit_holds m v r_main r_arith opcode_lit) :
    main_c_packed m r_main = arith_c_packed v r_arith := by
  obtain ⟨_h_main_subset, _h_arith_bool, h_bus, h_mode_main, _h_mode_arith⟩ := h
  obtain ⟨_, _, _, _, _, _, h_match_clo, h_match_chi, _, _, _, _⟩ := h_bus
  obtain ⟨_h_isext, _h_op, h_m32, _h_flag, _h_setpc⟩ := h_mode_main
  simp only [opBus_row_Main, opBus_row_Arith] at h_match_clo h_match_chi
  unfold main_c_packed arith_c_packed
  rw [h_match_clo, h_match_chi]

end ZiskFv.Tactics.MulArchetype
