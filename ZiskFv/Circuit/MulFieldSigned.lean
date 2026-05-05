import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.CarryChain
import ZiskFv.Airs.Arith.Bridge1
import ZiskFv.Airs.OperationBus
import ZiskFv.Circuit.Add
import ZiskFv.Circuit.Mul
import ZiskFv.Circuit.MulField

/-!
**Track N K4 — Bridge 2 (signed variant): Main ↔ Arith signed-MUL
field composition.**

Mirrors `Spec/MulField.lean`'s `main_mul_unsigned_field_correct` for the
**signed** MUL family (MULH/MUL with signed operands). Consumes
`arith_mul_signed_packed_correct` from `Airs/Arith/Mul.lean` and
composes it with the same Bridge 1 + bus-match chain as the unsigned case.

## What this provides

```
theorem main_mul_signed_field_correct
```

The signed-case packed identity over the Main AIR:

    (1 - 2*na - 2*nb + 4*na*nb) * a_packed * b_packed
    + (nb*(1-2*na)*a_packed + na*(1-2*nb)*b_packed) * 2^64
    + (na*nb - np) * 2^128
    = (1 - 2*np) * (c_packed + d_packed * 2^64)

where `a_packed = main_a_packed m r_main`, `b_packed = main_b_packed m r_main`,
`c_packed = main_c_packed m r_main`, and `d_packed = d_chunks_packed v r_arith`.

## Relationship to the unsigned theorem

`main_mul_unsigned_field_correct` (in `MulField.lean`) is the specialization
at `na = nb = np = nr = 0`. The signed theorem takes `na`, `nb`, `np` as
**free** witnesses — their assignment to operand sign bits is enforced by the
`arith_table` permutation lookup, which the caller supplies via an opcode
hypothesis. `nr` is zero for MUL (it is nonzero only for DIV).

## Usage by Phase 2 N-MDR-signed

Phase 2 derivation lemmas for MULH, MUL (signed), MULHSU will consume this
theorem plus:
- `arith_table_lookup_sound_mul` (for the signed sign-witness pinning)
- `Fundamentals/PackedBitVec/Signed.lean` (for the BitVec.toInt lift)
- `Fundamentals/PackedBitVec.lean` (for the byte-sum bridge)

to discharge `h_rd_val : U64.toBV #v[...] = execute_MUL_pure r1 r2 .MULH`.
-/

namespace ZiskFv.Circuit.MulFieldSigned

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.ArithBridge1
open ZiskFv.Airs.ArithCarryChain
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Mul
open ZiskFv.Circuit.MulField
open Arith.extraction

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Bundled signed-MUL field hypotheses.** Extends `mul_field_circuit_holds`
    (the same bus-match + carry-chain bundle used for unsigned MUL) for
    the signed case. The signed identity uses the same carry-chain constraints
    (6-8 sign prep + 31-38 carry chain), the same constraint 46, and the
    same bus-match predicate — the only difference is that `na`, `nb`, `np`
    are not pinned to zero. -/
@[simp]
def mul_signed_field_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ) : Prop :=
  mul_field_circuit_holds m v r_main r_arith

/-- **MUL-signed field correctness.** The full packed signed-MUL identity
    over the Main AIR. Takes `na`, `nb`, `np` as **free** witnesses
    (arith_table-pinned by transpile contract; the caller supplies them from
    the `arith_table_lookup_sound_mul` axiom). `nr` is zero for MUL.

    The conclusion is the field-level signed identity:

        (1 - 2*na - 2*nb + 4*na*nb) * a * b
        + (nb*(1-2*na)*a + na*(1-2*nb)*b) * 2^64
        + (na*nb - np) * 2^128
        = (1 - 2*np) * (c + d * 2^64)

    where `a = main_a_packed m r_main`, `b = main_b_packed m r_main`,
    `c = main_c_packed m r_main`, `d = d_chunks_packed v r_arith`.

    Composes Bridge 1 + Bridge 2 + `arith_mul_signed_packed_correct`.

    **Specializations.**
    * `na = nb = np = 0` ↔ unsigned (both operands non-negative): reduces to
      `a * b = c + d * 2^64` — exactly `main_mul_unsigned_field_correct`.
    * `na = 1, nb = 0, np = 1` ↔ rs1 negative, rs2 non-negative: the LHS
      encodes `(-|a|) * |b| = -(|a| * |b|)`.
    * `na = 0, nb = 1, np = 1` ↔ rs1 non-negative, rs2 negative: symmetric.
    * `na = 1, nb = 1, np = 0` ↔ both negative, result non-negative (or the
      overflow case `INT_MIN * -1`). -/
theorem main_mul_signed_field_correct
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h : mul_signed_field_circuit_holds m v r_main r_arith)
    (h_nr : v.nr r_arith = 0) :
    (1 - 2 * v.na r_arith - 2 * v.nb r_arith + 4 * v.na r_arith * v.nb r_arith)
        * Spec.Add.main_a_packed m r_main * Spec.Add.main_b_packed m r_main
      + (v.nb r_arith * (1 - 2 * v.na r_arith) * Spec.Add.main_a_packed m r_main
          + v.na r_arith * (1 - 2 * v.nb r_arith) * Spec.Add.main_b_packed m r_main)
          * (65536 * 65536 * 65536 * 65536)
      + (v.na r_arith * v.nb r_arith - v.np r_arith)
          * (65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536 * 65536)
      = (1 - 2 * v.np r_arith)
          * (main_c_packed m r_main
            + d_chunks_packed v r_arith * (65536 * 65536 * 65536 * 65536)) := by
  -- Unpack the circuit hypotheses.
  have h_circuit := h.1
  have h_chain := h.2.1
  have h_c46 := h.2.2
  have h_mode_arith := h_circuit.2.2.2.2
  have h_div := h_mode_arith.2.2.1
  have h_sext := h_mode_arith.2.2.2.1
  have h_m32_arith := h_mode_arith.2.2.2.2
  -- Unpack carry chain constraints.
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  -- Obtain the packed signed identity from the carry-chain closure.
  have h_packed := arith_mul_signed_packed_correct v r_arith
    h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
    h_nr h_sext h_m32_arith h_div
  -- Bridge 2: Main-side a/b equal Arith chunks packs.
  have h_a_eq := main_a_eq_chunks_mul m v r_main r_arith h_circuit
  have h_b_eq := main_b_eq_chunks_mul m v r_main r_arith h_circuit
  -- Bridge 1 ∘ mul_compositional: Main-side c equals Arith c chunks.
  have h_c_eq := main_c_eq_chunks_mul m v r_main r_arith h
  -- Rewrite a/b/c using the bridges.
  rw [h_a_eq, h_b_eq, h_c_eq]
  exact h_packed

end ZiskFv.Circuit.MulFieldSigned
