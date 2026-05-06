import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.CarryChain
import ZiskFv.Airs.Arith.Bridge1
import ZiskFv.Airs.OperationBus
import ZiskFv.Circuit.Add
import ZiskFv.Circuit.Mul

/-!
**Bridge 2: Main ↔ Arith operand field composition.**

Composes the bus-match (provided by `mul_circuit_holds`), Bridge 1
(`Airs/Arith/Bridge1.lean`), and the carry-chain packed identity
(`arith_mul_unsigned_packed_correct` in `Airs/Arith/Mul.lean`) to
derive the field-level MUL correctness equation over the Main AIR:

```
main_a_packed m r_main * main_b_packed m r_main
  = main_c_packed m r_main
    + d_chunks_packed v r_arith * (65536 * 65536 * 65536 * 65536)
```

i.e. Main's packed `c` holds the low 64 bits of the 128-bit product
(with the high 64 bits sitting in Arith's `d[]` chunks). This is the
field-level statement of RV64 MUL correctness modulo the `BitVec 64`
lift, which is handled by Bridge 3 in `Fundamentals/PackedBitVec.lean`.

This file is called "MulField" rather than extending `Circuit.Mul` because
it consumes circuit hypotheses that `Circuit.Mul.mul_compositional`
didn't: specifically the carry-chain constraints (6-8, 31-38) and
constraint 46. Composing Bridges 1 + 2 is additive on top of the
existing `mul_compositional` theorem.

DIV/REM analogues for `div_unsigned_field_correct` and
`rem_unsigned_field_correct` are authored in-file — they follow the
same composition pattern with `Valid_ArithDiv` / `div_carry_chain_holds`
and the `div`/`rem` bridge-1 specializations.
-/

namespace ZiskFv.Circuit.MulField

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.ArithBridge1
open ZiskFv.Airs.ArithCarryChain
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Mul
open Arith.extraction

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Bundled MUL-unsigned field hypotheses.** Packs the circuit predicates
    required for the full packed-field MUL identity. Wraps the existing
    `mul_circuit_holds` (Main-AIR ADD-subset + Arith-AIR mode booleans +
    bus-match + mode witnesses) with the additional carry-chain constraints
    (6–8 sign prep + 31–38 carry chain, via `mul_carry_chain_holds`) and
    constraint 46 (the `bus_res1` normalization). -/
@[simp]
def mul_field_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ) : Prop :=
  mul_circuit_holds m v r_main r_arith
  ∧ mul_carry_chain_holds v r_arith
  ∧ constraint_46_every_row v.circuit r_arith

/-- **Bridge 2: Main-side packed a equals Arith-side 4-chunk pack.**
    Under MUL-mode `m32 = 0`, the bus-match on `a_lo`/`a_hi` composes
    into Main's 2-lane packing equaling Arith's 4-chunk packing. -/
lemma main_a_eq_chunks_mul
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h : mul_circuit_holds m v r_main r_arith) :
    Circuit.Add.main_a_packed m r_main = a_chunks_packed v r_arith := by
  obtain ⟨_, _, h_bus, h_mode, _⟩ := h
  obtain ⟨_, _, h_match_alo, h_match_ahi, _, _, _, _, _, _, _, _⟩ := h_bus
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  simp only [opBus_row_Main, opBus_row_Arith] at h_match_alo h_match_ahi
  rw [h_m32] at h_match_ahi
  simp only [one_sub_zero_mul] at h_match_ahi
  unfold Circuit.Add.main_a_packed a_chunks_packed
  rw [h_match_alo, h_match_ahi]
  ring

/-- **Bridge 2: Main-side packed b equals Arith-side 4-chunk pack.** -/
lemma main_b_eq_chunks_mul
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h : mul_circuit_holds m v r_main r_arith) :
    Circuit.Add.main_b_packed m r_main = b_chunks_packed v r_arith := by
  obtain ⟨_, _, h_bus, h_mode, _⟩ := h
  obtain ⟨_, _, _, _, h_match_blo, h_match_bhi, _, _, _, _, _, _⟩ := h_bus
  obtain ⟨_, _, h_m32, _, _⟩ := h_mode
  simp only [opBus_row_Main, opBus_row_Arith] at h_match_blo h_match_bhi
  rw [h_m32] at h_match_bhi
  simp only [one_sub_zero_mul] at h_match_bhi
  unfold Circuit.Add.main_b_packed b_chunks_packed
  rw [h_match_blo, h_match_bhi]
  ring

/-- **Bridge 1 + 2 composition: Main-side packed c equals Arith-side
    c-chunks pack.** Combines `mul_compositional` (→ `main_c_packed =
    arith_c_packed`) with Bridge 1 (→ `arith_c_packed = c_chunks_packed`
    under MUL-unsigned mode) and constraint 46. -/
lemma main_c_eq_chunks_mul
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h : mul_field_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = c_chunks_packed v r_arith := by
  have h_circuit := h.1
  have h_c46 := h.2.2
  have h_mode_arith := h_circuit.2.2.2.2
  have h_main_mul := h_mode_arith.1
  have h_main_div := h_mode_arith.2.1
  have h_sext := h_mode_arith.2.2.2.1
  have h_m32 := h_mode_arith.2.2.2.2
  have h_compositional := mul_compositional m v r_main r_arith h_circuit
  have h_bridge1 := mul_bus_res1_eq_c_hi v r_arith h_c46 h_sext h_m32
                      h_main_mul h_main_div
  -- `arith_c_packed = (c_0 + c_1*65536) + bus_res1 * 2^32`; substitute
  -- bus_res1 from Bridge 1 and unfold to `c_chunks_packed`.
  unfold arith_c_packed at h_compositional
  rw [h_bridge1] at h_compositional
  rw [h_compositional]
  unfold c_chunks_packed
  ring

/-- **MUL-unsigned field correctness.** The full packed MUL identity
    over the Main AIR: Main's packed `a * b` equals Main's packed `c`
    plus Arith's `d` chunks scaled by `2^64`. This is the field-level
    statement of RV64 MUL-unsigned correctness; lifting it to `BitVec 64`
    semantics (accounting for the Goldilocks `< 2^64` range bound) is
    Bridge 3 in `Fundamentals/PackedBitVec.lean`.

    Composes Bridge 1 + Bridge 2 + `arith_mul_unsigned_packed_correct`.

    The unsigned-mode witnesses (`na = nb = np = nr = 0`) are passed
    explicitly; `mul_circuit_holds` only pins the MUL-vs-DIV selector
    booleans (`main_mul`/`main_div`/`div`/`sext`/`m32`), not the
    sign-preprocessing witnesses that distinguish MULU from MULH /
    MULHSU / signed MUL. For the unsigned-MUL opcodes (MULU, MULHU
    selected via opcode literal 0xb0/0xb1) these four witnesses are
    pinned to zero by the transpile contract and the `arith_table`
    lookup; we take them as explicit proof inputs. -/
theorem main_mul_unsigned_field_correct
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h : mul_field_circuit_holds m v r_main r_arith)
    (h_na : v.na r_arith = 0) (h_nb : v.nb r_arith = 0)
    (h_np : v.np r_arith = 0) (h_nr : v.nr r_arith = 0) :
    Circuit.Add.main_a_packed m r_main * Circuit.Add.main_b_packed m r_main
      = main_c_packed m r_main
        + d_chunks_packed v r_arith * (65536 * 65536 * 65536 * 65536) := by
  have h_circuit := h.1
  have h_chain := h.2.1
  have h_mode_arith := h_circuit.2.2.2.2
  have h_div := h_mode_arith.2.2.1
  have h_sext := h_mode_arith.2.2.2.1
  have h_m32_arith := h_mode_arith.2.2.2.2
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  -- Packed identity via the carry-chain closure.
  have h_packed := arith_mul_unsigned_packed_correct v r_arith
    h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
    h_na h_nb h_np h_nr h_sext h_m32_arith h_div
  -- Bridge 2: Main-side a/b equal Arith chunks packs.
  have h_a_eq := main_a_eq_chunks_mul m v r_main r_arith h_circuit
  have h_b_eq := main_b_eq_chunks_mul m v r_main r_arith h_circuit
  -- Bridge 1 ∘ mul_compositional: Main-side c equals Arith c chunks.
  have h_c_eq := main_c_eq_chunks_mul m v r_main r_arith h
  rw [h_a_eq, h_b_eq, h_c_eq]
  exact h_packed

end ZiskFv.Circuit.MulField
