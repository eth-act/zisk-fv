import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus
import ZiskFv.Spec.Mul

/-!
Compositional MULW spec (Phase 3A M3). MULW is the 32-bit word variant of
MUL: low 32 bits of each source are multiplied as 32-bit operands, the
low 32 bits of the product are sign-extended to 64. The Zisk side wires
this through the **same Arith SM** as MUL (not BinaryExtension) but with
two mode bits flipped: `m32 = 1` (32-bit operand width) and `sext = 1`
(the Arith SM internally sign-extends the 32-bit output to 64).

Unlike MULHU / MULHSU (siblings that reuse `Tactics.MulArchetype` at a
different opcode literal), MULW **cannot instantiate the macro**: the
archetype's `main_row_in_mul_archetype_mode` predicate hardcodes
`m32 = 0`. We take the same Option-(a) path `Spec.Shift` took for SLLW
(which was the first `m32 = 1` opcode): inline the compositional
derivation with MULW-specific mode predicates.

The core observation: the bus `c_lo`/`c_hi` match is **independent** of
`m32` / `sext`. Main's `c_0`/`c_1` lanes and Arith's
`c[0]/c[1]/bus_res1` lanes speak the same packed-64 value regardless of
whether Arith's internal carry chains computed a 64-bit or a
sign-extended-32-bit result. The `(1 - m32)` factor in `opBus_row_Main`
applies only to `a_hi`/`b_hi` (zeroing operand high lanes on the bus
for 32-bit ops); the `c` lanes are forwarded verbatim. So the
compositional bus-projection identity closes by the same
`h_match_clo`/`h_match_chi` rewrite that MUL / MULH / MULHU / MULHSU
use.

The Arith-internal claim — that for MULW Arith's `c[]` + `bus_res1`
packs `sign_extend_32_to_64 (low32 a * low32 b)` — is (as always)
delegated to Phase 4 audit.
-/

namespace ZiskFv.Spec.MulW

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Spec.Mul

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in MULW-execution mode: external op with
    opcode literal 182 (`OP_MUL_W`), 32-bit width (`m32 = 1`), `flag = 0`
    (div_by_zero), and `set_pc = 0`. Distinguished from MUL/MULH/MULHU/
    MULHSU by the `m32 = 1` bit. -/
@[simp]
def main_row_in_mulw_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = OP_MUL_W
  ∧ m.m32 r_main = 1
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- The Arith row at `r_arith` is in MULW-primary execution mode: the
    full MUL-primary bits (`main_mul = 1`, `main_div = 0`, `div = 0`)
    plus the 32-bit variant pair (`sext = 1`, `m32 = 1`). -/
@[simp]
def arith_row_in_mulw_mode (v : Valid_ArithMul C FGL FGL) (r_arith : ℕ) : Prop :=
  v.main_mul r_arith = 1
  ∧ v.main_div r_arith = 0
  ∧ v.div r_arith = 0
  ∧ v.sext r_arith = 1
  ∧ v.m32 r_arith = 1

/-- All hypotheses needed by `mulw_compositional`. Packs the ADD-subset
    Main constraints, the MUL-mode Arith booleans (same predicate as
    MUL/MULH — `main_mul` vs. `main_div` disjoint, the boolean
    constraints on `m32` / `sext` / `div`), the bus-row match, and the
    MULW mode witnesses on both AIRs. -/
@[simp]
def mulw_circuit_holds
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ) : Prop :=
  add_subset_holds m r_main
  ∧ mul_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_Arith v r_arith)
  ∧ main_row_in_mulw_mode m r_main
  ∧ arith_row_in_mulw_mode v r_arith

/-- **Compositional MULW theorem.** If the MULW circuit-holds predicate
    holds, then Main's packed `c` lanes equal Arith's packed result lanes.

    Same proof skeleton as `Spec.Mul.mul_compositional` — the `m32 = 1`
    bit does not affect the `c` bus lanes, only the `a_hi`/`b_hi`
    operand-bus zeroing (which is irrelevant to this `c`-projection
    identity). The Arith-internal correctness (MULW carry chains →
    sign-extended 32-bit product) is delegated to Phase 4. -/
theorem mulw_compositional
    (m : Valid_Main C FGL FGL) (v : Valid_ArithMul C FGL FGL)
    (r_main r_arith : ℕ)
    (h : mulw_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_c_packed v r_arith := by
  obtain ⟨_h_main_subset, _h_arith_bool, h_bus, _h_mode_main, _h_mode_arith⟩ := h
  obtain ⟨_, _, _, _, _, _, h_match_clo, h_match_chi, _, _, _, _⟩ := h_bus
  simp only [opBus_row_Main, opBus_row_Arith] at h_match_clo h_match_chi
  unfold main_c_packed arith_c_packed
  rw [h_match_clo, h_match_chi]

end ZiskFv.Spec.MulW
