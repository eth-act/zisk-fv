import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.OperationBus.OperationBus

/-!
Compositional MUL spec: given the named ADD-subset Main constraints
(reused verbatim — MUL shares the same external-op boolean + flag/op/m32
predicates as ADD), the named Arith-subset mul-mode booleans, and the
operation-bus matching between the two rows, Main's `(c_lo, c_hi)` lanes
equal Arith's packed result lanes (`c[0] + c[1]*2^16`, `bus_res1`).

**Parameterization.** Unlike `Circuit.Add`, which derives Main's
packed `c` from BinaryAdd's carry chain, `Circuit.Mul` **does not derive**
the multiplication from Arith's carry chains (constraints 31–38). That
derivation — which would unfold the 8-chunk byte-level decomposition to
`BitVec 128` arithmetic — is delegated to the audit. Instead we
parameterize on the bus-match hypothesis: the proof states that *if*
Main and Arith emit matching bus entries, then Main's `c` lanes are
exactly Arith's packed result. The separate Arith-correctness claim
(Arith's `c[]` = low 64 bits of `a*b` for MUL) is an unresolved
obligation discharged by the audit (the carry chains entail
multiplication).

This mirrors BEQ's treatment of the Binary SM's `flag` bit — both
archetypes exercise a secondary state machine whose internal
correctness is proved *outside* the archetype's scope.
-/

namespace ZiskFv.ZiskCircuit.Mul

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted


/-- The Main row at `r_main` is in MUL-execution mode: external op with
    opcode literal 180 (OP_MUL), full 64-bit width (m32 = 0), `flag = 0`
    (MUL's Arith-side flag is `div_by_zero`, always 0 on MUL rows), and
    no PC write (`set_pc = 0`). -/
@[simp]
def main_row_in_mul_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = OP_MUL
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- The Arith row at `r_arith` is in MUL-primary execution mode:
    `main_mul = 1`, `main_div = 0`, `div = 0` (it's a multiplication,
    not a division), `sext = 0` (no sign-extension — MULW uses sext=1
    and is out of scope), `m32 = 0` (64-bit operand form). -/
@[simp]
def arith_row_in_mul_mode (v : Valid_ArithMul FGL FGL) (r_arith : ℕ) : Prop :=
  v.main_mul r_arith = 1
  ∧ v.main_div r_arith = 0
  ∧ v.div r_arith = 0
  ∧ v.sext r_arith = 0
  ∧ v.m32 r_arith = 0

/-- All hypotheses needed by `mul_compositional`: the ADD-subset Main
    constraints (MUL reuses the same booleans), the MUL-mode boolean
    constraints on Arith, the bus-row match between the two rows, and
    the mode witnesses on both sides. -/
@[simp]
def mul_circuit_holds
    (m : Valid_Main FGL FGL) (v : Valid_ArithMul FGL FGL)
    (r_main r_arith : ℕ) : Prop :=
  add_subset_holds m r_main
  ∧ mul_mode_booleans v r_arith
  ∧ matches_entry (opBus_row_Main m r_main) (opBus_row_Arith v r_arith)
  ∧ main_row_in_mul_mode m r_main
  ∧ arith_row_in_mul_mode v r_arith

/-- The 64-bit value packed into Arith's `(c[0], c[1], c[2], c[3])`
    chunks, treated as a single Goldilocks element. For MUL-primary
    this is the low 64 bits of `a * b`. -/
@[simp]
def arith_c_packed (v : Valid_ArithMul FGL FGL) (r : ℕ) : FGL :=
  (v.c_0 r + v.c_1 r * 65536) + v.bus_res1 r * 4294967296

/-- The 64-bit value packed into the Main row's `(c_0, c_1)` lanes. -/
@[simp]
def main_c_packed (m : Valid_Main FGL FGL) (r : ℕ) : FGL :=
  m.c_0 r + m.c_1 r * 4294967296

/-- **Compositional MUL theorem.** If the MUL circuit-holds predicate
    holds — the Main ADD-subset constraints + Arith's MUL-mode booleans +
    the bus-row match + the mode witnesses — then Main's packed `c`
    equals Arith's packed result lanes:

    `main_c_packed = arith_c_packed = (c[0] + c[1]*2^16) + bus_res1 * 2^32`.

    This is the Main↔Arith bus-projection identity for MUL. The lifting
    from this field-level identity to the `BitVec 64` semantics of RV64
    MUL happens in `Equivalence.Mul`, which parameterizes on an Arith-
    correctness hypothesis (left to the audit). -/
lemma mul_compositional
    (m : Valid_Main FGL FGL) (v : Valid_ArithMul FGL FGL)
    (r_main r_arith : ℕ)
    (h : mul_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_c_packed v r_arith := by
  obtain ⟨_h_main_subset, _h_arith_bool, h_bus, h_mode_main, _h_mode_arith⟩ := h
  -- Extract the lane-match equalities from the bus match.
  obtain ⟨_, _, _, _, _, _, h_match_clo, h_match_chi, _, _, _, _⟩ := h_bus
  obtain ⟨_h_isext, _h_op, h_m32, _h_flag, _h_setpc⟩ := h_mode_main
  -- Unfold the bus-row emissions so we can compare their `c_lo` / `c_hi`
  -- fields. On Main's side `c_lo := m.c_0 r` and `c_hi := m.c_1 r`;
  -- on Arith's side `c_lo := v.c_0 r + v.c_1 r * 2^16` and `c_hi :=
  -- v.bus_res1 r`. The `a_hi` / `b_hi` `(1 - m32) *` factors are
  -- irrelevant for the `c` identity but the `c_hi` match gives us
  -- exactly what we need.
  simp only [opBus_row_Main, opBus_row_Arith] at h_match_clo h_match_chi
  -- Substitute the bus-derived equalities into Main's packed c.
  unfold main_c_packed arith_c_packed
  rw [h_match_clo, h_match_chi]

end ZiskFv.ZiskCircuit.Mul
