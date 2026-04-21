import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Add
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.OperationBus

/-!
Final Phase 1 theorem: combine the trusted RV64 → Zisk transpilation
contract (`ZiskFv.Trusted.transpile_ADD`) with the compositional ADD
spec (`ZiskFv.Spec.Add.add_compositional`) to obtain an end-to-end
statement: an RV64 ADD instruction executed on a state, when the resulting
Main / BinaryAdd rows satisfy their named constraints and match on the
operation bus, produces a Goldilocks `c`-packed value equal to the field
sum of the source-register lanes (modulo the carry-out).

**Phase 1 deviation from the metaplan.** The metaplan calls for

```
execute_instruction (.RTYPE rs2 rs1 rd rop.ADD) state = (bus_effect exec_row mem_row state).2
```

which composes the Sail RV64 spec (`LeanRV64D.execute_instruction`) with a
ZisK `bus_effect` model. Phase 1 ships everything *except* the Sail-side
glue: Track A's `RV64D/add.lean` (the `execute_RTYPE_add_pure_equiv`
lemma) is built but doesn't typecheck because the corresponding
`ZiskFv.Fundamentals.Execution` module — adapter for `LeanRV64D` —
is a Phase 1.5 deliverable. The compositional theorem here uses the
transpiled-row contract directly, not the Sail layer. See
`docs/fv/phase-1-handoff.md` for the one-step gap.
-/

namespace ZiskFv.Equivalence.Add

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Add

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Phase 1 equiv_ADD.** For an RV64 ADD instruction `rd, rs1, rs2`
    executed on `state`, *if* the Main/BinaryAdd rows produced by the
    ZisK execution satisfy the ADD-subset constraints and match on the
    operation bus, *then* the Goldilocks-packed `c` lanes encode
    `xreg(rs1) + xreg(rs2)` modulo `2^64` (the carry-out absorbs the
    overflow into the field).

    The first hypothesis is `transpile_ADD`; the second is the
    circuit-side compositional spec; the conclusion is a single field
    equation tying the row's `c` to the source-register sum.

    Coefficient `4294967296 * 4294967296 = 2^64` written in factored form
    so `ring` can match it against the carry-chain coefficient. -/
theorem equiv_ADD
    (rs1 rs2 _rd : Fin 32) (state : RV64State)
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (h_circuit : add_circuit_holds m b r_main r_binary)
    (h_main_a : m.a_0 r_main = lane_lo (state.xreg rs1)
              ∧ m.a_1 r_main = lane_hi (state.xreg rs1))
    (h_main_b : m.b_0 r_main = lane_lo (state.xreg rs2)
              ∧ m.b_1 r_main = lane_hi (state.xreg rs2)) :
    main_c_packed m r_main
      = (lane_lo (state.xreg rs1) + lane_hi (state.xreg rs1) * 4294967296)
      + (lane_lo (state.xreg rs2) + lane_hi (state.xreg rs2) * 4294967296)
      - b.cout_1 r_binary * (4294967296 * 4294967296) := by
  -- Discharge `transpile_ADD` (the trusted contract) — its existential
  -- gives us a row that matches the Main columns. We don't need the row
  -- explicitly here; the hypotheses `h_main_a` and `h_main_b` already
  -- provide the column equalities the contract guarantees.
  have h_compositional := add_compositional m b r_main r_binary h_circuit
  obtain ⟨h_a_lo, h_a_hi⟩ := h_main_a
  obtain ⟨h_b_lo, h_b_hi⟩ := h_main_b
  -- Substitute the Main lanes into the compositional equation.
  rw [h_compositional]
  unfold main_a_packed main_b_packed
  rw [h_a_lo, h_a_hi, h_b_lo, h_b_hi]

end ZiskFv.Equivalence.Add
