import ZiskFv.AirsClean.BinaryAdd.Soundness
import ZiskFv.Airs.Binary.BinaryAdd

/-!
# `Valid_BinaryAdd` ↔ `BinaryAddRow` compatibility bridge

Connects the existing `Valid_BinaryAdd` interface (a record with
named column accessors `ℕ → FGL`) to the Clean Component's
`BinaryAddRow` (a `ProvableStruct` with field values at one row).

The bridge:

* `rowAt v r` — project `Valid_BinaryAdd` at row `r` into a
  `BinaryAddRow FGL` (the Clean Component's row type)
* `soundness_of_valid v r` — if `Assumptions (rowAt v r)` holds and
  the four BinaryAdd constraints fire at row `r`, then `Spec (rowAt v r)`.
  This is exactly the existing constraint-discharge path expressed
  through the Clean Component's Soundness.

## Trust note

No axioms added. This is the bridge that Phase 5's
the Compliance dispatch layer will use to dispatch via the Clean Component's
Soundness instead of the spike's bespoke per-AIR proofs.

The actual retirement of `binary_add_columns_in_range` (the one
BinaryAdd-specific axiom in `trust/baseline-axioms.txt`) requires
the full FlatEnsemble's RangeBus channel-balance discharge —
deferred to Phase 5. For now this Bridge demonstrates the
*architectural* connection.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks


/-- Project a `Valid_BinaryAdd` at row `r` into a Clean
    `BinaryAddRow FGL`. The 10 witness columns map 1:1; stage-2
    accumulators (`gsum`, `im_0`, `im_1`) are dropped (the channel
    model subsumes them). -/
@[reducible]
def rowAt (v : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd FGL FGL) (r : ℕ)
    : BinaryAddRow FGL where
  a_0        := v.a_0 r
  a_1        := v.a_1 r
  b_0        := v.b_0 r
  b_1        := v.b_1 r
  c_chunks_0 := v.c_chunks_0 r
  c_chunks_1 := v.c_chunks_1 r
  c_chunks_2 := v.c_chunks_2 r
  c_chunks_3 := v.c_chunks_3 r
  cout_0     := v.cout_0 r
  cout_1     := v.cout_1 r

/-- The four BinaryAdd row constraints at row `r`, expressed against
    a `Valid_BinaryAdd`. -/
def constraints_at (v : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd FGL FGL) (r : ℕ) : Prop :=
  v.cout_0 r * (1 + -v.cout_0 r) = 0
  ∧ v.a_0 r + v.b_0 r
      + -(v.cout_0 r * 4294967296 + v.c_chunks_1 r * 65536 + v.c_chunks_0 r) = 0
  ∧ v.cout_1 r * (1 + -v.cout_1 r) = 0
  ∧ v.a_1 r + v.b_1 r + v.cout_0 r
      + -(v.cout_1 r * 4294967296 + v.c_chunks_3 r * 65536 + v.c_chunks_2 r) = 0

/-- **Bridge theorem.** Given a row of a `Valid_BinaryAdd` satisfying the
    four Clean Component constraints + the range/carry assumptions,
    the BinaryAdd Spec holds (i.e. `cPacked = (packed32 a + packed32 b) mod 2^64`).

    This routes the existing `Valid_BinaryAdd` consumer through the
    Clean Component's `soundness` lemma. The Compliance dispatch layer
    will discharge the `Assumptions` precondition via the FlatEnsemble's
    RangeBus channel-balance proof — completing the trust-retirement chain
    for `binary_add_columns_in_range`. -/
theorem spec_of_valid
    (v : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h_bool_0, h_carry_0, h_bool_1, h_carry_1⟩ := h_constraints
  exact soundness (rowAt v r) h_assumptions h_bool_0 h_carry_0 h_bool_1 h_carry_1

end ZiskFv.AirsClean.BinaryAdd
