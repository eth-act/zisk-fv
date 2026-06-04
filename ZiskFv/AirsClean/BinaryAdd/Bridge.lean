import ZiskFv.AirsClean.BinaryAdd.Soundness
import ZiskFv.AirsClean.BinaryAdd.Circuit
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Binary.BinaryAddPackedCorrect
import ZiskFv.Channels.OperationBus

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
Soundness instead of the extraction harness's bespoke per-AIR proofs.

The old `binary_add_columns_in_range` axiom is retired by concrete
Clean/static lookup witnesses in the full ensemble path. This bridge
preserves the architectural connection from the named AIR wrapper to the
Clean component.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus


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

@[reducible]
def opBusMessage (row : BinaryAddRow FGL) : OpBusMessage FGL :=
  { op := 10
    a_lo := row.a_0
    a_hi := row.a_1
    b_lo := row.b_0
    b_hi := row.b_1
    c_lo := ((row.c_chunks_1 * 65536) + row.c_chunks_0)
    c_hi := ((row.c_chunks_3 * 65536) + row.c_chunks_2)
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

theorem opBusMessage_toEntry_rowAt_eq_opBus_row
    (v : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd FGL FGL) (r : ℕ) :
    OpBusMessage.toEntry (opBusMessage (rowAt v r)) 1 =
      ZiskFv.Airs.OperationBus.opBus_row_BinaryAdd v r := by
  rfl

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
    discharges the `Assumptions` precondition via concrete Clean/static
    lookup witnesses, completing the trust-retirement chain for
    `binary_add_columns_in_range`. -/
theorem spec_of_valid
    (v : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h_bool_0, h_carry_0, h_bool_1, h_carry_1⟩ := h_constraints
  exact soundness (rowAt v r) h_assumptions h_bool_0 h_carry_0 h_bool_1 h_carry_1

/-- **C0d re-root — Component-routed `Spec`.** From `core_every_row` (the
    hand-rolled four BinaryAdd row constraints) derive `BinaryAdd.Spec`
    **through the Clean Component**: `spec_via_component` routes through
    `circuit.soundness`, so any consumer of this lemma depends on `circuit`.

    `core_every_row`'s four conjuncts become the four constraints
    `spec_via_component` consumes (`1 - x` → `1 + -x` via `sub_eq_add_neg`;
    `(rowAt v row).field` ≡ `v.field row` since `rowAt` is `@[reducible]`).

    This is the routing half of the ADD re-root. The remaining half — an
    adapter from this `Spec` (`cPacked = (packed a + packed b) % 2^64`) to
    the `BitVec`-addition equation `h_rd_val_arith_add` consumes — hits a
    Lean kernel `deep recursion` in the `BitVec`/`Nat`-`%` arithmetic;
    isolating that adapter is the next C0d step. -/
theorem spec_of_core_every_row_via_component
    (v : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd FGL FGL) (row : ℕ)
    (h_chain : ZiskFv.Airs.BinaryAdd.core_every_row v row)
    (h_a_range : ZiskFv.Airs.BinaryAdd.a_chunks_in_range v row)
    (h_b_range : ZiskFv.Airs.BinaryAdd.b_chunks_in_range v row)
    (h_c_range : ZiskFv.Airs.BinaryAdd.c_chunks_in_range v row) :
    Spec (rowAt v row) := by
  obtain ⟨h_bool0, h_carry0, h_bool1, h_carry1⟩ := h_chain
  obtain ⟨h_a0, h_a1⟩ := h_a_range
  obtain ⟨h_b0, h_b1⟩ := h_b_range
  obtain ⟨h_c0, h_c1, h_c2, h_c3⟩ := h_c_range
  simp only [ZiskFv.Airs.BinaryAdd.boolean_cout_0, ZiskFv.Airs.BinaryAdd.carry_chain_0,
    ZiskFv.Airs.BinaryAdd.boolean_cout_1, ZiskFv.Airs.BinaryAdd.carry_chain_1,
    sub_eq_add_neg] at h_bool0 h_carry0 h_bool1 h_carry1
  exact spec_via_component (rowAt v row) h_a0 h_a1 h_b0 h_b1 h_c0 h_c1 h_c2 h_c3
    h_bool0 h_carry0 h_bool1 h_carry1

/-- **C0d re-root — the BitVec adapter.** Same statement as the hand-rolled
    `Airs.Binary.BinaryAddPackedCorrect.binary_add_chunks_eq_bv_add`, so it
    drops in at `h_rd_val_arith_add`'s call site — the swap that makes
    `equiv_ADD` (hence the global theorem) depend on `circuit`. The carry
    content comes from `spec_of_core_every_row_via_component` (→ the Clean
    Component); the `BitVec` arithmetic mimics the hand-rolled lemma's
    pure-`rw` shape (a `simp`-based variant kernel-`deep recursion`s). -/
theorem binary_add_chunks_eq_bv_add_via_component
    (v : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd FGL FGL) (row : ℕ)
    (h_chain : ZiskFv.Airs.BinaryAdd.core_every_row v row)
    (h_a_range : ZiskFv.Airs.BinaryAdd.a_chunks_in_range v row)
    (h_b_range : ZiskFv.Airs.BinaryAdd.b_chunks_in_range v row)
    (h_c_range : ZiskFv.Airs.BinaryAdd.c_chunks_in_range v row) :
    BitVec.ofNat 64 ((v.a_0 row).val + (v.a_1 row).val * 4294967296)
    + BitVec.ofNat 64 ((v.b_0 row).val + (v.b_1 row).val * 4294967296)
    = BitVec.ofNat 64
        ((v.c_chunks_0 row).val
          + (v.c_chunks_1 row).val * 65536
          + (v.c_chunks_2 row).val * 4294967296
          + (v.c_chunks_3 row).val * 281474976710656) := by
  have h_spec := spec_of_core_every_row_via_component v row h_chain
    h_a_range h_b_range h_c_range
  simp only [Spec, cPacked, packed32, Nat.reducePow] at h_spec
  obtain ⟨h_a0, h_a1⟩ := h_a_range
  obtain ⟨h_b0, h_b1⟩ := h_b_range
  obtain ⟨h_c0, h_c1, h_c2, h_c3⟩ := h_c_range
  have h_av : (v.a_0 row).val + (v.a_1 row).val * 4294967296 < 18446744073709551616 := by omega
  have h_bv : (v.b_0 row).val + (v.b_1 row).val * 4294967296 < 18446744073709551616 := by omega
  have h_cv : (v.c_chunks_0 row).val + (v.c_chunks_1 row).val * 65536
      + (v.c_chunks_2 row).val * 4294967296
      + (v.c_chunks_3 row).val * 281474976710656 < 18446744073709551616 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h_av, Nat.mod_eq_of_lt h_bv, Nat.mod_eq_of_lt h_cv, ← h_spec]
  ring

/-- Project a single Clean `BinaryAddRow` back into a one-row
    `Valid_BinaryAdd` validator (constant function), pinning all rows
    to the given row's column values. The stage-2 accumulator columns
    are zeroed; consumers do not depend on them. Mirrors
    `AirsClean.Binary.validOfRow`. -/
@[reducible]
def validOfRow (row : BinaryAddRow FGL) :
    ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd FGL FGL where
  a_0 := fun _ => row.a_0
  a_1 := fun _ => row.a_1
  b_0 := fun _ => row.b_0
  b_1 := fun _ => row.b_1
  c_chunks_0 := fun _ => row.c_chunks_0
  c_chunks_1 := fun _ => row.c_chunks_1
  c_chunks_2 := fun _ => row.c_chunks_2
  c_chunks_3 := fun _ => row.c_chunks_3
  cout_0 := fun _ => row.cout_0
  cout_1 := fun _ => row.cout_1
  gsum := fun _ => 0
  im_0 := fun _ => 0
  im_1 := fun _ => 0

theorem rowAt_validOfRow_zero (row : BinaryAddRow FGL) :
    rowAt (validOfRow row) 0 = row := by
  cases row
  rfl

theorem eval_opBusMessageExpr
    (env : Environment FGL) (row : Var BinaryAddRow FGL) :
    eval env (opBusMessageExpr row) = opBusMessage (eval env row) := by
  rw [OpBusMessage.mk.injEq]
  simp only [opBusMessageExpr, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field, Expression.eval]
  repeat constructor

theorem component_eval_opBusMessageExpr
    (env : Environment FGL) :
    eval env (opBusMessageExpr component.rowInputVar) =
      opBusMessage (component.rowInput env) := by
  rw [eval_opBusMessageExpr]
  exact congrArg opBusMessage
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset component.Input 0 env))

end ZiskFv.AirsClean.BinaryAdd
