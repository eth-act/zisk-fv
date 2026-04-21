import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd

/-!
ZisK operation-bus schema and Main↔BinaryAdd projection.

The operation bus carries 11 fields per row, defined in `vendor/zisk/pil/operations.pil:144`:

  `[op, a_lo, a_hi, b_lo, b_hi, c_lo, c_hi, flag, main_step, extended_arg, extra_args_0]`

Identifier `OPERATION_BUS_ID = 5000` (`vendor/zisk/pil/opids.pil:2`). Mirrors
the `ExecutionBusEntry`/`MemoryBusEntry` shape in
`openvm-fv/OpenvmFv/Fundamentals/Interaction.lean:63-150`.
-/

namespace ZiskFv.Airs.OperationBus

open Goldilocks

/-- One row's operation-bus entry. The Main AIR pushes one entry per
    `is_external_op = 1` row; the appropriate secondary state machine pops
    one entry under matching multiplicity. -/
structure OperationBusEntry (F : Type) [Field F] where
  /-- Permutation accumulator multiplicity. Concretely `is_external_op` for
      Main and the BinaryAdd-side `mul` selector. Sign distinguishes
      assume-side from prove-side. -/
  multiplicity : F
  op : F
  a_lo : F
  a_hi : F
  b_lo : F
  b_hi : F
  c_lo : F
  c_hi : F
  flag : F
  main_step : F
  extended_arg : F
  extra_args_0 : F
  deriving BEq, DecidableEq, Inhabited

/-- Main AIR's operation-bus emission for a given row. Mirrors the
    `assumes_operation(...)` call at
    `vendor/zisk/state-machines/main/pil/main.pil:367-374`. PIL-faithful:
    the `a_hi` and `b_hi` lanes carry the `(1 - m32) *` factor from PIL so
    that 32-bit opcodes (`m32 = 1`) zero their high halves on the bus,
    while 64-bit opcodes (`m32 = 0`) pass them through. Callers supply the
    `m32` value via a constraint hypothesis (see
    `Spec.Add.main_row_in_add_mode`, which pins `m32 = 0` for ADD);
    downstream `simp` closes `(1 - 0) * x = x` via `one_sub_zero_mul` /
    `Goldilocks.one_sub_m32_mul_of_eq_zero` below. The `c` lanes are
    forwarded verbatim; `main_step`/`extended_arg` derive from precompile
    gating which we treat as zero (`is_precompiled = 0` for plain ADD). -/
@[simp]
def opBus_row_Main {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (m : ZiskFv.Airs.Main.Valid_Main C F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := m.is_external_op row
    op := m.op row
    a_lo := m.a_0 row
    a_hi := (1 - m.m32 row) * m.a_1 row
    b_lo := m.b_0 row
    b_hi := (1 - m.m32 row) * m.b_1 row
    c_lo := m.c_0 row
    c_hi := m.c_1 row
    flag := m.flag row
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- `(1 - 0) * x = x` — the trivial simp lemma that lets the bus
    `a_hi`/`b_hi` factor collapse once a constraint hypothesis of the form
    `m.m32 row = 0` has been rewritten in. Needed because generic `simp`
    and `ring_nf` do not themselves fire `(1 - 0) * x ↦ x` under the
    `Valid_Main` column accessors in the `OperationBusEntry` structure —
    the `simp only` pass that unfolds `opBus_row_Main` needs this lemma
    explicit, not merely `sub_zero`/`one_mul` in some order. -/
@[simp]
lemma one_sub_zero_mul {F : Type} [Field F] (x : F) :
    (1 - (0 : F)) * x = x := by ring

/-- Specialization of `one_sub_zero_mul` that takes the `m32 = 0` hypothesis
    explicitly. Useful when the goal has `(1 - m.m32 row) * ...` and we
    have `h : m.m32 row = 0` in scope: `rw [h]` followed by `simp`
    (or `one_sub_zero_mul`) closes it. -/
lemma one_sub_m32_mul_of_eq_zero {F : Type} [Field F]
    {m32 : F} (h : m32 = 0) (x : F) : (1 - m32) * x = x := by
  subst h; ring

/-- BinaryAdd's operation-bus emission for a given row. Mirrors the
    `proves_operation(op: OP_ADD, a:, b:, c:)` call at
    `vendor/zisk/state-machines/binary/pil/binary_add.pil:25`. Multiplicity
    is `1` (the implicit `mul:1` default). `c` is reassembled from
    `c_chunks` per the per-lane recombination
    `c[i] := c_chunks[2i+1] * 2^16 + c_chunks[2i]`. -/
@[simp]
def opBus_row_BinaryAdd {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (b : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd C F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := 1
    -- Opcode literal `0x0A` per `vendor/zisk/pil/opids.pil`. The bus entry
    -- is parametric in F, so we use the natural literal directly rather
    -- than `ZiskFv.Trusted.OP_ADD` (which is fixed to `FGL`).
    op := 10
    a_lo := b.a_0 row
    a_hi := b.a_1 row
    b_lo := b.b_0 row
    b_hi := b.b_1 row
    c_lo := b.c_chunks_1 row * 65536 + b.c_chunks_0 row
    c_hi := b.c_chunks_3 row * 65536 + b.c_chunks_2 row
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- Two `OperationBusEntry`s match when every field agrees. The proof of
    Spec.Add reduces to: Main's bus row at `r_main` matches BinaryAdd's bus
    row at `r_binary`. -/
@[simp]
def matches_entry {F : Type} [Field F]
    (a b : OperationBusEntry F) : Prop :=
  a.multiplicity = b.multiplicity
  ∧ a.op = b.op
  ∧ a.a_lo = b.a_lo
  ∧ a.a_hi = b.a_hi
  ∧ a.b_lo = b.b_lo
  ∧ a.b_hi = b.b_hi
  ∧ a.c_lo = b.c_lo
  ∧ a.c_hi = b.c_hi
  ∧ a.flag = b.flag
  ∧ a.main_step = b.main_step
  ∧ a.extended_arg = b.extended_arg
  ∧ a.extra_args_0 = b.extra_args_0

end ZiskFv.Airs.OperationBus
