import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryExtension

/-!
ZisK operation-bus schema and Main↔BinaryAdd projection.

The operation bus carries 11 fields per row, defined in `zisk/pil/operations.pil:144`:

  `[op, a_lo, a_hi, b_lo, b_hi, c_lo, c_hi, flag, main_step, extended_arg, extra_args_0]`

Identifier `OPERATION_BUS_ID = 5000` (`zisk/pil/opids.pil:2`). Mirrors
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
    `zisk/state-machines/main/pil/main.pil:367-374`. PIL-faithful:
    the `a_hi` and `b_hi` lanes carry the `(1 - m32) *` factor from PIL so
    that 32-bit opcodes (`m32 = 1`) zero their high halves on the bus,
    while 64-bit opcodes (`m32 = 0`) pass them through. Callers supply the
    `m32` value via a constraint hypothesis (see
    `Circuit.Add.main_row_in_add_mode`, which pins `m32 = 0` for ADD);
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

/-- `(1 - 1) * x = 0` — the mirror of `one_sub_zero_mul` for the
    `m32 = 1` path. Collapses the `(1 - m32) * a_hi` / `(1 - m32) * b_hi`
    factors on the bus entry for 32-bit word variants. Fires after
    `rw [h_m32]` rewrites `m.m32 row = 1` into the `OperationBusEntry`;
    without this lemma `simp` leaves `(1 - 1) * x` unreduced under the
    named-column accessors. -/
@[simp]
lemma one_sub_one_mul {F : Type} [Field F] (x : F) :
    (1 - (1 : F)) * x = 0 := by ring

/-- Specialization of `one_sub_one_mul` that takes the `m32 = 1`
    hypothesis explicitly. Useful when the goal has
    `(1 - m.m32 row) * ...` and we have `h : m.m32 row = 1` in scope:
    `rw [h]` then `simp` (or `one_sub_one_mul`) closes the factor to 0. -/
lemma one_sub_m32_mul_of_eq_one {F : Type} [Field F]
    {m32 : F} (h : m32 = 1) (x : F) : (1 - m32) * x = 0 := by
  subst h; ring

/-- BinaryAdd's operation-bus emission for a given row. Mirrors the
    `proves_operation(op: OP_ADD, a:, b:, c:)` call at
    `zisk/state-machines/binary/pil/binary_add.pil:25`. Multiplicity
    is `1` (the implicit `mul:1` default). `c` is reassembled from
    `c_chunks` per the per-lane recombination
    `c[i] := c_chunks[2i+1] * 2^16 + c_chunks[2i]`. -/
@[simp]
def opBus_row_BinaryAdd {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (b : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd C F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := 1
    -- Opcode literal `0x0A` per `zisk/pil/opids.pil`. The bus entry
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

/-- Binary's operation-bus emission for a given row. Mirrors the
    `proves_operation(op: b_op + 0x10 * mode32, a:, b:, c:, flag:cout)` call
    at `zisk/state-machines/binary/pil/binary.pil:156`. The `a`/`b`/`c`
    chunks are reassembled from per-byte witnesses via the standard
    base-256 weights (4 bytes per 32-bit chunk). The `c_lo` lane carries
    an additional `+ carry_7` summand from the `c[0] += cout` rebase
    line at `binary.pil:154`. Multiplicity is `1` (the implicit
    `mul:1` default for `proves_operation`).

    Cross-checked against the extracted spec
    `bus_emission_Binary_0` at
    `build/extraction/Extraction/Buses.lean` (gsum debug #1178). -/
@[simp]
def opBus_row_Binary {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (b : ZiskFv.Airs.Binary.Valid_Binary C F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := 1
    op := b.b_op row + 16 * b.mode32 row
    a_lo := b.free_in_a_0 row + 256 * b.free_in_a_1 row
            + 65536 * b.free_in_a_2 row + 16777216 * b.free_in_a_3 row
    a_hi := b.free_in_a_4 row + 256 * b.free_in_a_5 row
            + 65536 * b.free_in_a_6 row + 16777216 * b.free_in_a_7 row
    b_lo := b.free_in_b_0 row + 256 * b.free_in_b_1 row
            + 65536 * b.free_in_b_2 row + 16777216 * b.free_in_b_3 row
    b_hi := b.free_in_b_4 row + 256 * b.free_in_b_5 row
            + 65536 * b.free_in_b_6 row + 16777216 * b.free_in_b_7 row
    c_lo := b.free_in_c_0 row + 256 * b.free_in_c_1 row
            + 65536 * b.free_in_c_2 row + 16777216 * b.free_in_c_3 row
            + b.carry_7 row
    c_hi := b.free_in_c_4 row + 256 * b.free_in_c_5 row
            + 65536 * b.free_in_c_6 row + 16777216 * b.free_in_c_7 row
    flag := b.carry_7 row
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- BinaryExtension's operation-bus emission for a given row. Mirrors the
    `proves_operation` call at
    `zisk/state-machines/binary/pil/binary_extension.pil:118`. The `op_is_shift`
    selector chooses between two routings:
    * shift family (`op_is_shift = 1`): `a := free_in_a` (assembled from per-byte
      columns), `b_lo := free_in_b + 256 * b_aux_0`, `b_hi := b_aux_1`;
    * sign-extend family (`op_is_shift = 0`): `a := b_aux`, `b := free_in_a`.
    The two `c` lanes are sums of the per-byte `free_in_c[*][0|1]` columns;
    in this AIR the `[j][0]` half is flattened to `free_in_c_(2j)` and the
    `[j][1]` half to `free_in_c_(2j+1)`. Multiplicity is `1`.

    Cross-checked against the extracted spec
    `bus_emission_BinaryExtension_0` at
    `build/extraction/Extraction/Buses.lean` (gsum debug #1220). -/
@[simp]
def opBus_row_BinaryExtension {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (e : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C F ExtF)
    (row : ℕ) : OperationBusEntry F :=
  let a0 := e.free_in_a_0 row + 256 * e.free_in_a_1 row
            + 65536 * e.free_in_a_2 row + 16777216 * e.free_in_a_3 row
  let a1 := e.free_in_a_4 row + 256 * e.free_in_a_5 row
            + 65536 * e.free_in_a_6 row + 16777216 * e.free_in_a_7 row
  { multiplicity := 1
    op := e.op row
    a_lo := e.op_is_shift row * (a0 - e.b_0 row) + e.b_0 row
    a_hi := e.op_is_shift row * (a1 - e.b_1 row) + e.b_1 row
    b_lo := e.op_is_shift row * (e.free_in_b row + 256 * e.b_0 row - a0) + a0
    b_hi := e.op_is_shift row * (e.b_1 row - a1) + a1
    c_lo := e.free_in_c_0 row + e.free_in_c_2 row + e.free_in_c_4 row
            + e.free_in_c_6 row + e.free_in_c_8 row + e.free_in_c_10 row
            + e.free_in_c_12 row + e.free_in_c_14 row
    c_hi := e.free_in_c_1 row + e.free_in_c_3 row + e.free_in_c_5 row
            + e.free_in_c_7 row + e.free_in_c_9 row + e.free_in_c_11 row
            + e.free_in_c_13 row + e.free_in_c_15 row
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- Two `OperationBusEntry`s match when every field agrees. The proof of
    `Circuit.Add` reduces to: Main's bus row at `r_main` matches BinaryAdd's
    bus row at `r_binary`. -/
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
