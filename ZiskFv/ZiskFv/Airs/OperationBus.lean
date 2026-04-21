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
    `assumes_operation(...)` call at `vendor/zisk/state-machines/main/pil/main.pil:367-374`,
    specialized to the **non-32-bit (m32 = 0)** case. The full PIL has
    `a_hi := (1 - m32) * a_1` and similarly for `b_hi`, but Phase 1 only
    proves the 64-bit ADD path; the `m32`-gated 32-bit-op path is out of
    scope. The `m32 = 0` precondition is one of the explicit hypotheses of
    `Spec.Add.add_circuit_holds`. The `c` lanes are forwarded verbatim;
    `main_step`/`extended_arg` derive from precompile gating which we treat
    as zero (`is_precompiled = 0` for plain ADD). -/
@[simp]
def opBus_row_Main {C : Type → Type → Type} {F ExtF : Type}
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (m : ZiskFv.Airs.Main.Valid_Main C F ExtF) (row : ℕ) : OperationBusEntry F :=
  { multiplicity := m.is_external_op row
    op := m.op row
    a_lo := m.a_0 row
    a_hi := m.a_1 row
    b_lo := m.b_0 row
    b_hi := m.b_1 row
    c_lo := m.c_0 row
    c_hi := m.c_1 row
    flag := m.flag row
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

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
