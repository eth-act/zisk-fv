import ZiskFv.AirsClean.Main.Soundness
import ZiskFv.AirsClean.Main.Constraints
import ZiskFv.Airs.Main.Main
import ZiskFv.Channels.OperationBus
import ZiskFv.Airs.OperationBus.OperationBus

/-!
# `Valid_Main` ↔ `MainRow` compatibility bridge (long-lived)

This is the **central Bridge** — every opcode's `EquivCore/<Op>.lean`
proof takes `m : Valid_Main FGL FGL`. The Bridge preserves the
`Valid_Main` parameter shape through Phases C and D, so opcode-level
proofs compile unchanged until the final Phase D3 (drop circuit field).

The cross-row pc_handshake adjacency theorem is NOT in this Phase B
commit; it's tracked as Phase B.1 follow-up. Per-row Spec is what
the Component captures.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open ZiskFv.Channels.OperationBus


@[reducible]
def rowAt (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r : ℕ) : MainRow FGL where
  a_0 := m.a_0 r
  a_1 := m.a_1 r
  b_0 := m.b_0 r
  b_1 := m.b_1 r
  c_0 := m.c_0 r
  c_1 := m.c_1 r
  flag := m.flag r
  pc := m.pc r
  is_external_op := m.is_external_op r
  op := m.op r
  m32 := m.m32 r
  ind_width := m.ind_width r
  set_pc := m.set_pc r
  jmp_offset1 := m.jmp_offset1 r
  jmp_offset2 := m.jmp_offset2 r
  store_pc := m.store_pc r
  im_high_degree_2 := m.im_high_degree_2 r
  segment_l1 := m.segment_l1 r

/-- The 9 F-typed per-row Main constraints at row `r`, expressed
    against a `Valid_Main`. -/
def constraints_at (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r : ℕ) : Prop :=
  m.flag r * (1 - m.flag r) = 0
  ∧ m.is_external_op r * (1 - m.is_external_op r) = 0
  ∧ (1 - m.is_external_op r) * (1 - m.op r) * m.c_0 r = 0
  ∧ (1 - m.is_external_op r) * (1 - m.op r) * m.c_1 r = 0
  ∧ (1 - m.is_external_op r) * m.op r * (m.b_0 r - m.c_0 r) = 0
  ∧ (1 - m.is_external_op r) * m.op r * (m.b_1 r - m.c_1 r) = 0
  ∧ (1 - m.is_external_op r) * (1 - m.op r) * (1 - m.flag r) = 0
  ∧ (1 - m.is_external_op r) * m.op r * m.flag r = 0
  ∧ m.flag r * m.set_pc r = 0

theorem spec_of_valid
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt m r))
    (h_constraints : constraints_at m r) :
    Spec (rowAt m r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h_constraints
  exact soundness (rowAt m r) h_assumptions h1 h2 h3 h4 h5 h6 h7 h8 h9

/-- Main's operation-bus message without multiplicity, as a concrete row
    value. Clean carries multiplicity on the interaction, while the legacy
    `OperationBusEntry` carries it in the record. -/
@[reducible]
def opBusMessage (row : MainRow FGL) : OpBusMessage FGL :=
  { op := row.op
    a_lo := row.a_0
    a_hi := (1 - row.m32) * row.a_1
    b_lo := row.b_0
    b_hi := (1 - row.m32) * row.b_1
    c_lo := row.c_0
    c_hi := row.c_1
    flag := row.flag
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

theorem opBusMessage_toEntry_rowAt_eq_opBus_row
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r : ℕ) :
    OpBusMessage.toEntry (opBusMessage (rowAt m r)) (m.is_external_op r) =
      ZiskFv.Airs.OperationBus.opBus_row_Main m r := by
  rfl

theorem eval_opBusMessageExpr
    (env : Environment FGL) (row : Var MainRow FGL) :
    eval env (opBusMessageExpr row) = opBusMessage (eval env row) := by
  rw [OpBusMessage.mk.injEq]
  simp only [opBusMessageExpr, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field, Expression.eval]
  repeat constructor <;> try ring_nf <;> trivial

end ZiskFv.AirsClean.Main
