import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus

/-!
Compositional JAL (jump-and-link) spec: given the named jump-subset Main
constraints and the mode witnesses supplied by `transpile_JAL`
(`op = OP_FLAG = 0`, `is_external_op = 0`, `m32 = 0`, `set_pc = 0`,
`store_pc = 1`), the *next-row* `pc` cell equals `pc + jmp_offset1`
(= `pc + imm`) and the store-value lane zero equals `pc + jmp_offset2`
(= `pc + 4` — the return address written to rd).

Unlike BEQ, JAL is **not** an external op (`is_external_op = 0`), so
constraints 8/15 (internal-op=0 zeroes c) and 17 (internal-op=0 sets
flag) are non-trivial and together force `flag = 1` and `c = 0`. No
operation-bus hop is emitted.

This is the A2 archetype spec. JALR will differ by `set_pc = 1` and
`c[0]` (from rs1 via the operation bus) driving next-pc.
-/

namespace ZiskFv.Spec.Jal

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in JAL-execution mode: internal op with
    opcode literal 0 (OP_FLAG), full 64-bit width (m32 = 0), `set_pc = 0`
    (PC advance comes from `flag = 1` + `jmp_offset1`, not `c[0]`), and
    `store_pc = 1` (rd receives `pc + jmp_offset2 = pc + 4`). -/
@[simp]
def main_row_in_jal_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 0
  ∧ m.op r_main = (0 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0
  ∧ m.store_pc r_main = 1

/-- Hypotheses needed by `jal_compositional`. All four circuit-side
    obligations are constraint witnesses plus the transpile-axiom's
    mode witnesses — no external SM delegation needed (JAL is internal
    op 0). -/
@[simp]
def jal_circuit_holds
    (m : Valid_Main C FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  jump_subset_holds m r_main next_pc
  ∧ main_row_in_jal_mode m r_main

/-- **Compositional JAL (next-pc) theorem.** Given the jump-subset Main
    constraints (booleans + `flag*set_pc = 0` disjointness + constraints
    8/15/17 + PC handshake) and the mode witnesses (`is_external_op = 0`,
    `op = 0`, `m32 = 0`, `set_pc = 0`, `store_pc = 1`), the next-row `pc`
    equals `pc + jmp_offset1`.

    Composed with `transpile_JAL` (which pins `jmp_offset1 = imm`), this
    says JAL advances PC to `pc + imm`, consistent with the RISC-V
    unconditional-jump semantics. -/
theorem jal_pc_advance
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jal_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, _h_c0_zero, _h_c1_zero,
          h17, h_handshake⟩ := h_subset
  obtain ⟨h_ext, h_op, _h_m32, h_set_pc, _h_store_pc⟩ := h_mode
  have h_flag : m.flag r_main = 1 :=
    flag_eq_one_of_internal_op_zero m r_main h_ext h_op h17
  exact pc_handshake_jump m r_main next_pc h_set_pc h_flag h_handshake

/-- **Return address.** The `store_value[0] = store_pc*(pc + jmp_offset2
    - c_0) + c_0` expression (`main.pil:311`) under JAL's mode
    witnesses (`store_pc = 1`, and `c_0 = 0` from constraint 8 with
    `is_external_op = 0, op = 0`) evaluates to `pc + jmp_offset2`.
    With `transpile_JAL` pinning `jmp_offset2 = 4`, this is the
    `pc + 4` return-address value written to rd. -/
theorem jal_store_value
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jal_circuit_holds m r_main next_pc) :
    m.store_pc r_main * (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
        + m.c_0 r_main
      = m.pc r_main + m.jmp_offset2 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, h8, _h15, _h17, _h_handshake⟩ := h_subset
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  have h_c0 : m.c_0 r_main = 0 :=
    c_0_eq_zero_of_internal_op_zero m r_main h_ext h_op h8
  rw [h_c0, h_store_pc]
  ring

end ZiskFv.Spec.Jal
