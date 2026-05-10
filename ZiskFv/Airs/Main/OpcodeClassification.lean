import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main

/-!
# Main AIR — opcode-set classification

The 63 canonical `equiv_<OP>` theorems each pin `m.op r_main` to a
specific `OP_<X>` literal. The global compliance theorem
(`zisk_riscv_compliant_program_bus`, Step 4 of
`/home/cody/.claude/plans/plan-to-completely-resolve-wild-lynx.md`)
dispatches by case on which literal is in play. This file provides:

1. `main_op_in_RV64IM_scope` — a `Prop`-valued predicate enumerating
   the 35 distinct Zisk `OP_<X>` literals that the RV64IM equiv
   proofs use (some Zisk OPs cover multiple RV64IM opcodes, e.g.
   `OP_ADD` is shared by ADD and ADDI — the immediate-vs-register
   discrimination lives in Main's `b_src_imm` selector, not the `op`
   column).

2. `main_op_in_scope_of_universal` — a trivial specialization helper:
   given the universal "this trace's `op` selectors all lie in the
   RV64IM scope" precondition (which the global theorem accepts as a
   verification-boundary scope assumption), produce the per-row
   classification.

**No new axiom is added.** The opcode-set fact is a *scope assumption*
about the program being verified — the same flavor as
`docs/fv/trusted-base.md`'s "Out of scope: Zicclsm, precompiles
(Keccak / SHA256 / big-int / DMA / etc.), ECALL/EBREAK, ZisK's custom
internal ops." Callers (the global theorem) accept the scope
assumption explicitly and pass it through.

The contents of this file enumerate, not posit, the in-scope
opcodes. The trust ledger is unchanged.
-/

namespace ZiskFv.Airs.Main

open Goldilocks
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **RV64IM opcode-set classifier.** Asserts that `m.op r_main` is one
    of the 35 `OP_<X>` literals defined in `Fundamentals/Transpiler.lean`
    that Zisk uses to encode the 63 RV64IM opcodes (some Zisk OPs are
    shared across RTYPE / ITYPE variants).

    Auxiliary OPs (`OP_FLAG = 0`, `OP_COPYB = 1`,
    `OP_SIGNEXTEND_{B,H,W}`) are included because Main's `op` selector
    can emit them under `is_external_op = 1` for sub-doubleword load
    sign-extension routing. They do not correspond to a separate
    canonical `equiv_<OP>`; the dispatch in
    `zisk_riscv_compliant_program_bus` handles them via the relevant
    LB / LH / LW chains.

    Out-of-scope opcodes (precompiles like Keccak / SHA256 / big-int,
    Zicclsm, ECALL / EBREAK) are deliberately excluded — that's what
    "RV64IM scope" means. -/
@[simp]
def main_op_in_RV64IM_scope (m : Valid_Main C FGL FGL) (r : ℕ) : Prop :=
    m.op r = OP_FLAG
  ∨ m.op r = OP_COPYB
  ∨ m.op r = OP_LTU
  ∨ m.op r = OP_LT
  ∨ m.op r = OP_EQ
  ∨ m.op r = OP_ADD
  ∨ m.op r = OP_SUB
  ∨ m.op r = OP_AND
  ∨ m.op r = OP_OR
  ∨ m.op r = OP_XOR
  ∨ m.op r = OP_ADD_W
  ∨ m.op r = OP_SUB_W
  ∨ m.op r = OP_SLL
  ∨ m.op r = OP_SRL
  ∨ m.op r = OP_SRA
  ∨ m.op r = OP_SLL_W
  ∨ m.op r = OP_SRL_W
  ∨ m.op r = OP_SRA_W
  ∨ m.op r = OP_SIGNEXTEND_B
  ∨ m.op r = OP_SIGNEXTEND_H
  ∨ m.op r = OP_SIGNEXTEND_W
  ∨ m.op r = OP_MULU
  ∨ m.op r = OP_MULUH
  ∨ m.op r = OP_MULSUH
  ∨ m.op r = OP_MUL
  ∨ m.op r = OP_MULH
  ∨ m.op r = OP_MUL_W
  ∨ m.op r = OP_DIVU
  ∨ m.op r = OP_REMU
  ∨ m.op r = OP_DIV
  ∨ m.op r = OP_REM
  ∨ m.op r = OP_DIVU_W
  ∨ m.op r = OP_REMU_W
  ∨ m.op r = OP_DIV_W
  ∨ m.op r = OP_REM_W

/-- **Specialization helper.** Given the universal-over-rows scope
    assumption that every active row's `op` lies in the RV64IM set
    (a precondition supplied by the caller of the global theorem),
    extract the per-row classification.

    The proof is a one-liner — no new trust is introduced; the trust
    *is* the universal hypothesis itself. -/
theorem main_op_in_RV64IM_scope_of_universal
    (m : Valid_Main C FGL FGL)
    (h_scope : ∀ r, m.is_external_op r = 1 → main_op_in_RV64IM_scope m r)
    (r : ℕ) (h_active : m.is_external_op r = 1) :
    main_op_in_RV64IM_scope m r :=
  h_scope r h_active

end ZiskFv.Airs.Main
