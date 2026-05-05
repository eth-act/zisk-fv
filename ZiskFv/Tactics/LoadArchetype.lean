import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Circuit.LoadD

/-!
**Load archetype macros / generic lemmas** (Phase 2 A3-M).

The seven RV64IM integer loads (LD/LW/LWU/LH/LHU/LB/LBU) share a single
ZisK transpilation shape: one microinstruction with `src_a = reg(rs1)`,
`src_b = ind(imm)`, `store = reg(rd)`, `j(4, 4)`, and `is_external_op`
determined by the `op` kind. Two sub-families split on sign-extension:

* **Zero-extension loads (LD, LWU, LHU, LBU)** transpile to
  `op = "copyb"` (`OP_COPYB = 1`, `OpType::Internal`). The Main row's
  constraint 9 forces `c = b` directly — **no operation-bus hop**.
  A3 closes this family; archetype sub-name: **"load / copyb"**.

* **Sign-extension loads (LW, LH, LB)** transpile to
  `op ∈ {"signextend_w", "signextend_h", "signextend_b"}` with
  `OpType::BinaryE` — i.e. external op, operation-bus hop to the
  BinaryExtension SM. Not closed by A3; Phase 3 sweep work using
  the A6 (SLLW) infrastructure.

This module packages the load-family circuit-side archetype lemmas —
parametric over the memory-operand width (8/4/2/1 bytes) — so the
A3 (LD) proof generalizes by instantiation to LWU/LHU/LBU, and the
sign-extension loads fall out as a simple composition with the
BinaryExtension-SM archetype (Phase 3).

## Usage pattern (Phase 3 fan-out)

```lean
-- LWU case (width = 4, op = OP_COPYB = 1):
theorem equiv_LWU_metaplan (...) := by
  have := load_archetype_c_packed m r next_pc entry h_circuit
  -- apply `memory_entry_toField` lemmas specialized to width = 4
  ...
```

Phase 3 will add per-width bridging lemmas (`memory_entry_width_*`),
but A3 only exposes the width-independent archetype (packed 64-bit
c-cell = packed bus-entry value).

## Minimalism note

Phase 2 A3 closes LD with `Spec.LoadD.load_d_compositional` directly
(no macro call). The macro here is the *delivery* of the archetype —
what Phase 3's LWU/LHU/LBU proofs consume. Keeping LD's proof concrete
while providing the macro at the same surface lets reviewers diff the
two and confirm the macro generalizes correctly.

## A3 → A4 (SD) bridge note

**Phase 3 preview.** A4 (SD) is the near-mirror of A3: same
memory-bus infrastructure, but with the multiplicity / `as` /
direction flipped for writes. The predicates in `Airs/MemoryBus.lean`
(`matches_memory_entry`, `memory_entry_toField`) are already
write-side-symmetric — the only SD-specific additions will be a
`store_subset_holds` (constraint 10 + the store-side `mem_op`) and a
`memory_store_lanes_match` predicate asserting `value = b` rather than
`value = c`. Most of A3's scaffolding (Transpiler extensions for
`store_reg`/`store_ind`, the `Valid_Main` column accessors, the
`memory_entry_toField` packing) carries over verbatim.
-/

namespace ZiskFv.Tactics.LoadArchetype

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Circuit.LoadD
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Archetype mode predicate.** A Main row is in load-execution mode
    for a given Zisk opcode literal when `is_external_op`, `op`, `m32`,
    `set_pc`, and `store_pc` match the transpile-axiom witnesses.
    Parametric over the opcode literal; for zero-extension loads the
    literal is `OP_COPYB = 1` + `is_external_op = 0`. -/
@[simp]
def main_row_in_load_mode
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (opcode_lit : FGL) (is_ext : FGL) : Prop :=
  m.is_external_op r_main = is_ext
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- **Archetype circuit-holds (zero-extension loads).** Parametric
    version of `Spec.LoadD.load_d_circuit_holds`. Only for the
    `OP_COPYB` sub-family (`is_external_op = 0`); sign-extension loads
    need a different subset (constraint 10 plus an operation-bus hop).

    Exposes the width at the top level so Phase 3 can specialize the
    per-byte-lane memory-entry match (LWU zeros x4..x7, LHU zeros
    x2..x7, LBU zeros x1..x7). -/
@[simp]
def load_archetype_copyb_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL) : Prop :=
  load_subset_holds m r_main next_pc
  ∧ main_row_in_load_mode m r_main (1 : FGL) (0 : FGL)
  ∧ memory_load_lanes_match m r_main entry

/-- **Archetype theorem (zero-extension loads, c-packed).**
    Same shape as `Spec.LoadD.load_d_compositional` but expressed in
    the parametric `load_archetype_copyb_circuit_holds` form. LWU /
    LHU / LBU close via instantiation + a width-specific
    zeroing-of-high-bytes assumption on the memory-bus entry. -/
theorem load_archetype_copyb_c_packed
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_archetype_copyb_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_toField entry := by
  obtain ⟨h_subset, h_mode, h_mem⟩ := h
  obtain ⟨h_ext, h_op, h_m32, h_setpc⟩ := h_mode
  apply load_d_compositional m r_main next_pc entry
  refine ⟨h_subset, ?_, h_mem⟩
  exact ⟨h_ext, h_op, h_m32, h_setpc⟩

/-- **Archetype next-PC (zero-extension loads).** Same shape as
    `Spec.LoadD.load_d_next_pc_concrete`: when `jmp_offset1 =
    jmp_offset2 = 4`, the next-pc is `pc + 4`. Holds uniformly for
    LD/LWU/LHU/LBU since they all use `j(4, 4)` in the Zisk
    transpiler. -/
theorem load_archetype_copyb_next_pc
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h : load_archetype_copyb_circuit_holds m r_main next_pc entry)
    (h_jmp1 : m.jmp_offset1 r_main = 4)
    (h_jmp2 : m.jmp_offset2 r_main = 4) :
    next_pc = m.pc r_main + 4 := by
  obtain ⟨h_subset, h_mode, h_mem⟩ := h
  obtain ⟨h_ext, h_op, h_m32, h_setpc⟩ := h_mode
  apply load_d_next_pc_concrete m r_main next_pc entry _ h_jmp1 h_jmp2
  exact ⟨h_subset, ⟨h_ext, h_op, h_m32, h_setpc⟩, h_mem⟩

/-- **Tactic macro `load_archetype_proof`.** Convenience wrapper for
    proving the packed-c formula from a hypothesis
    `h_circuit : load_archetype_copyb_circuit_holds m r_main next_pc entry`
    in scope.

    **Expected goal shape:**
    `main_c_packed m r_main = memory_entry_toField entry`.

    **Required hypotheses (must be named literally in the caller):**
    * `m : Valid_Main C FGL FGL`,
    * `r_main : ℕ`, `next_pc : FGL`, `entry : MemoryBusEntry FGL`,
    * `h_circuit : load_archetype_copyb_circuit_holds m r_main next_pc entry`. -/
macro "load_archetype_proof" : tactic => `(tactic| (
  exact load_archetype_copyb_c_packed m r_main next_pc entry h_circuit
))

end ZiskFv.Tactics.LoadArchetype
