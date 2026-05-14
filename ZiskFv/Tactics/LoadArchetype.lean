import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Circuit.LoadD

/-!
**Load archetype macros / generic lemmas.**

The seven RV64IM integer loads (LD/LW/LWU/LH/LHU/LB/LBU) share a single
ZisK transpilation shape: one microinstruction with `src_a = reg(rs1)`,
`src_b = ind(imm)`, `store = reg(rd)`, `j(4, 4)`, and `is_external_op`
determined by the `op` kind. Two sub-families split on sign-extension:

* **Zero-extension loads (LD, LWU, LHU, LBU)** transpile to
  `op = "copyb"` (`OP_COPYB = 1`, `OpType::Internal`). The Main row's
  constraint 9 forces `c = b` directly — **no operation-bus hop**.
  This file's archetype covers them.

* **Sign-extension loads (LW, LH, LB)** transpile to
  `op ∈ {"signextend_w", "signextend_h", "signextend_b"}` with
  `OpType::BinaryE` — i.e. external op, operation-bus hop to the
  BinaryExtension SM. See `SignExtendLoadArchetype.lean`.

The archetype is parametric over the memory-operand width (8/4/2/1
bytes); LWU/LHU/LBU close via instantiation + a width-specific
zeroing-of-high-bytes assumption on the memory-bus entry.

## Usage pattern

```lean
-- LWU case (width = 4, op = OP_COPYB = 1):
theorem equiv_LWU (...) := by
  have := load_archetype_c_packed m r next_pc entry h_circuit
  -- apply `memory_entry_toField` lemmas specialized to width = 4
  ...
```
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
    version of `Circuit.LoadD.load_d_circuit_holds`. Only for the
    `OP_COPYB` sub-family (`is_external_op = 0`); sign-extension loads
    need a different subset (constraint 10 plus an operation-bus hop).

    Exposes the width at the top level so callers can specialize
    the per-byte-lane memory-entry match (LWU zeros x4..x7, LHU
    zeros x2..x7, LBU zeros x1..x7). -/
@[simp]
def load_archetype_copyb_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL) : Prop :=
  load_subset_holds m r_main next_pc
  ∧ main_row_in_load_mode m r_main (1 : FGL) (0 : FGL)
  ∧ memory_load_lanes_match m r_main entry

/-- **Archetype theorem (zero-extension loads, c-packed).**
    Same shape as `Circuit.LoadD.load_d_compositional` but expressed in
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

end ZiskFv.Tactics.LoadArchetype
