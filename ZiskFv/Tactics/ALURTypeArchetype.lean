import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus

/-!
**ALU RTYPE archetype macros / generic lemmas.**

The six ALU-RTYPE opcodes (SUB, AND, OR, XOR, SLT, SLTU) share a
single ZisK microinstruction shape under `create_register_op`:

* `op` = one of `OP_SUB`/`OP_AND`/`OP_OR`/`OP_XOR`/`OP_LT`/`OP_LTU`
  (Binary-SM externally-dispatched opcodes, `zisk_ops.rs`);
* `is_external_op = 1`, type `Binary` — dispatched to the Binary SM
  via the operation bus;
* `m32 = 0` — these are all 64-bit variants;
* `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`;
* `a`/`b` lanes carry `xreg(rs1)` / `xreg(rs2)`.

Unlike ADD (which has an extracted `Valid_BinaryAdd` AIR), the other
Binary-SM AIRs (`BinarySub`, `BinaryLogic`, etc.) are **not extracted**.
We close these six opcodes by parameterizing the archetype over an
abstract `OperationBusEntry FGL` — exactly the pattern
`Tactics/ShiftArchetype.lean` uses for SLLW / SRLW / SRAW. The
secondary SM's internal correctness (that the bus entry's `c_lo`,
`c_hi` correctly encode the opcode's semantics on the input `a`, `b`
lanes) is a separate audit obligation.

## Parameterization

* `opcode_lit : FGL` — the Zisk opcode literal for the RTYPE variant.
  `OP_SUB = 11`, `OP_AND = 14`, `OP_OR = 15`, `OP_XOR = 16`,
  `OP_LT = 7` (reused from BLT), `OP_LTU = 6` (reused from BLTU).

## Usage pattern

```
lemma sub_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : alu_rtype_archetype_circuit_holds m r_main bus_entry OP_SUB) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_rtype_archetype_c_bus_match m r_main bus_entry OP_SUB h
```

## Minimalism note

ADD's `Valid_BinaryAdd`-dependent carry-chain identity does **not**
generalize — SUB/AND/OR/XOR/SLT/SLTU have no analogous extracted AIR.
We keep `Spec/Add.lean` untouched and define a narrower archetype here
that stops at the bus-match identity (Main's `c` lanes equal the bus
entry's `c` lanes).
-/

namespace ZiskFv.Tactics.ALURTypeArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Archetype mode predicate (Main side).** A Main row is in ALU-RTYPE
    execution mode when `is_external_op = 1`, `op = opcode_lit`,
    `m32 = 0` (64-bit operands), and `set_pc = 0` (no PC mutation).

    We intentionally do **not** constrain `flag`: SLT/SLTU emit their
    boolean result via `flag`, so pinning `flag = 0` would invalidate
    those two. SUB/AND/OR/XOR's `op_*` always returns `flag = false`
    but at the Main-row level that is a Binary-SM output, not an
    input; leaving `flag` free keeps the archetype uniform across all
    six RTYPE opcodes. -/
@[simp]
def main_row_in_alu_rtype_mode
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (opcode_lit : FGL) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0

/-- **Archetype circuit-holds.** Packs the Main AIR's boolean /
    disjointness booleans + bus-match to an abstract entry + mode
    witnesses. Parametric over the Zisk opcode literal. The bus-match
    hypothesis is the link to a concrete Binary-SM row. -/
@[simp]
def alu_rtype_archetype_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit : FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_alu_rtype_mode m r_main opcode_lit
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- The 64-bit value packed into Main's `(c_0, c_1)` lanes. Redeclared
    here (instead of importing `Circuit.Add.main_c_packed`) so the
    archetype module has no dependency on `Circuit.Add`; downstream
    ALU-RTYPE opcodes are identical to ADD in this packing. -/
@[simp]
def main_c_packed (m : Valid_Main C FGL FGL) (r : ℕ) : FGL :=
  m.c_0 r + m.c_1 r * 4294967296

/-- **Archetype bus-match theorem.** Parametric version of
    `Circuit.Mul.mul_compositional`'s bus-match identity, adapted to an
    abstract bus entry (as in `Tactics/ShiftArchetype.lean`).

    Under ALU-RTYPE mode witnesses + bus-match, Main's packed `c`
    equals `bus_entry.c_lo + bus_entry.c_hi * 2^32`, i.e. Main
    faithfully carries the Binary-SM's packed 64-bit output on the
    two `c` lanes. The Binary SM's internal correctness (that
    `c_lo`/`c_hi` decode to the opcode's semantics on `a`/`b`) is
    a separate audit obligation. -/
lemma alu_rtype_archetype_c_bus_match
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit : FGL)
    (h : alu_rtype_archetype_circuit_holds m r_main bus_entry opcode_lit) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 := by
  obtain ⟨_, _, _, _h_mode, h_match⟩ := h
  obtain ⟨_, _, _, _, _, _, h_match_clo, h_match_chi, _, _, _, _⟩ := h_match
  simp only [opBus_row_Main] at h_match_clo h_match_chi
  unfold main_c_packed
  rw [h_match_clo, h_match_chi]

end ZiskFv.Tactics.ALURTypeArchetype
