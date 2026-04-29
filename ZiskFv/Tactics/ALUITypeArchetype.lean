import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.ALURTypeArchetype

/-!
**ALU ITYPE archetype** (Phase 3C Track T-IT).

The six Phase 3C ALU-ITYPE opcodes (ADDI, ANDI, ORI, XORI, SLTI,
SLTIU) share a ZisK microinstruction shape that differs from their
RTYPE siblings only in the `b` lane source — `immediate_op` emits
`src_b("imm", i.imm as u64, false)` rather than `src_b("reg", rs2,
false)`. The Main-AIR constraint conjunction the archetype relies on
is **b-source-agnostic**: the `matches_entry` bus-match predicate and
the boolean / disjointness flags only constrain `is_external_op`,
`op`, `m32`, `set_pc`, and the `c_lo`/`c_hi` lanes. The `a`/`b` lanes
enter only through the bus entry the caller supplies, which this
module does not inspect.

Concretely the ALU-ITYPE and ALU-RTYPE archetypes share an identical
**circuit-level** identity: `main_c_packed = bus_entry.c_lo +
bus_entry.c_hi * 2^32`. We therefore **re-use**
`Tactics.ALURTypeArchetype`'s primitives verbatim here, exporting a
shallow rebranded alias. This keeps the track-T-RT and track-T-IT
consumer sites textually symmetric while sidestepping the Phase 3
plan's Fragility #1 risk — mutating `ALURTypeArchetype` to generalize
over b-source would be invasive; duplication via alias costs <30
lines.

## Parameterization

Identical to `ALURTypeArchetype`: `opcode_lit : FGL` — one of
`OP_ADD` (ADDI), `OP_AND` (ANDI), `OP_OR` (ORI), `OP_XOR` (XORI),
`OP_LT` (SLTI), `OP_LTU` (SLTIU). All ITYPE opcodes run at `m32 = 0`.

## Usage pattern

```
theorem addi_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : alu_itype_archetype_circuit_holds m r_main bus_entry OP_ADD) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_itype_archetype_c_bus_match m r_main bus_entry OP_ADD h
```
-/

namespace ZiskFv.Tactics.ALUITypeArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ALURTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Archetype mode predicate (Main side, ITYPE).** Alias for
    `ALURTypeArchetype.main_row_in_alu_rtype_mode` — Main's column
    predicates (`is_external_op = 1`, `op = opcode_lit`, `m32 = 0`,
    `set_pc = 0`) are identical across RTYPE and ITYPE since the
    `a`/`b` lane sources are not constrained by these columns. -/
@[simp]
def main_row_in_alu_itype_mode
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (opcode_lit : FGL) : Prop :=
  main_row_in_alu_rtype_mode m r_main opcode_lit

/-- **Archetype circuit-holds (ITYPE).** Alias for
    `ALURTypeArchetype.alu_rtype_archetype_circuit_holds`. Same
    Main-side boolean / disjointness booleans + bus-match; the
    difference from RTYPE is purely in the *transpile* axiom (which
    governs the b lanes the caller is expected to thread through the
    bus entry), not in the Main-AIR column predicates this archetype
    references. -/
@[simp]
def alu_itype_archetype_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit : FGL) : Prop :=
  alu_rtype_archetype_circuit_holds m r_main bus_entry opcode_lit

/-- **Archetype bus-match theorem (ITYPE).** Under ALU-ITYPE mode
    witnesses + bus-match, Main's packed `c` equals `bus_entry.c_lo +
    bus_entry.c_hi * 2^32`. Delegates to
    `ALURTypeArchetype.alu_rtype_archetype_c_bus_match` — the proof is
    bit-for-bit identical. The Binary SM's internal correctness (that
    `c_lo`/`c_hi` pack the signed/unsigned/logical opcode's result on
    the `a`/`b` lanes the transpile axiom pinned) is the Phase 4 audit
    obligation. -/
theorem alu_itype_archetype_c_bus_match
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit : FGL)
    (h : alu_itype_archetype_circuit_holds m r_main bus_entry opcode_lit) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_rtype_archetype_c_bus_match m r_main bus_entry opcode_lit h

end ZiskFv.Tactics.ALUITypeArchetype
