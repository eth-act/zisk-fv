import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus

/-!
**RTYPEW archetype macros / generic lemmas.**

The two Binary-SM RTYPEW opcodes (ADDW, SUBW) and the
immediate sibling ADDIW share the `m32 = 1` variant of the
`ALURTypeArchetype` pattern:

* `op` = one of `OP_ADD_W = 26` or `OP_SUB_W = 27` (Binary type,
  `zisk_ops.rs:408-409`);
* `is_external_op = 1`, type `Binary` — dispatched to the Binary SM
  via the operation bus;
* `m32 = 1` — 32-bit variants; the PIL `a = [a[0], (1 - m32) *
  a[1]]` / `b = [b[0], (1 - m32) * b[1]]` bus-zeroing zeros out the
  high lanes on the bus entry;
* `flag = 0` — ADDW / SUBW's `op_*` functions return `(_, false)`
  (`zisk_ops.rs:572` for `op_add_w`, `zisk_ops.rs:596` for `op_sub_w`);
* `set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`.

This module is the `m32 = 1` twin of
`Tactics/ALURTypeArchetype.lean`. We duplicate rather than mutate the
shared macro — the m32-0 archetype's mode predicate hardcodes
`m32 = 0`, and fighting the parameterization carries more risk than
copying the five-line bus-match skeleton.

The core identity is bus-passthrough on the `c` lanes: Main's packed
`c` equals the bus entry's packed `c` (`c_lo + c_hi * 2^32`),
independent of `m32`. The `m32 = 1` bit affects only the operand-side
(`a_hi` / `b_hi`) bus zeroing, which is a separate Binary-SM audit
obligation's concern.

## Parameterization

* `opcode_lit : FGL` — the Zisk opcode literal for the RTYPEW
  variant. `OP_ADD_W = 26`, `OP_SUB_W = 27` (and, for the ADDIW
  immediate sibling, also `OP_ADD_W = 26`).

## Usage pattern

```
lemma addw_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : rtypew_archetype_circuit_holds m r_main bus_entry OP_ADD_W) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  rtypew_archetype_c_bus_match m r_main bus_entry OP_ADD_W h
```
-/

namespace ZiskFv.Tactics.RTypeWArchetype

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Archetype mode predicate (Main side).** A Main row is in
    RTYPEW execution mode when `is_external_op = 1`, `op =
    opcode_lit`, `m32 = 1` (32-bit operands), `flag = 0`, and
    `set_pc = 0`. The key difference from
    `ALURTypeArchetype.main_row_in_alu_rtype_mode` is the `m32 = 1`
    bit; ADDW / SUBW / ADDIW all return `flag = false` from their
    Binary-SM `op_*` hooks, so we pin `flag = 0` (unlike SLT / SLTU
    in the m32-0 archetype). -/
@[simp]
def main_row_in_rtypew_mode
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (opcode_lit : FGL) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = opcode_lit
  ∧ m.m32 r_main = 1
  ∧ m.flag r_main = 0
  ∧ m.set_pc r_main = 0

/-- **Archetype circuit-holds.** Packs the Main AIR's boolean /
    disjointness booleans + bus-match to an abstract entry + mode
    witnesses. Parametric over the Zisk opcode literal. The
    bus-match hypothesis is the link to a concrete Binary-SM row. -/
@[simp]
def rtypew_archetype_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit : FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ main_row_in_rtypew_mode m r_main opcode_lit
  ∧ matches_entry (opBus_row_Main m r_main) bus_entry

/-- The 64-bit value packed into Main's `(c_0, c_1)` lanes.
    Redeclared here (instead of importing `Circuit.Add.main_c_packed`)
    so the archetype module has no dependency on `Circuit.Add`. -/
@[simp]
def main_c_packed (m : Valid_Main C FGL FGL) (r : ℕ) : FGL :=
  m.c_0 r + m.c_1 r * 4294967296

/-- **Archetype bus-match theorem (m32 = 1 variant).** Parametric
    version of the `c`-lane bus identity for RTYPEW opcodes. Under
    the mode witnesses + bus-match, Main's packed `c` equals
    `bus_entry.c_lo + bus_entry.c_hi * 2^32` — i.e. Main faithfully
    carries the Binary SM's packed 64-bit output on the two `c`
    lanes (`c_lo` = low 32 = sign-extended 32-bit op result low 32,
    `c_hi` = high 32 = sign-extension of bit 31). The Binary SM's
    internal correctness (that `c_lo`/`c_hi` decode to
    `sign_extend_32_to_64 (op_32 (low32 a) (low32 b))`) is a
    separate audit obligation. -/
lemma rtypew_archetype_c_bus_match
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (opcode_lit : FGL)
    (h : rtypew_archetype_circuit_holds m r_main bus_entry opcode_lit) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 := by
  obtain ⟨_, _, _, _h_mode, h_match⟩ := h
  obtain ⟨_, _, _, _, _, _, h_match_clo, h_match_chi, _, _, _, _⟩ := h_match
  simp only [opBus_row_Main] at h_match_clo h_match_chi
  unfold main_c_packed
  rw [h_match_clo, h_match_chi]

end ZiskFv.Tactics.RTypeWArchetype
