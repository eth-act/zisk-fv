import Mathlib

import ZiskFv.Equivalence.Lui
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `equiv_LUI` trust-discharge wrapper — ControlFlow non-branch shape exemplar
## Why LUI

LUI is the cheapest non-branch ControlFlow opcode:

* No `rs1` / `rs2` read (no operand bridge — category 5 is N/A).
* No PC offset / no-wrap precondition (unlike AUIPC's
  `h_no_wrap` / `h_lo_bound` / `h_pc_offset_lt_2_32`).
* No signed-vs-unsigned distinction (category 3 N/A).
* No mode columns on a provider AIR (category 2 N/A — LUI is
  Main-only, no provider).
* Range/bound (category 4) is fully discharged inside the
  canonical `equiv_LUI` via `memory_bus_entry_byte_range_perm_sound`.
* Lane-match (category 1) is fully discharged inside the canonical
  `equiv_LUI` via `Bridge/ControlFlow.lui_discharge_lanes`.

The remaining discharge target is the bundled
`h_circuit : lui_archetype_circuit_holds m r_main next_pc` — a
**constructibility obligation** packing per-row constraints + mode
pins. This wrapper shows how `Compliance.lean` will supply
`h_circuit` from three trust-ledger-style ingredients:

1. The activation pin `m.is_external_op r_main = 0` (Compliance.lean
   delivers this from the Main AIR's ROM handshake on the row hosting
   the LUI instruction).
2. The opcode pin `m.op r_main = OP_COPYB` (likewise from the
   ROM handshake).
3. The per-row Main constraint bundle `lui_subset_holds m r_main next_pc`
   (Compliance.lean delivers this from
   `∀ r, lui_universal_row m r`, the universal-row Main validity).

Together with `transpile_LUI` (class #1) — which derives the routing
pins `m32 = 0`, `set_pc = 0`, `store_pc = 0` from activation + opcode
pin — we assemble `lui_archetype_circuit_holds` and delegate to
`equiv_LUI`.

## 5-category discharge applied

* **Lane-match.** Internalized by `equiv_LUI` via
  `lui_discharge_lanes` (consumes `main_store_pc_emission_bundle`,
  trust class #4). Pre-discharged on the canonical surface.
* **Mode pins.** N/A for the provider-AIR sense (no provider AIR).
  The Main-side mode pins (`m32 = 0`, `set_pc = 0`, `store_pc = 0`,
  `jmp_offset2 = 4`, `b_0 = imm_lo`, `b_1 = imm_hi`) come from
  `transpile_LUI` (class #1) — already consumed inside `equiv_LUI`'s
  proof.
* **Sign-witness pins.** N/A (no signed-vs-unsigned distinction at
  the operand-pack layer).
* **Range/bound.** Internalized by `equiv_LUI` via
  `memory_bus_entry_byte_range_perm_sound` (class #5b).
  Pre-discharged on the canonical surface.
* **Operand bridges.** N/A — no register read. State-bridge
  hypotheses (`h_input_imm`, `h_input_rd`, `h_input_pc`) pass
  through unmodified.

## Anti-laundering report

Per the discharge-recipe.md wrapper-specific checks:

* **No new axioms.** This wrapper consumes only `transpile_LUI`
  (class #1) and `equiv_LUI` itself. Trust ledger unchanged at 116
  axioms — matches the per-AIR axiom map's 0-new-axioms prediction
  for ControlFlow.
* **Bridges cross-shape if possible.** N/A — this opcode adds no
  helpers; the only derivation (mode pins from activation +
  opcode pin) is a 4-line application of `transpile_LUI`.
* **Caller-burden shrinks.** See the count below.

## Caller-burden

`equiv_LUI` (canonical): 22 binders / 12 hypotheses.
`equiv_LUI_from_trust` (this file): 22 binders / 13 hypotheses.

The hypothesis-count *grows by 1* on this opcode because the
discharged `h_circuit` is itself a *bundle* of two structural
parts (`lui_subset_holds` + `main_row_in_lui_mode`), and the
wrapper unpacks it into three caller-supplied ingredients
(`h_main_active`, `h_main_op_lui`, `h_lui_subset`). The two added
hypotheses minus the removed one (and minus the removed
`h_nextPC_eq` / `nextPC_val` made `rfl` by setting
`nextPC_val := lui_input.PC + 4#64`) yields +1 net hypothesis at the
per-opcode level.

This is the **structural-unpacking pattern** documented in
`trust/structural-unpacking-exceptions.txt` (though LUI itself is
not on that list because no canonical-theorem refactor occurred —
the unpacking happens only in this Compliance wrapper). The Compliance
caller collapses `(m, ∀ r, lui_universal_row m r)` into one set of
shared parameters across all eleven ControlFlow opcodes plus all
Main-only opcodes — so at the *global* level the trust footprint
strictly shrinks.

The two `h_main_active` / `h_main_op_lui` pins themselves come from
Compliance.lean's program-counter handshake — they are SHARED with
the eventual ControlFlow branch wrappers and the other UTYPE
wrapper (AUIPC) once those are authored.

## Cross-shape lesson

ControlFlow non-branch needs **no per-opcode trust-ledger axiom**.
The only ingredients are:
1. `transpile_<OP>` (class #1) — already in place for LUI / JAL /
   JALR / AUIPC.
2. The universal per-row Main constraint bundle (a constructibility
   obligation on `Valid_Main`, not an axiom).
3. The activation / opcode pin (delivered by Compliance.lean from
   the Main AIR's ROM handshake).

This generalizes mechanically to JAL / JALR / AUIPC. The pilot
confirms the per-AIR axiom map's prediction: 0 new axioms for
ControlFlow.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Pilot wrapper for `equiv_LUI`.**

    Caller obligations (signature header, ordered):
    1. The Sail-side inputs (`state`, `lui_input`, `imm`, `rd`).
    2. The Main AIR validator with its selected row index
       (`m : Valid_Main`, `r_main`). Compliance.lean shares
       `m` across all Main-only opcodes.
    3. The next-PC Goldilocks witness `next_pc` (Compliance.lean
       supplies this as `m.pc (r_main + 1)`, the next row's PC
       column, via the PC handshake).
    4. The structural bus rows (`exec_row`, `e_rd`).
    5. The activation + opcode pins on Main (`h_main_active`,
       `h_main_op_lui`). Both come from Compliance.lean's
       program-counter handshake on the row hosting the LUI
       instruction.
    6. The per-row Main constraint bundle (`h_lui_subset`).
       Compliance.lean delivers this from a universal
       `∀ r, lui_universal_row m r` parameter shared across all
       ControlFlow non-branch opcodes.
    7. The structural exec/mem row shape — same shape `equiv_LUI`
       accepts; passed through unchanged.
    8. The SPEC-PRE preconditions on the Sail input
       (`h_input_imm`, `h_input_rd`, `h_input_pc`).

    Derived internally (NOT caller-supplied):
    * `m.m32 r_main = 0`, `m.set_pc r_main = 0`,
      `m.store_pc r_main = 0` — from `transpile_LUI` (class #1)
      applied to `h_main_active` + `h_main_op_lui`.
    * `h_circuit : lui_archetype_circuit_holds m r_main next_pc` —
      from `h_lui_subset` + the four transpile-derived mode pins
      packed together.
    * `nextPC_val := lui_input.PC + 4#64`, with `h_nextPC_eq` as
      definitional `rfl` from `execute_LUI_pure`'s definition.

    Trust footprint: `transpile_LUI` + `equiv_LUI`'s closure (which
    transitively consumes `main_store_pc_emission_bundle` (class #4),
    `memory_bus_entry_byte_range_perm_sound` (class #5b),
    `main_columns_in_range` (class #5b), plus platform-feature
    auxiliaries). Zero new axioms — matches `docs/fv/per-air-axiom-map.md`'s
    prediction. -/
theorem equiv_LUI_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    -- AIR validator + row index. Compliance.lean shares (m) across
    -- all Main-only opcodes.
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    -- Activation / opcode pins. Compliance.lean derives these from
    -- the Main AIR's ROM handshake on the row hosting LUI.
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_lui : m.op r_main = OP_COPYB)
    -- Per-row Main constraint bundle. Compliance.lean delivers this
    -- from `∀ r, lui_universal_row m r`, the universal-row Main
    -- validity (shared across all ControlFlow non-branch opcodes
    -- AND the UTYPE shape's twin AUIPC).
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    -- Sail-side state predicates (SPEC-PRE).
    (h_input_imm : lui_input.imm = imm)
    (h_input_rd : lui_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some lui_input.PC)
    -- Bus-protocol structural hypotheses — pass-through from
    -- `equiv_LUI`; Compliance.lean supplies these from the same
    -- bus-shape obligations as every other opcode in the shape.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = lui_input.PC + 4#64)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_rd_idx : lui_input.rd = Transpiler.wrap_to_regidx e_rd.ptr) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  -- ============ Derive routing mode pins via `transpile_LUI` ============
  -- Fire `transpile_LUI` with arbitrary placeholders for the ghost
  -- `Fin 32` / `FGL` / `RV64State` parameters; we consume only the
  -- routing pins (`m32`, `set_pc`, `store_pc`), not the
  -- `jmp_offset` / `a_*` / `b_*` columns (those are internal to
  -- `equiv_LUI`'s `lui_discharge_full`).
  have h_tr := ZiskFv.Trusted.transpile_LUI m r_main (0 : Fin 32)
    (0 : FGL) (0 : FGL)
    { xreg := fun _ => 0#64, pc := 0#64 } h_main_active h_main_op_lui
  obtain ⟨h_m32, h_set_pc, h_store_pc, _, _, _, _, _, _⟩ := h_tr
  -- ============ Assemble `main_row_in_lui_mode` ============
  have h_lui_mode : main_row_in_lui_mode m r_main := by
    refine ⟨h_main_active, ?_, h_m32, h_set_pc, h_store_pc⟩
    -- `OP_COPYB := 1` definitionally; the constraint expects
    -- `m.op r_main = (1 : FGL)`.
    rw [h_main_op_lui]; rfl
  -- ============ Assemble `lui_archetype_circuit_holds` ============
  have h_circuit : lui_archetype_circuit_holds m r_main next_pc :=
    ⟨h_lui_subset, h_lui_mode⟩
  -- ============ Delegate to canonical `equiv_LUI` ============
  -- `nextPC_val := lui_input.PC + 4#64` is the value
  -- `execute_LUI_pure lui_input |>.nextPC` definitionally equals,
  -- so `h_nextPC_eq` reduces to `rfl`.
  exact ZiskFv.Equivalence.Lui.equiv_LUI state lui_input imm rd
    m r_main next_pc exec_row e_rd (lui_input.PC + 4#64)
    h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as
    rfl  -- h_nextPC_eq : (execute_LUI_pure lui_input).nextPC = lui_input.PC + 4#64
    h_rd_idx h_circuit

end ZiskFv.Compliance
