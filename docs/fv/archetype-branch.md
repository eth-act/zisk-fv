# Branch archetype (BEQ/BNE/BLT/BGE/BLTU/BGEU) — Phase 2 A1 delivery

This note describes the **branch proof archetype** that Phase 2 A1 established
and that Phase 3 will instantiate across the remaining five RV64IM branches.

## What a branch archetype proof proves

Given an RV64IM branch opcode `B<cmp>`, the archetype closes the
*circuit-side* piece of the metaplan theorem

```
execute_instruction (.BTYPE (imm, r2, r1, cmp)) state =
  (bus_effect exec_row mem_row state).2
```

reducing it to three hypotheses the caller supplies:

1. a transpile axiom (`transpile_B<cmp>`) fixing the Zisk
   microinstruction row's opcode, `is_external_op = 1`, `set_pc = 0`,
   `m32 = 0`, `jmp_offset1`, `jmp_offset2`, and the `a`/`b` lane
   population;
2. a Sail-side `execute_<cmp>_pure_equiv` lemma (per-opcode — BEQ is
   closed in Phase 2; BNE/etc. close via the same pattern with
   `LeanRV64D.Functions.execute_BTYPE`'s appropriate match arm);
3. a bus-emission hypothesis `h_bus_execute_matches_sail` identifying
   the circuit's two-entry execution bus + (empty) memory bus with
   the Sail pure-spec monadic block.

## Archetype deliverables (files landed Phase 2 A1)

* `ZiskFv/Tactics/BranchArchetype.lean` — module containing:
  * `branch_archetype_circuit_holds` — parametric circuit-holds
    predicate over `opcode_lit`;
  * `branch_archetype_pc_dispatch` — parametric theorem; main archetype
    output;
  * `branch_archetype_taken` / `branch_archetype_not_taken` — the two
    case-split corollaries;
  * `branch_archetype_proof` — convenience tactic macro.
* `ZiskFv/Spec/BranchEqual.lean` — BEQ-specific compositional theorem
  (`branch_eq_compositional`). Same shape as the archetype lemma but
  pinned to `OP_EQ = 9`; delivered as a concrete specialization so
  reviewers can diff it against the macro.
* `ZiskFv/Equivalence/BranchEqual.lean` — BEQ's metaplan theorem
  (`equiv_BEQ_metaplan`) + companions (`equiv_BEQ`, `equiv_BEQ_sail`).
* `ZiskFv/RV64D/beq.lean` — BEQ's Sail equivalence lemma
  (`execute_BEQ_pure_equiv`) — **closed** in Phase 2 A1 (previously
  `sorry`ed).
* `ZiskFv/GoldenTraces/BEQ.lean` — concrete taken/not-taken fixture.

## Macro call shape

The Phase 3 fan-out for the other five branches follows this
template (pseudocode for BNE; the pattern is identical for
BLT/BGE/BLTU/BGEU):

```lean
import ZiskFv.Tactics.BranchArchetype
import ZiskFv.RV64D.bne  -- opcode-specific Sail equivalence (close in Phase 3)

namespace ZiskFv.Equivalence.BranchNotEqual

open ZiskFv.Tactics.BranchArchetype

theorem equiv_BNE
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : branch_archetype_circuit_holds m r_main next_pc OP_EQ) :
    -- Same next-pc dispatch, different Sail-side opcode matching.
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) := by
  let opcode_lit : FGL := OP_EQ
  branch_archetype_proof

-- Sail-equivalence via the pure spec:
theorem equiv_BNE_sail ...
  -- Wraps PureSpec.execute_BNE_pure_equiv (closed Phase 3).

theorem equiv_BNE_metaplan ... := by
  rw [equiv_BNE_sail ...]
  exact h_bus_execute_matches_sail.symm
```

## Per-opcode parameters (Phase 3 fan-out table)

| Opcode | `opcode_lit` | `jmp_offset1` (from `create_branch_op`) | `jmp_offset2` | Sail `bop` arm | Comparison predicate |
|--------|--------------|------------------------------------------|---------------|----------------|-----------------------|
| BEQ    | `OP_EQ = 9`  | `imm`                                    | `4`           | `.BEQ`         | `r1 == r2`            |
| BNE    | `OP_EQ = 9`  | `4`                                      | `imm`         | `.BNE`         | `r1 != r2`            |
| BLT    | `OP_LT = 7`  | `imm`                                    | `4`           | `.BLT`         | `zopz0zI_s r1 r2`     |
| BGE    | `OP_LT = 7`  | `4`                                      | `imm`         | `.BGE`         | `zopz0zKzJ_s r1 r2`   |
| BLTU   | `OP_LTU = 6` | `imm`                                    | `4`           | `.BLTU`        | `zopz0zI_u r1 r2`     |
| BGEU   | `OP_LTU = 6` | `4`                                      | `imm`         | `.BGEU`        | `zopz0zKzJ_u r1 r2`   |

The **opcode-literal distinction** (`OP_EQ` / `OP_LT` / `OP_LTU`)
affects only the transpile axiom and the bus-emission hypothesis —
the Main-AIR's `flag`-handshake is identical for all six.

The **offset swap** (`neg=true` in `create_branch_op`) is a property
of the transpile axiom, not the archetype lemma. For BNE, the
transpile axiom guarantees `jmp_offset1 = 4` and `jmp_offset2 = imm`;
`flag = 1` then produces `next_pc = pc + 4` (not taken because Binary
SM reports equality), which corresponds to BNE's fall-through.

## Archetype assumptions

### Required in scope at macro-call site

* `m : Valid_Main C FGL FGL`
* `r_main : ℕ`
* `next_pc : FGL`
* `opcode_lit : FGL`
* `h_circuit : branch_archetype_circuit_holds m r_main next_pc opcode_lit`

If the caller names the hypothesis `h_circuit_<opcode>` instead of
`h_circuit`, the macro will fail — per-opcode proofs should either
rename or (cleaner) call `branch_archetype_pc_dispatch` directly.

### Pre-conditions (from the transpile axiom)

The `main_row_in_branch_mode` predicate must hold — i.e. the Main row
must have the expected opcode literal, be an external op, be 64-bit
(`m32 = 0`), and have `set_pc = 0`. `transpile_B<cmp>` axioms encode
these; wrap the axiom's conclusion into `branch_archetype_circuit_holds`
via the per-opcode mode-assembly lemma.

### Post-conditions (what the macro concludes)

The flag-dispatched next-pc formula:
`next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)`.

For branch-taken (`flag = 1`) this simplifies to `next_pc = pc + jmp_offset1`;
for not-taken (`flag = 0`) to `next_pc = pc + jmp_offset2`.

## Intended use in Phase 3

Phase 3's long-tail sweep closes BNE/BLT/BGE/BLTU/BGEU by:

1. closing the per-opcode Sail equivalence in `RV64D/<opcode>.lean`
   using `jump_to_equiv` (same pattern as BEQ — the five already-ported
   files have `sorry`s on this lemma);
2. writing a per-opcode `Equivalence/<Opcode>.lean` that calls
   `branch_archetype_proof` for the circuit-side piece and
   wraps the Sail pure-spec equivalence for the Sail side;
3. adding a golden-trace fixture per opcode.

One subagent per opcode; all five parallelize after Phase 2 A1 lands.

## Limitations & future work

* **The archetype does not prove `flag` correctness.** The
  `flag = 1 ↔ a == b` (or `<`, `<u`) relationship is delegated to the
  Binary SM via the operation bus. Phase 4 audit derives this from the
  PIL-level bus-emission spec (same as `h_bus_execute_matches_sail`).
* **PC handshake (Main constraint 20) is not extracted from
  `.pilout`.** `zisk-pil-extract` skips the constraint because it
  uses a negative rotation (`'`-prefixed previous-row cells). The
  archetype exposes the handshake as a named predicate
  (`Airs.Main.pc_handshake`), parameterized on a caller-supplied
  `next_pc` cell. Phase 4 extractor feature adds negative-rotation
  support; Phase 4 audit wires it to the PIL row-to-row trace.
* **No bus-emission derivation.** Like `equiv_ADD_metaplan`, all six
  branch metaplan theorems parameterize `h_bus_execute_matches_sail`.
  Phase 4 closes the loop by deriving it from a reusable
  `Airs/BusEmission.lean` module.
