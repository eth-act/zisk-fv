# Jump archetype (JAL) — Phase 2 A2 delivery

This note describes the **unconditional-jump proof archetype** that Phase 2 A2
established. Unlike the branch archetype (six opcodes), the jump archetype is a
singleton in the RV64IM scope: JAL is the only base-ISA unconditional jump that
matches this shape. JALR has a different Zisk microinstruction shape
(`set_pc = 1`, `op = OP_COPYB`, `c[0]` drives next-pc) and gets its own
archetype.

## What a jump archetype proof proves

Given an RV64IM unconditional-jump opcode (JAL), the archetype closes the
*circuit-side* piece of the metaplan theorem

```
execute_instruction (.JAL (imm, rd)) state =
  (bus_effect exec_row mem_row state).2
```

reducing it to three hypotheses the caller supplies:

1. a transpile axiom (`transpile_JAL`) fixing the Zisk microinstruction row's
   opcode, `is_external_op = 0`, `set_pc = 0`, `store_pc = 1`, `m32 = 0`,
   `jmp_offset1`, `jmp_offset2`, and zero `a`/`b` lanes;
2. a Sail-side `execute_JAL_pure_equiv` lemma (closed Phase 2 A2 via
   `jump_to_equiv`);
3. a bus-emission hypothesis `h_bus_execute_matches_sail` identifying the
   circuit's execution + memory bus entries with the Sail pure-spec monadic
   block. (Unlike BEQ, there is **no** operation-bus entry — JAL is an internal
   op.)

## Archetype deliverables (files landed Phase 2 A2)

* `ZiskFv/Tactics/JumpArchetype.lean` — module containing:
  * `jump_archetype_circuit_holds` — parametric circuit-holds predicate over
    `opcode_lit`;
  * `jump_archetype_pc_advance` — parametric theorem (specialized to
    `opcode_lit = 0` because constraint 17 only fires for `OP_FLAG`);
  * `jump_archetype_store_value` — store-value expression resolves to
    `pc + jmp_offset2`;
  * `jump_archetype_proof` — convenience tactic macro.
* `ZiskFv/Spec/Jal.lean` — JAL-specific compositional theorems
  (`jal_pc_advance`, `jal_store_value`). Same shape as the archetype lemmas but
  pinned to `OP_FLAG = 0`; delivered as a concrete specialization so reviewers
  can diff it against the macro.
* `ZiskFv/Equivalence/Jal.lean` — JAL's metaplan theorem (`equiv_JAL_metaplan`)
  + companions (`equiv_JAL`, `equiv_JAL_sail`).
* `ZiskFv/RV64D/jal.lean` — JAL's Sail equivalence lemma
  (`execute_JAL_pure_equiv`) — **closed** in Phase 2 A2 (previously `sorry`ed).
* `ZiskFv/GoldenTraces/JAL.lean` — concrete taken-jump fixture
  (JAL x1, +20 at pc = 100 → next_pc = 120, x1 = 104).
* Transpiler axiom `transpile_JAL` added to `ZiskFv/Fundamentals/Transpiler.lean`;
  `store_pc` field added to `ZiskInstructionRow`. Existing axioms
  `transpile_ADD`/`transpile_BEQ` now pin `store_pc = 0`.

## Macro call shape

The only current in-scope consumer of the jump archetype is JAL itself. If
compressed-ext support (`C_JAL`, `C_J`) is ever added, those opcodes would
reuse this archetype pattern. The template call shape:

```lean
import ZiskFv.Tactics.JumpArchetype

namespace ZiskFv.Equivalence.SomeJump

open ZiskFv.Tactics.JumpArchetype

theorem equiv_<Opcode>
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : jump_archetype_circuit_holds m r_main next_pc (0 : FGL)) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  jump_archetype_proof

theorem equiv_<Opcode>_sail ...
  -- Wraps PureSpec.execute_<Opcode>_pure_equiv.

theorem equiv_<Opcode>_metaplan ... := by
  rw [equiv_<Opcode>_sail ...]
  exact h_bus_execute_matches_sail.symm
```

## Per-opcode parameters (RV64IM scope)

| Opcode | `opcode_lit` | `store_pc` | `set_pc` | `jmp_offset1` | `jmp_offset2` | Sail instruction arm |
|--------|--------------|------------|----------|---------------|---------------|-----------------------|
| JAL    | `OP_FLAG = 0` | `1`       | `0`      | `imm`         | `4`           | `.JAL (imm, rd)`      |

JALR is **not** covered by this archetype. Its distinguishing shape:

| Opcode | `opcode_lit`  | `store_pc` | `set_pc` | `jmp_offset1` | `jmp_offset2` |
|--------|---------------|------------|----------|---------------|---------------|
| JALR   | `OP_COPYB = 1` | `1`        | `1`      | `imm`         | `4`           |

JALR exercises `c[0] + jmp_offset1` as the next-pc source (via `set_pc = 1`)
rather than the flag-dispatched handshake — a different proof structure.

## Archetype assumptions

### Required in scope at macro-call site

* `m : Valid_Main C FGL FGL`
* `r_main : ℕ`
* `next_pc : FGL`
* `h_circuit : jump_archetype_circuit_holds m r_main next_pc (0 : FGL)`

### Pre-conditions (from the transpile axiom)

The `main_row_in_jump_mode` predicate must hold — i.e. the Main row must have
`is_external_op = 0`, `op = 0` (OP_FLAG), `m32 = 0`, `set_pc = 0`, and
`store_pc = 1`. `transpile_JAL` encodes all five; wrap the axiom's conclusion
into `jump_archetype_circuit_holds` via the per-opcode mode-assembly lemma.

### Post-conditions (what the macro concludes)

The unconditional PC advance: `next_pc = pc + jmp_offset1`. With
`transpile_JAL`'s `jmp_offset1 = imm`, this is `next_pc = pc + imm`.

The accompanying `jump_archetype_store_value` lemma proves the
`store_value[0]` (PIL `main.pil:311`) resolves to `pc + jmp_offset2 = pc + 4`,
which is what gets written to rd via the memory bus.

## Intended use

Because JAL is the only RV64IM opcode with this shape, there is no fan-out
equivalent of the branch archetype's six-opcode table. The macro is retained
for:

* **Compressed-ext expansion.** `C_JAL` / `C_J` from `Ext_Zca` would consume
  it directly. ZisK currently targets RV64IM only; these remain out of scope.
* **Per-opcode refactor stability.** Any future refactor that reorganizes
  `Spec.Jal` can validate correctness by showing `Spec.Jal.jal_pc_advance`
  still factors through `jump_archetype_pc_advance`.
* **Archetype discipline.** Phase 2's "every archetype delivers a macro" rule
  applies to JAL even though JAL is a singleton. Better to ship the macro and
  not need it than to ship a one-off proof that later fan-out cannot reuse.

## Limitations & future work

* **The archetype hard-codes `opcode_lit = 0`.** `jump_archetype_pc_advance`
  requires `OP_FLAG = 0` because constraint 17 (`internal_op0_sets_flag`) only
  fires for `op = 0`. Any hypothetical jump-shape instruction with a different
  opcode would need its own flag-derivation lemma.
* **PC handshake (Main constraint 20) is not extracted from `.pilout`.** Same
  limitation as the branch archetype — `zisk-pil-extract` skips it because of
  the negative rotation. The archetype exposes the handshake as the named
  predicate `Airs.Main.pc_handshake`, parameterized on a caller-supplied
  `next_pc` cell.
* **No bus-emission derivation.** Like `equiv_ADD_metaplan` /
  `equiv_BEQ_metaplan`, `equiv_JAL_metaplan` parameterizes
  `h_bus_execute_matches_sail`. Phase 4 closes the loop by deriving it from a
  reusable `Airs/BusEmission.lean` module.
* **Memory bus for rd-write not modeled compositionally.** JAL writes the
  link address to rd via the memory bus; the `equiv_JAL_metaplan` hypothesis
  assumes this bus entry matches Sail's `write_xreg`. Phase 4 audit proves it
  from the `store_pc` selector + memory-bus schema.
