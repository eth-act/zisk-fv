# Per-shape promise-bundle struct design

## Context

The 63 canonical `equiv_<OP>` theorems in `ZiskFv/Equivalence/<Op>.lean`
each take a long binder list — typically 17 to 80+ hypotheses — covering
register-read facts, bus-protocol structural assertions, AIR mode pins,
byte-range obligations, and lane-match assertions. Reading the binder
list is one of the audit's most repetitive tasks: an auditor reviewing
six ALU-RTYPE opcodes effectively re-reads the same dozen structural
binders six times.

This document proposes the **per-shape promise-bundle struct** lift:
collect each shape's structurally-uniform binders into a per-shape
`<Shape>Promises` record, leaving only opcode-specific binders inline.

## Per-shape binder taxonomy

Each of the 12 instruction-shape archetypes (`Tactics/<Shape>Archetype.lean`)
groups a set of opcodes that share a uniform binder structure. Below,
for each shape, we list:

- **opcodes covered** (the per-opcode `equiv_<OP>` theorems that
  belong to this shape)
- **bundle-candidate binders** (structurally uniform; lift into
  `<Shape>Promises`)
- **opcode-specific binders** (parametrise the bundle by these or
  keep them as separate args; cannot be bundled)

### Sketch (provisional; numbers from `Explore` agent audit)

| Shape | Opcodes covered (count) | Structural binders (estimate) | Opcode-specific binders (estimate) |
|---|---|---:|---:|
| **ALU-RTYPE** | SUB, AND, OR, XOR, SLT, SLTU (6) | ~14 | ~3 + (Binary lane-match bundle) |
| **ALU-ITYPE** | ADDI, ANDI, ORI, XORI, SLTI, SLTIU, SLLI, SRLI, SRAI (9) | ~14 | ~3 + (Binary lane-match bundle) |
| **U-TYPE** | LUI, AUIPC (2) | ~17 | ~1 (`h_circuit` archetype) |
| **BRANCH** | BEQ, BNE, BLT, BLTU, BGE, BGEU (6) | ~14 | ~3 |
| **LOAD** | LBU, LHU, LWU, LD (4 + 7 sext) | ~16 | varies (Mem entry shape) |
| **STORE** | SB, SH, SW, SD (4) | ~15 | varies (Mem entry shape) |
| **JUMP** | JAL, JALR (2) | ~15 | ~2 |
| **MUL** | MUL, MULH, MULHU, MULHSU, MULW (5) | ~15 | ~30 (Arith carry chain) |
| **SHIFT** | SLLW, SLLIW, SRAW, SRAIW, SRLW, SRLIW (6) | ~16 | varies (BinaryExt lanes) |
| **R-TYPE-W** | ADDW, SUBW (2) | ~14 | varies |
| **ARITH-SM** | DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW (8) | ~14 | ~30 (Arith carry chain) |
| **SIGN-EXT-LOAD** | LB, LH, LW (3) | ~16 | varies |
| **FENCE** | FENCE (1) — degenerate | ~10 | ~0 |

Total: 63 opcodes. The structural binder count is *approximate*; the
actual figures emerge from the per-shape audit during implementation.

### Per-shape struct shape (worked example: U-TYPE)

U-TYPE is the simplest shape — 2 opcodes (LUI, AUIPC), the smallest
binder list, no Binary or Arith AIR dependencies.

Pre-refactor (current `equiv_LUI` from `ZiskFv/Equivalence/Lui.lean`):

```lean
theorem equiv_LUI
    (state : SailState)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_imm : lui_input.imm = imm)
    (h_input_rd : lui_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some lui_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches : ... = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1)
    (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq : (PureSpec.execute_LUI_pure lui_input).nextPC = nextPC_val)
    (h_rd_idx : lui_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_circuit : lui_archetype_circuit_holds m r_main next_pc) :
    ... = ... := by ...
```

Post-refactor (proposed):

```lean
-- ZiskFv/Equivalence/Promises/UType.lean (new file)
structure UTypePromises
    (state : SailState)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (imm : BitVec 20) (rd : regidx)
    (input_imm : BitVec 20) (input_rd : Fin _)
    (input_pc : BitVec 64) (pure_pc : BitVec 64)
    (nextPC_val : BitVec 64) where
  input_imm_eq : input_imm = imm
  input_rd_eq : input_rd = regidx_to_fin rd
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
  exec_len : exec_row.length = 2
  e0_mult : exec_row[0]!.multiplicity = -1
  e1_mult : exec_row[1]!.multiplicity = 1
  nextPC_matches : (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val)) = nextPC_val
  rd_mult : e_rd.multiplicity = 1
  rd_as : e_rd.as.val = 1
  nextPC_eq : pure_pc = nextPC_val
  rd_idx : input_rd.val = (Transpiler.wrap_to_regidx e_rd.ptr).val
```

Then:

```lean
-- ZiskFv/Equivalence/Lui.lean (refactored)
theorem equiv_LUI
    {state : SailState}
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20) (rd : regidx)
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    {e_rd : Interaction.MemoryBusEntry FGL}
    (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (promises : UTypePromises state exec_row e_rd imm rd
        lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC nextPC_val)
    (h_circuit : lui_archetype_circuit_holds m r_main next_pc) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  obtain ⟨h_input_imm, h_input_rd, h_input_pc, h_exec_len, h_e0_mult,
          h_e1_mult, h_nextPC_matches, h_rd_mult, h_rd_as, h_nextPC_eq,
          h_rd_idx⟩ := promises
  -- ... rest of original proof body, unchanged ...
```

The proof body destructures `promises` at the top, then proceeds
unchanged.

### Design tension

The `<Shape>Promises` struct is heavily parametrised — it takes ~10
type/value parameters that the canonical theorem passes in. The
*upside* is that all opcodes of the same shape pass identical-shape
parameter lists; the *downside* is that the struct definition itself
is dense.

**Net effect on caller-burden:** the canonical theorem's binder list
shrinks from ~17 (LUI) to ~5 (`promises` + 4 opcode-specific args).
Multiplied across 63 opcodes that's a substantial reduction in audit
surface.

**Net effect on trust-gate:** the V2 `forbidden-types.txt` binder
walk uses `forallTelescope` + `whnfR`. Marking each `<Shape>Promises`
`@[reducible] structure` lets `whnfR` unfold the struct to its fields,
so the binder walk sees the same field types as before. **This is
load-bearing** — if `@[reducible]` is missed, the gate stops seeing
the field types and the audit loses the binder-shape guarantee.

## Implementation plan

The refactor lands in 14 commits (one per shape + 2 wrap-up):

1. **Commit 1 — Design doc + tooling.** This doc + extensions to
   `trust/scripts/regenerate-caller-burden.py` to unfold a `<Shape>Promises`
   binder by one level when emitting the ledger. (No proof changes.)
2. **Commits 2-13 — One shape per commit.** Each commit adds
   `ZiskFv/Equivalence/Promises/<Shape>.lean` with the struct
   definition, refactors all canonical theorems of that shape to
   take the struct, and updates the matching wrappers in
   `Compliance/Wrappers/<Op>.lean`. Per-commit gate green:
   `lake build` + V1 + V2 + regenerated baselines. Order:
   * Commit 2: U-TYPE (2 opcodes — pilot)
   * Commit 3: BRANCH (6 opcodes)
   * Commit 4: ALU-RTYPE (6 opcodes)
   * Commit 5: ALU-ITYPE (9 opcodes)
   * Commit 6: R-TYPE-W (2 opcodes)
   * Commit 7: SHIFT (6 opcodes)
   * Commit 8: JUMP (2 opcodes)
   * Commit 9: LOAD (4 opcodes)
   * Commit 10: SIGN-EXT-LOAD (3 opcodes)
   * Commit 11: STORE (4 opcodes)
   * Commit 12: MUL (5 opcodes)
   * Commit 13: ARITH-SM (8 opcodes)
   * Commit 14: FENCE + cleanup
3. **Commit 15 — Audit-facing doc.** `docs/fv/promise-bundles.md`
   describing each `<Shape>Promises` schema in audit-friendly prose,
   linked from `docs/fv/trusted-base.md`. Update `trust/README.md`
   with the new ledger format. Append a per-shape entry to
   `trust/structural-unpacking-exceptions.txt`.

## Realistic scope

This refactor is **multi-session work**. Each shape commit involves:
- Designing the struct (1 hour)
- Refactoring 2-9 canonical theorems (5-30 min each)
- Refactoring 2-9 trust-discharge wrappers (5-30 min each)
- Verifying `lake build` (5 min per cycle, multiple cycles)
- Regenerating + reviewing trust baselines

Conservatively: 2-4 hours per shape × 12 shapes ≈ 30-50 hours of focused
implementation, plus review time.

The current commit (Phase 4.0) lands ONLY the design doc + the
U-TYPE pilot. Remaining shapes are tracked as follow-up work, with
this design doc as the load-bearing reference for the schema each
shape's commit produces.

## Open design questions (for follow-up)

1. **Struct parametrisation strategy.** Direct value-level
   parametrisation (as in the U-TYPE sketch) vs. typeclass-based
   abstraction over the opcode's `PureInput` record. Direct
   parametrisation is simpler and more transparent; typeclass adds
   one abstraction level but may consolidate shared fields better.
   Decision deferred to the per-shape implementation; the pilot
   commit uses direct parametrisation.
2. **AIR-witness inclusion.** Some shapes (ALU, MUL, ARITH-SM) take a
   `Valid_<AIR>` witness in addition to `Valid_Main`. Whether these
   live in the bundle (parametrised by the AIR type) or stay as
   separate arguments. Pilot keeps them separate.
3. **Bridge invocation.** Some canonical theorems consume both the
   bundle AND an explicit `h_circuit` archetype-predicate witness.
   Whether to bundle `h_circuit` too. Pilot keeps it separate.
4. **`Valid_Main` row index `r_main`.** Currently a separate arg in
   every canonical theorem. Could be bundled with the
   `Valid_Main` witness or stay free. Pilot keeps it free.
