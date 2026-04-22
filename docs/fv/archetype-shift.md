# Shift archetype (Phase 2 A6)

The **shift archetype** covers the six RV64IM shift opcodes:

| RV64 opcode | Zisk op | `OP_*` | `m32` | Sail dispatch |
|-------------|---------|--------|-------|---------------|
| `SLL`       | `sll`    | `0x21 = 33` | 0 | `RTYPE … rop.SLL`  |
| `SRL`       | `srl`    | `0x22 = 34` | 0 | `RTYPE … rop.SRL`  |
| `SRA`       | `sra`    | `0x23 = 35` | 0 | `RTYPE … rop.SRA`  |
| **`SLLW`**  | `sll_w`  | `0x24 = 36` | 1 | `RTYPEW … ropw.SLLW` |
| `SRLW`      | `srl_w`  | `0x25 = 37` | 1 | `RTYPEW … ropw.SRLW` |
| `SRAW`      | `sra_w`  | `0x26 = 38` | 1 | `RTYPEW … ropw.SRAW` |

A6 lands **SLLW** as the representative (the `m32 = 1` acid test —
no other Phase 2 archetype sets `m32 = 1`). The other five are
Phase 3 fan-out via the macros documented below.

## What's shared

All six share:

* `create_register_op(..., <op-str>, 4)` — one Main-AIR row with
  `is_external_op = 1`, `flag = 0`, `set_pc = 0`, `store_pc = 0`,
  `jmp_offset1 = jmp_offset2 = 4`.
* `src_a = reg(rs1)`, `src_b = reg(rs2)`, `store = reg(rd)`.
* `is_external_op = 1` — the op is type `BinaryE`, dispatched to the
  `BinaryExtension` state machine via the operation bus (**not**
  `BinaryAdd` — that's add/sub/comparison only).
* `ZiskInstBuilder::m32 = "<op>".contains("_w")` — 1 for SLLW/SRLW/
  SRAW, 0 for SLL/SRL/SRA.

## What's opcode-specific

* **Opcode literal** (`op`): the `OP_*` value from
  `vendor/zisk/pil/operations.pil:59-64`.
* **`m32` bit**: 1 for `_w` variants, 0 otherwise. Parameterized in
  the macro.
* **Shift direction + sign behavior**: lives on the Sail side. The
  32-bit variants compute their 32-bit result and `sign_extend (m :=
  64)` to 64; the 64-bit variants operate directly on 64 bits.
  `Fundamentals/Execution.lean::execute_RTYPEW_pure` and
  `execute_RTYPE_pure` respectively.

## Key Phase 2 finding: the `m32 = 1` bus path works

Before A6 landed, Phase 1.5 Track M generalized `opBus_row_Main` to
carry the PIL-faithful `(1 - m32) *` factors on the `a_hi` / `b_hi`
lanes, but no opcode exercised `m32 = 1`. A6 closes that gap:

* `Spec/Shift.lean::sllw_bus_high_lanes_zero` proves that under
  `m32 = 1` mode witnesses the emitted bus entry's high lanes are 0.
* The proof fires the **new `one_sub_one_mul : (1 - 1) * x = 0`**
  @[simp] lemma (mirror of Phase 1's `one_sub_zero_mul`) after
  `rw [h_m32 : m.m32 row = 1]`.
* Both simp lemmas sit side-by-side in `Airs/OperationBus.lean`.
* No Track M regressions surfaced — ADD and BEQ's `m32 = 0` proofs
  continue to close via `one_sub_zero_mul`.

## Proof structure

### Sail side (`RV64D/sllw.lean`)

Mirrors `RV64D/add.lean` shape one-for-one, switching:
- `execute_RTYPE'` → `execute_RTYPEW'`
- `rop.ADD` → `ropw.SLLW`
- `RTYPE` → `RTYPEW`
- `AddInput` → `SllwInput`

The actual 32-bit-shift-then-sign-extend compute is factored out
into `Fundamentals/Execution.lean::execute_RTYPEW_pure`. The
equivalence lemma (`execute_RTYPEW_eq_execute_RTYPEW'`) closes by
`cases op <;> simp_all` plus one `rfl` for the SRAW case's
`setWidth 32`/`ofNat 32` synonym residual.

### Circuit side (`Spec/Shift.lean`)

* `main_row_in_sllw_mode` — mode witnesses (external op, opcode 36,
  `m32 = 1`, `flag = 0`, `set_pc = 0`).
* `sllw_circuit_holds` — adds the standard boolean / disjointness
  Main constraints plus `matches_entry` between
  `opBus_row_Main m r` and a caller-supplied `bus_entry`.
* `sllw_bus_high_lanes_zero` — `m32 = 1` zeroes the bus's high lanes.
* `sllw_compositional` — composes the above to conclude
  `bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0`.

Like BEQ, we **DEFER** the concrete `BinaryExtension` AIR's bus-
emission derivation. The `matches_entry` hypothesis is a
parameterized trusted boundary for Phase 2; Phase 4 audit wires it
to a concrete `Valid_BinaryExtension` AIR.

### Equivalence (`Equivalence/Shift.lean`)

Three-theorem shape mirrors BEQ:

* `equiv_SLLW` — circuit-level. `m32 = 1` ⇒ bus `a_hi = b_hi = 0`.
* `equiv_SLLW_sail` — Sail-level. Wraps
  `execute_RTYPE_sllw_pure_equiv`.
* `equiv_SLLW_metaplan` — metaplan shape. Composes sail +
  `h_bus_execute_matches_sail`.

## Macro: `ZiskFv.Tactics.ShiftArchetype`

Parametric over `opcode_lit : FGL` and `m32_val : FGL`:

```
theorem shift_archetype_m32_one_zeros_bus :
    shift_archetype_circuit_holds m r_main bus_entry opcode_lit 1
      → bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0

theorem shift_archetype_m32_zero_passthrough_bus :
    shift_archetype_circuit_holds m r_main bus_entry opcode_lit 0
      → bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main
```

Plus tactic convenience wrappers `shift_archetype_m32_one_proof` and
`shift_archetype_m32_zero_proof`.

**Phase 3 fan-out:**

* SRLW, SRAW: invoke `shift_archetype_m32_one_zeros_bus` with
  `opcode_lit := OP_SRL_W` / `OP_SRA_W`. Transpile axioms are
  literal copies of `transpile_SLLW` with the opcode swapped.
* SLL, SRL, SRA: invoke `shift_archetype_m32_zero_passthrough_bus`.
  Transpile axioms set `m32 = 0`.

## A6-B decision log

Same as A1-B (BEQ): **DEFER** PIL-level `BinaryExtension` bus-
emission derivation. The `h_bus_execute_matches_sail` /
`matches_entry` hypotheses stay parameterized at the metaplan-
theorem layer. Phase 4 audit will either derive them from a
concrete `Valid_BinaryExtension` AIR (requires fresh
`zisk-pil-extract` output) or treat them as trusted contract.

## Files added / modified in A6

| File | Status |
|------|--------|
| `Fundamentals/Execution.lean` | `execute_RTYPEW_pure` section added |
| `Fundamentals/Transpiler.lean` | `OP_SLL_W` literal + `transpile_SLLW` axiom |
| `Airs/OperationBus.lean` | `one_sub_one_mul` + `one_sub_m32_mul_of_eq_one` |
| `Spec/Shift.lean` | **new** — compositional SLLW Main-side proof |
| `RV64D/sllw.lean` | closed — zero sorries |
| `Equivalence/Shift.lean` | **new** — three-theorem shape |
| `Tactics/ShiftArchetype.lean` | **new** — parametric macros |
| `GoldenTraces/SLLW.lean` | **new** — two-case fixture |
| `docs/fv/archetype-shift.md` | **new** — this file |
| `justfile` | `verify-phase2` extended with SLLW build target |

## References

- `vendor/zisk/pil/operations.pil:59-64` — opcode literals
- `vendor/zisk/core/src/riscv2zisk_context.rs:153-157` — transpile arms
- `vendor/zisk/core/src/zisk_ops.rs:416-421` — op-type dispatch table
- `vendor/zisk/core/src/zisk_inst_builder.rs:206` — `m32 = optxt.contains("_w")`
- `vendor/zisk/state-machines/main/pil/main.pil:364-369` — PIL
  `assumes_operation` with `(1 - m32) * a[1]`
- `vendor/zisk/state-machines/binary/pil/binary_extension.pil` — the
  `BinaryExtension` SM (not audited in A6; Phase 4 scope)
- `LeanRV64D.InstsEnd.lean:65650-65661` — `execute_RTYPEW` Sail def
