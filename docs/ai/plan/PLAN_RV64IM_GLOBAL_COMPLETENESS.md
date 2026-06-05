# RV64IM Global Completeness Plan

## Target

Extend the completed ADD pilot into a global RV64IM completeness result for
the production ZisK-supported instruction surface:

For every raw 32-bit instruction word that the generated Sail model accepts as
a ZisK-supported RV64IM instruction, the Aeneas-extracted production ZisK
decoder/lowering/materialization path accepts it and maps it to a
circuit-covered opcode, except for explicit known ZisK restrictions such as
generic FENCE forms.

This targets the 63 production ZisK RV64IM opcodes extracted through
`zisk/core/src/aeneas_extract.rs`. It does not target every Sail constructor
from unsupported extensions.

The completed ADD pilot is tracked separately in
`docs/plans/rv-add-completeness.md`.

## Execution Strategy

Execute depth-first by instruction family. A family is complete only when its
Sail whitelist/containment, generated Aeneas production coverage, checked-in
global theorem composition, verification commands, progress matrix, `STATUS.md`,
and commit are all done.

Family order:

1. Register ALU: ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND.
2. Register word ALU: ADDW, SUBW, SLLW, SRLW, SRAW.
3. M extension: MUL, MULH, MULHSU, MULHU, MULW, DIV, DIVU, DIVW,
   DIVUW, REM, REMU, REMW, REMUW.
4. Immediate ALU: ADDI, SLLI, SLTI, SLTIU, XORI, SRLI, SRAI, ORI, ANDI.
5. Immediate word ALU: ADDIW, SLLIW, SRLIW, SRAIW.
6. Branches: BEQ, BNE, BLT, BGE, BLTU, BGEU.
7. Loads: LB, LBU, LH, LHU, LW, LWU, LD.
8. Stores: SB, SH, SW, SD.
9. Upper/jump: LUI, AUIPC, JAL, JALR.
10. Fence: supported FENCE forms only; generic FENCE remains a known gap.

Per-family closure loop:

1. Extend `SailRv64imInstruction` with only the current family.
2. For extension-gated families, first use a state-aware SailM return
   predicate under an RV64IM-enabled Sail state assumption.
3. Add family-specific Sail predicates and raw encoding lemmas.
4. Prove the family containment theorem into the existing `Rv64imShapes`
   family shape.
5. Compose the containment into the checked-in supported-decode theorem.
6. Extend generated Aeneas RV completeness coverage only as much as needed for
   the current family.
7. Run verification.
8. Update this plan matrix and `STATUS.md`.
9. Commit the semantic slice.

## Scope

In scope:

- Upper/jump/fence: LUI, AUIPC, JAL, JALR, FENCE.
- Register ALU: ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND.
- Register word ALU: ADDW, SUBW, SLLW, SRLW, SRAW.
- M extension: MUL, MULH, MULHSU, MULHU, MULW, DIV, DIVU, DIVW, DIVUW,
  REM, REMU, REMW, REMUW.
- Immediate ALU: ADDI, SLLI, SLTI, SLTIU, XORI, SRLI, SRAI, ORI, ANDI.
- Immediate word ALU: ADDIW, SLLIW, SRLIW, SRAIW.
- Branches: BEQ, BNE, BLT, BGE, BLTU, BGEU.
- Loads: LB, LBU, LH, LHU, LW, LWU, LD.
- Stores: SB, SH, SW, SD.

Out of scope:

- Sail constructors for extensions ZisK does not implement.
- Pure completeness for known ZisK restrictions. These remain explicit
  `knownGap` cases until production ZisK changes.
- Checking generated Lean or Rust extraction output into the repository.

## Architecture

The proof stays split into three layers:

1. Checked-in Sail-side Lean proves that Sail RV64IM executable raw words land
   in the appropriate raw instruction shape families. For extension-gated Sail
   constructors such as M instructions, the Sail encode/decode relation is
   evaluated under an RV64IM-enabled Sail state rather than treated as an
   unconditional equality to `pure`.
2. Generated Aeneas Lean proves that the extracted production ZisK path covers
   those raw shape families.
3. Checked-in abstract RV completeness theorems compose the Sail containment
   theorem and generated ZisK shape coverage into global completeness avoiding
   known bugs.

The ZisK side must use Aeneas-extracted production functions:

- `extract_decode_rv64im_raw`
- `extract_transpile_rv64im_raw`
- `extract_transpile_rv64im_accepted_raw`
- `extract_transpile_rv64im_materializes_raw`

Do not introduce a second hand-written ZisK decoder.

## Progress Matrix

Use this table as the durable status source. Mark entries complete only after
the corresponding checked-in and generated builds have passed.

| Family | Opcodes | Sail whitelist | Sail raw-shape lemma | Shape in global theorem | Aeneas production coverage | Known-gap status |
| --- | --- | --- | --- | --- | --- | --- |
| Planning trail | n/a | n/a | n/a | n/a | n/a | done |
| ADD pilot | ADD | done | done | done | done | none |
| Register ALU | ADD SUB SLL SLT SLTU XOR SRL SRA OR AND | done | done | done | done | none |
| Register word ALU | ADDW SUBW SLLW SRLW SRAW | done | done | done | done | none |
| Sail relation infrastructure | n/a | done | done | done | n/a | enables extension-gated Sail constructors |
| M extension | MUL MULH MULHSU MULHU MULW DIV DIVU DIVW DIVUW REM REMU REMW REMUW | done | done | done | done | none |
| Immediate ALU | ADDI SLLI SLTI SLTIU XORI SRLI SRAI ORI ANDI | done | done | done | done | none |
| Immediate word ALU | ADDIW SLLIW SRLIW SRAIW | done | done | done | done | none |
| Branches | BEQ BNE BLT BGE BLTU BGEU | done | done | done | done | none |
| Loads | LB LBU LH LHU LW LWU LD | done | done | done | done | none |
| Stores | SB SH SW SD | done | done | done | done | none |
| Upper/jump | LUI AUIPC JAL JALR | done | done | done | done | none |
| Fence | FENCE | done | done | done | done | generic FENCE restrictions |

## Implementation Checklist

- [x] Agree on depth-first family execution order.
- [x] Create normalized project trail files for this worktree.
- [x] Commit the planning/setup slice.
- [x] Preserve the existing ADD theorem as the first closed slice.
- [x] Register ALU: extend Sail whitelist and per-opcode constructor predicates.
- [x] Register ALU: prove Sail encodings imply `RTypeRegisterShape`.
- [x] Register ALU: compose shape into the checked-in supported-decode theorem.
- [x] Register ALU: verify generated Aeneas production coverage for the full
  family.
- [x] Register ALU: run all verification commands, update matrix/status, commit.
- [x] Register word ALU: close whitelist, raw-shape lemma, global theorem shape,
  generated coverage, verification, docs, commit.
- [x] Sail relation infrastructure: add state-aware encode/decode relation and
  compatibility lemmas for already-closed unconditional families.
- [x] M extension: close whitelist, raw-shape lemma, global theorem shape,
  generated coverage, verification, docs, commit.
- [x] Immediate ALU: close whitelist, raw-shape lemma, global theorem shape,
  generated coverage, verification, docs, commit.
- [x] Immediate word ALU: close whitelist, raw-shape lemma, global theorem shape,
  generated coverage, verification, docs, commit.
- [x] Branches: close whitelist, raw-shape lemma, global theorem shape,
  generated coverage, verification, docs, commit.
- [x] Loads: close whitelist, raw-shape lemma, global theorem shape, generated
  coverage, verification, docs, commit.
- [x] Stores: close whitelist, raw-shape lemma, global theorem shape, generated
  coverage, verification, docs, commit.
- [x] Upper/jump: close whitelist, raw-shape lemma, global theorem shape,
  generated coverage, verification, docs, commit.
- [x] Fence: close supported-FENCE theorem surface while keeping generic FENCE
  restrictions as explicit known gaps.
- [x] State the checked-in global theorem in
  `ZiskFv/Completeness/Rv64im.lean`, for example
  `rv64im_global_completeness_avoiding_known_bugs`.
- [x] State the generated production theorem in the generated
  `RvCompleteness.lean` workspace as `rv_completeness_avoiding_known_bugs`.
- [x] Update this matrix after every completed family.

## Verification Commands

Run the checked-in Lean build:

```sh
nix develop . --command lake build ZiskFv.Completeness.SailDecode ZiskFv.Completeness.Rv64im ZiskFv.Completeness.Fence
```

Run the generated Aeneas completeness check:

```sh
AENEAS_CHECK_RV_COMPLETENESS=1 nix run .#aeneas-production-extract
```

When extraction helpers change, run the ZisK extraction sanity test:

```sh
cargo test -p zisk-core raw_rv64im_extraction_uses_general_decoder_gate --features aeneas_extract
```

## Acceptance Criteria

- This file is the source of truth for RV64IM completeness progress.
- `STATUS.md` points to this plan and names the current family/focus.
- The Sail-side RV64IM domain covers all 63 ZisK-supported RV64IM opcodes.
- Every opcode family has checked-in Sail raw-shape containment.
- Every opcode family has generated Aeneas production coverage, or an explicit
  known-gap/blocker entry.
- The final theorem is stated as completeness avoiding known ZisK gaps.
- The checked-in Lake build passes.
- The generated Aeneas completeness check passes.
- No generated code is checked into the repository.
- Commits are normal commits on `rv-completeness`; no amend or force-push.
