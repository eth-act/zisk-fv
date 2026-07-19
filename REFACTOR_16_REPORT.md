# Refactor 16 report

## Item 1 — shape inventory and factoring map (committed before migration)

The authoritative archive contains 22 requested opcode modules. The measured starting inventory is below (physical lines; `—` means no per-opcode wrapper exists).

| class | opcode | `EquivCore` | `Wrappers` | genuinely per-opcode data |
|---|---:|---:|---:|---|
| logic | AND | 162 | 70 | `OP_AND`, `rop.AND`, `PureSpec.AndInput`/execute/equivalence theorem, AND static-table branch and result lemma |
| logic | ANDI | 167 | 139 | `OP_AND`, `iop.ANDI`, immediate input/spec, I-type promises/archetype, AND result lemma |
| logic | OR | 155 | 172 | `OP_OR`, `rop.OR`, OR input/spec, OR static-table branch and result lemma |
| logic | ORI | 163 | 81 | `OP_OR`, `iop.ORI`, immediate input/spec, OR result lemma |
| logic | XOR | 155 | 70 | `OP_XOR`, `rop.XOR`, XOR input/spec, XOR static-table branch and result lemma |
| logic | XORI | 163 | 81 | `OP_XOR`, `iop.XORI`, immediate input/spec, XOR result lemma |
| compare | SLT | 303 | 83 | `OP_SLT`, `rop.SLT`, signed mode, sign/carry witness pins, SLT Sail spec/result lemma |
| compare | SLTU | 317 | 83 | `OP_SLTU`, `rop.SLTU`, unsigned mode, carry witness pins, SLTU Sail spec/result lemma |
| compare | SLTI | 324 | 124 | `OP_SLT`, `iop.SLTI`, immediate reconstruction, signed mode/pins, SLTI Sail spec/result lemma |
| compare | SLTIU | 336 | 124 | `OP_SLTU`, `iop.SLTIU`, immediate reconstruction, unsigned mode/pins, SLTIU Sail spec/result lemma |
| shift | SLL | 263 | 133 | `OP_SLL`, `rop.SLL`, left mode, RV64 width pins, shift Sail spec/result lemma |
| shift | SLLI | 257 | 82 | `OP_SLL`, `iop.SLLI`, immediate shift amount, left/RV64 pins |
| shift | SLLW | 296 | — | `OP_SLL`, `rop.SLLW`, left/RV32 mode and sign-extension pins |
| shift | SLLIW | 296 | — | `OP_SLL`, `iop.SLLIW`, immediate amount, left/RV32/sign-extension pins |
| shift | SRL | 242 | 79 | `OP_SHR`, `rop.SRL`, logical-right/RV64 pins |
| shift | SRLI | 240 | 75 | `OP_SHR`, `iop.SRLI`, immediate amount, logical-right/RV64 pins |
| shift | SRLW | 285 | — | `OP_SHR`, `rop.SRLW`, logical-right/RV32 pins |
| shift | SRLIW | 275 | — | `OP_SHR`, `iop.SRLIW`, immediate amount, logical-right/RV32 pins |
| shift | SRA | 252 | 79 | `OP_SHR`, `rop.SRA`, arithmetic-right/RV64/sign pins |
| shift | SRAI | 250 | 75 | `OP_SHR`, `iop.SRAI`, immediate amount, arithmetic-right/RV64/sign pins |
| shift | SRAW | 285 | — | `OP_SHR`, `rop.SRAW`, arithmetic-right/RV32/sign pins |
| shift | SRAIW | 275 | — | `OP_SHR`, `iop.SRAIW`, immediate amount, arithmetic-right/RV32/sign pins |

Starting totals: logic 965 core + 613 wrapper = 1,578 lines; compare 1,280 + 414 = 1,694; shift 3,216 + 523 = 3,739; all classes 5,461 + 1,550 = **7,011 lines** in the named towers.

### Shared proof shape

* R-type logic shares `ALURTypeArchetype`, `RTypePromises`, static Binary provider extraction, operation-bus match/opcode pin derivation, eight output-byte range facts, packed c-lane/register-write matching, `BinaryLogic`, Sail-to-pure rewrite, and `bus_effect_matches_sail_alu_rrw`.
* I-type logic has the same static Binary/result spine, with `ALUITypeArchetype`, I-type promises, and immediate reconstruction replacing the second register read.
* Compare shares Binary provider extraction, subtraction/carry chain, c-lane match, and `BinaryCompare`; its real axes are R/I and signed/unsigned.
* Shift shares BinaryExtension provider extraction, shift byte chain, c-lane match, and `BinaryShift`; its real axes are R/I, left/logical-right/arithmetic-right, and 64/32-bit result mode. Existing `ShiftArchetype` and `RTypeWArchetype` already name the recurring consumer shapes.
* Every wrapper repeats the same balance-table witness unpacking and conversion of component/table membership into row spec plus derived row facts. Only the evidence type, opcode pin, operand bridge, and selected core instance differ.

### Initial reference inventory

Repository textual references to each old namespace pair (`EquivCore.<Op>` or `Wrappers.<Op>`) before migration were: AND 19, ANDI 9, OR 18, ORI 9, XOR 18, XORI 9; SLT 32, SLTU 8, SLTI 16, SLTIU 8; SLL 23, SLLI 11, SLLW 4, SLLIW 4, SRL 22, SRLI 11, SRLW 4, SRLIW 4, SRA 22, SRAI 11, SRAW 4, SRAIW 4.

## Items 2–5

Pending migration and verification.

## Item 2 — parametric core: partial, with verified blocker

Added `Compliance/ParametricStaticBinary.lean`, with two proved provider-elimination theorems. `dischargeRType` abstracts the complete repeated Clean static-Binary R-type witness projection (balance component, table membership, `Spec`, `core_every_row`, static spec/WF facts, input lane equalities, output lane match); `discharge` is the corresponding generic provider projection.

The R-type logic wrappers AND/OR/XOR now consume `dischargeRType`, and all three modules build. This removes 10 repeated proof lines from each wrapper, but does **not** yet abstract the opcode-dependent Sail statement/core, so it is not the requested complete class collapse.

A direct migration of ANDI/ORI/XORI to generic `discharge` was tested. Each declaration timed out during elaboration at 1,200,000 heartbeats (`Wrappers/Andi.lean:93`, `Ori.lean:35`, `Xori.lean:35`), although the generic theorem itself compiles. Those experimental edits were reverted. More importantly, the class-level exact-conclusion theorem remains blocked on a dependent packaging boundary: the six logic conclusions use distinct generated input structures, generated execute functions, and instruction constructors. The current `BinaryLogic` consolidation abstracts only the write-value proof; it does not expose a record/interface relating each generated Sail input and pure executor to the instruction and bus-effect normal form. That interface must be introduced before one theorem can retain each exact public conclusion without duplicating the generated-type proof.

Compare and shift were inventoried but not migrated. Their corresponding missing dependent interfaces have additional signed/carry and width/sign-extension pins respectively. No unverified declaration was added.

## Item 3 — instance tables: blocked

No instance tables were added. They depend on the missing class-level dependent interfaces described under item 2. Existing public `Equivalence/<Op>.lean` files and theorem statements remain byte-identical.

## Item 4 — deletion: blocked

No per-opcode file reached reference count zero, so no `EquivCore` or wrapper file was deleted. Reference counts for all old namespace pairs therefore remain the item-1 counts. Root imports were not changed.

## Item 5 — final sweep

Excluding this report and `ARISTOTLE_SUMMARY.md`, the retained proof-code delta against the installed authoritative state is **+97 / −48, net +49 lines**. The three migrated wrappers account for +18/−48; the shared proved module adds 79 lines. This does not meet the ≥5,000 net-deletion GO threshold. Deleted-file list: none.

Verification:

* `lake build ZiskFv`: passed (9,016 jobs), after two command-window cutoffs were resumed.
* Standard trust checks: checks 1–12 and 14–16 passed; check 13 alone failed exactly because `zisk/core/src/aeneas_extract.rs` is absent, the authorized missing-submodule deferral.
* `trust/scripts/check-all-semantic.sh`: all 16 checks passed.
* Zero-sorry gate passed; the new module and changed wrappers contain no `sorry`/`admit`.
* `root_soundness`, `root_completeness`, all `Equivalence/<Op>.lean` files, `ZiskFv/Audit.lean`, `Compliance/Defects.lean`, build pins/lockfiles, and `trust/generated/` were untouched.

## Work-order status

1. Shape inventory map: complete.
2. Parametric core per class: partial R-type provider elimination only; exact blocker above.
3. Instance table per class: blocked by item 2.
4. Per-opcode deletion: blocked because references remain.
5. Sweep and gates: complete; deletion target not met.
