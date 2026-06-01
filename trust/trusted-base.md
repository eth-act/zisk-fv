# Trusted Base

This is the narrative source of truth for zisk-fv's current trust boundary.
The generated machine ledgers live under [`generated/`](generated/).

## Claim

The intended soundness claim is:

> Assuming the Sail-to-Lean extraction and ZisK RV64IM circuit-to-Lean
> extraction are trusted, every state transition accepted by the modeled ZisK
> RV64IM circuits is a valid RISC-V state transition.

The global Lean theorem is:

```text
ZiskFv.Compliance.zisk_riscv_compliant_program_bus
```

Current generated counts:

| Surface | Count | Ledger |
| --- | ---: | --- |
| Source Lean trust declarations | 12 | [`generated/baseline-axioms.txt`](generated/baseline-axioms.txt) |
| Transitive project-axiom closure of `zisk_riscv_compliant_program_bus` | 10 | [`generated/baseline-zisk-riscv-compliant.txt`](generated/baseline-zisk-riscv-compliant.txt) |

The difference is intentional: some checked-in trust declarations are retained
for local components or completeness-direction placeholders but are not reached
by the current global compliance theorem. The semantic trust gate checks the
global closure against the source ledger modulo
[`tolerated-completeness-axioms.txt`](tolerated-completeness-axioms.txt).

The extraction assumptions are part of the project premise but outside the
Lean axiom ledger:

- Sail-to-Lean extraction for the official `riscv/sail-riscv` semantics.
- ZisK RV64IM circuit-to-Lean extraction from flake-pinned ZisK/PIL inputs.

## Current Classes

| Class | Declarations | In global closure | Removability |
| --- | ---: | ---: | --- |
| Transpiler bridge | 1 | 1 | Removable by a verified Lean transpiler or checker that proves the same per-opcode contracts. |
| Memory state load bridge | 1 | 1 | Removable by proving the memory-row model directly from extracted memory AIR facts and Sail memory. |
| Platform scope | 4 | 4 | Scope assumptions for PMP, PMA, CLINT, and Zicfilp under the current RV64IM platform profile. |
| Clean completeness placeholders | 6 | 4 | Completeness-direction placeholders; planned retirement with completeness work. |

## Transpiler Bridge

Declaration:

```text
ZiskFv.Trusted.transpiler_contract_sound
```

This is the remaining aggregate trust bridge between a Main AIR row accepted as
a transpiler-derived row and the per-opcode semantic facts consumed by the
compliance wrappers.

Current evidence is the in-tree Lean static transpiler model plus the Rust
differential harness in `tools/transpiler-diff`. That evidence checks the
static RV64IM fields fixed by instruction bits and `ZiskInstBuilder`: source
selectors, immediate chunks, store selectors and offsets, jump offsets,
`store_pc`, `set_pc`, `ind_width`, `is_external_op`, `m32`, and row count. It
does not prove runtime register contents, memory values, Main witness columns,
Sail state, or ROM/Main/dataflow bridges.

The former JALR/source-C special axioms are retired. The current JALR wrapper
uses the same final-row `PC_for_JALR` link shape as the rest of the transpiler
bridge. The unaligned row-1 ADD to final-row `lastc` relationship remains only
as a pure helper requiring explicit caller facts; it is not in the global
compliance theorem's trust closure.

Retirement path: replace `transpiler_contract_sound` with a Lean
implementation or independently checked certificate path that derives the same
facts without an aggregate axiom.

## Memory State Load Bridge

Declaration:

```text
ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load
```

This bridge says that the memory row selected by the circuit-side memory model
loads the same bytes as the Sail state memory. It is an unproved
model-fidelity boundary, not a known bug.

Retirement path: prove the end-to-end connection from extracted Mem AIR
constraints, memory-bus matching, byte assembly, and Sail memory
representation.

## Platform Scope

Declarations:

```text
ZiskFv.PlatformScope.pmpCheck_is_pure_none
ZiskFv.PlatformScope.pmaCheck_is_pure_none
ZiskFv.PlatformScope.within_clint_is_false
ZiskFv.PlatformScope.update_elp_state_is_pure_unit
```

These fix the verification target to the current platform profile: no active
PMP/PMA failure behavior, no CLINT-mapped access, and inert Zicfilp
landing-pad state update. They are scope assumptions, not ZisK defects.

Retirement path: model the corresponding platform behavior, or prove ordinary
preconditions that exclude those Sail branches.

## Clean Completeness Placeholders

Declarations live under `ZiskFv/AirsClean/Completeness.lean`.

These are completeness-direction placeholders for clean-table components. They
assert that a satisfying clean component witness exists for the relevant row
facts. They do not state per-opcode output equality.

Currently reached by the global compliance closure:

```text
ZiskFv.AirsClean.ArithDiv.arithDiv_circuit_completeness
ZiskFv.AirsClean.ArithMul.arithMul_circuit_completeness
ZiskFv.AirsClean.MemAlignByte.memAlignByte_circuit_completeness
ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByte_circuit_completeness
```

The two remaining clean completeness declarations are source-ledger entries
but are not part of the current global closure:

```text
ZiskFv.AirsClean.BinaryAdd.binaryAdd_circuit_completeness
ZiskFv.AirsClean.Main.mainWithRomAndMemBus_circuit_completeness
```

Retirement path: prove the corresponding clean component constructibility from
extracted constraints and witness definitions.

## ArithTable And DIV/REM Audit Conclusions

The opcode-shaped ArithTable axiom family has been retired from the active
trust shape. `generated/baseline-arith-table-op-axioms.txt` remains as a
guardrail so new `arith_table_op_*` trust facts cannot be added silently.

Active conclusions:

- True finite-table projections are now derived from row-native
  `ArithTableSpec` witnesses rather than trusted as opcode-shaped facts.
- False static claims such as unconditional W-mode `sext = 0` or static
  `np_xor` cannot be reintroduced; they must be replaced by dynamic proofs or
  explicit defect gates.
- `DIVU`, `REMU`, `DIVUW`, and `REMUW` are retired from the broad dynamic
  witness defect by deriving unsigned range, W high-chunk, nonzero-divisor,
  quotient high-zero, and remainder-bound facts from Clean ArithDiv/Binary
  evidence plus the unsigned Euclidean identity.
- Signed `DIV`, `DIVW`, `REM`, and `REMW` remain defect-gated because the
  signed remainder-bound route exposes an `LT_ABS_NP` byte-chain mismatch.
- Signed `MUL`, `MULH`, and `MULHSU` remain defect-gated for signed witness
  soundness under malicious witness construction.

The active defect boundaries and retirement criteria are in
[`defects.md`](defects.md).

## Active Caller Burden

The generated anti-laundering ledgers are:

- [`generated/baseline-hypothesis-count.txt`](generated/baseline-hypothesis-count.txt)
- [`generated/baseline-caller-burden.txt`](generated/baseline-caller-burden.txt)
- [`generated/baseline-wrapper-caller-burden.txt`](generated/baseline-wrapper-caller-burden.txt)
- [`generated/baseline-equiv-axiom-deps.txt`](generated/baseline-equiv-axiom-deps.txt)

Promise discharge must visibly reduce caller burden, unless a documented
structural-unpacking exception explains why added structural witnesses collapse
into shared global-theorem evidence.

## Not In This Ledger

The trust ledger does not enumerate the Lean kernel, mathlib,
LeanZKCircuit, the Sail-to-Lean compiler output, or flake-pinned upstream
inputs. Their audit surface is the Lake/Nix configuration and `flake.lock`,
not `generated/baseline-axioms.txt`.
