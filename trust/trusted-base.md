# Trusted Base

This is the human-readable ledger for zisk-fv's current trust boundary. The
machine ledger is [`baseline-axioms.txt`](baseline-axioms.txt), and the global
compliance closure is
[`baseline-zisk-riscv-compliant.txt`](baseline-zisk-riscv-compliant.txt).

Current counts:

| Surface | Count |
| --- | ---: |
| Source Lean trust declarations | 12 |
| Transitive project-axiom closure of `zisk_riscv_compliant_program_bus` | 9 |

The difference is intentional: some checked-in trust declarations are retained
for local components or completeness-direction placeholders but are not reached
by the current global compliance theorem.

## Current Classes

| Class | Declarations | In global closure | Removability |
| --- | ---: | ---: | --- |
| Transpiler bridge | 1 | 1 | Removable by a verified Lean transpiler or checker that proves the same per-opcode contracts. |
| Memory state load bridge | 1 | 1 | Removable by proving the memory-row model directly from the extracted memory AIR and Sail memory representation. |
| Platform scope | 4 | 4 | Fundamental only for the chosen platform profile; removable by modeling PMP, PMA, CLINT, and Zicfilp instead of fixing them inert. |
| Clean completeness placeholders | 6 | 3 | Removable by proving completeness for the corresponding clean-table components. |

## Transpiler Bridge

Declaration:

```text
ZiskFv.Trusted.transpiler_contract_sound
```

This is the remaining aggregate trust bridge between a Main AIR row accepted as
a transpiler-derived row and the per-opcode semantic facts consumed by the
compliance wrappers.

Evidence today is not the upstream Rust transpiler itself being verified in
Lean. The evidence is the in-tree Lean model, the differential harness, and the
pinning/audit process documented in
[`transpiler-differential-pinning.md`](transpiler-differential-pinning.md).

This is a possible-bug surface: if the Lean model, differential harness, or
pinning contract diverges from the actual upstream transpiler, the bridge can
hide that divergence. It is not fundamental. The intended replacement is a
Lean implementation or independently checked certificate path that derives the
same facts without an aggregate axiom.

The former JALR/source-C special axioms are retired. The current JALR wrapper
uses the same final-row `PC_for_JALR` link shape as the rest of the
transpiler bridge; the unaligned two-row source-C chain is not part of the
global theorem's trusted closure.

## Memory State Load Bridge

Declaration:

```text
ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load
```

This bridge says that the memory row selected by the circuit-side memory model
loads the same bytes as the Sail state memory. It is evidence of an unproved
model-fidelity boundary, not a known bug.

It is removable, but not by local simplification: the proof needs to connect
the extracted memory AIR, memory bus matching, byte assembly, and Sail memory
representation end to end.

## Platform Scope

Declarations:

```text
ZiskFv.PlatformScope.pmpCheck_is_pure_none
ZiskFv.PlatformScope.pmaCheck_is_pure_none
ZiskFv.PlatformScope.within_clint_is_false
ZiskFv.PlatformScope.update_elp_state_is_pure_unit
```

These axioms fix the verification target to the platform profile currently in
scope: no active PMP/PMA failure behavior, no CLINT-mapped access, and inert
Zicfilp landing-pad state update.

They are not evidence of a ZisK bug. They are explicit scoping assumptions.
They are fundamental only while the project remains restricted to this profile;
they can be removed by proving the corresponding platform behavior or by
excluding those Sail branches with ordinary proved preconditions.

## Clean Completeness Placeholders

Declarations live under `ZiskFv/AirsClean/Completeness.lean`.

These axioms are completeness-direction placeholders for clean-table
components. They assert that a satisfying clean component witness exists for
the relevant row facts. They do not state per-opcode output equality.

Three are currently reached by the global compliance closure:

```text
ZiskFv.AirsClean.ArithMul.arithMul_circuit_completeness
ZiskFv.AirsClean.MemAlignByte.memAlignByte_circuit_completeness
ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByte_circuit_completeness
```

The remaining clean completeness declarations are source-ledger entries but
are not part of the current global closure.

These are removable by proving the corresponding clean component
constructibility from the extracted constraints and witness definitions.

## Not In This Ledger

The trust ledger does not enumerate the Lean kernel, mathlib,
LeanZKCircuit, the Sail-to-Lean compiler output, or the flake-pinned upstream
inputs. Those are external build and proof dependencies. Their audit surface is
the Lake/Nix configuration and `flake.lock`, not `baseline-axioms.txt`.
