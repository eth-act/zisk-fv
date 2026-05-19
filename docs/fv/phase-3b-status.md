# Phase 3b — per-AIR Clean Component status

## What's done

Row types (ProvableStruct) for all 9 AIRs:

| AIR | File | Structure |
|---|---|---|
| BinaryAdd | `ZiskFv/AirsClean/BinaryAdd/Row.lean` | Flat, 10 cols |
| MemAlignReadByte | `ZiskFv/AirsClean/MemAlignReadByte/Row.lean` | Flat, 10 cols |
| MemAlignByte | `ZiskFv/AirsClean/MemAlignByte/Row.lean` | Flat, 16 cols |
| MemAlign | `ZiskFv/AirsClean/MemAlign/Row.lean` | Flat, 19 cols |
| Mem | `ZiskFv/AirsClean/Mem/Row.lean` | Flat, 13 cols |
| ArithMul | `ZiskFv/AirsClean/ArithMul/Row.lean` | Nested: chunks + flags |
| ArithDiv | `ZiskFv/AirsClean/ArithDiv/Row.lean` | Nested: chunks + flags |
| BinaryExtension | `ZiskFv/AirsClean/BinaryExtension/Row.lean` | Nested: aCols + cColsLo + cColsHi + flags |
| Binary | `ZiskFv/AirsClean/Binary/Row.lean` | Nested: aBytes + bBytes + cBytes + chain + mode |

## What's done in full (template AIR)

BinaryAdd has the complete Clean Component port:
- `Row.lean` — ProvableStruct
- `Spec.lean` — Assumptions + Spec
- `Constraints.lean` — circuit `main` with assertZero per constraint
- `Soundness.lean` — full carry-chain proof, FGL-adapted (~210 lines)
- `Bridge.lean` — `Valid_BinaryAdd ↔ BinaryAddRow` compatibility

## What's NOT done (8 AIRs × 4 files each = 32 files of focused proof work)

Each remaining AIR needs:
- **`Spec.lean`** (~80 LoC) — Assumptions + Spec definitions
- **`Constraints.lean`** (~50 LoC) — the AIR's constraint emissions as a `Circuit FGL Unit`
- **`Soundness.lean`** (~250 LoC) — the actual `constraints → Spec` proof, FGL-adapted from the spike pattern
- **`Bridge.lean`** (~80 LoC) — compatibility lemma connecting to existing `Valid_<AIR>`

Aggregate remaining: ~3700 LoC of focused proof work across the 8 AIRs.

## Why this is a separate session

Per AIR, the Soundness proof is the bulk of the work:
- Each AIR has 4-12 row constraints
- Each constraint becomes a Nat-level equation via the Fin-definitional reduction pattern
  (`(a + b).val = (a.val + b.val) % n` is `rfl`; combined with `Nat.mod_eq_of_lt`)
- Carry/chain reasoning needs `linear_combination` + `omega`
- BinaryAdd Soundness was ~210 LoC and required iterative debugging

Doing 8 such proofs in one session is unrealistic. The Row-type scaffolding lets each
follow-up PR focus exclusively on one AIR's Soundness without re-doing the structural work.

## Why Phase 3b matters

Phase 3b is the prerequisite for Phase 6's LeanZKCircuit removal — once every AIR has
a Clean Component, the existing `Valid_<AIR>` records (over LeanZKCircuit.OpenVM.Circuit)
can be retired in favor of the Clean Component's `Soundness.Output` predicate. Then
the `lakefile.toml` Clean-only require can replace the LeanZKCircuit require.

Until Phase 3b is done end-to-end for all 9 AIRs, Phase 6's full cutover is gated.

## Per-AIR Soundness scope (effort estimate)

| AIR | Constraint count | Spec complexity | Est. Soundness LoC |
|---|---|---|---|
| Mem | 6 booleans + memory consistency | High | ~300 |
| MemAlignReadByte | 4 (3 bool + composed) | Medium | ~200 |
| MemAlignByte | 6 (booleans + composed+writeback) | Medium-high | ~250 |
| MemAlign | ~10 (alignment + register chain) | High | ~400 |
| ArithMul | 6 (carry chain × 4 + 2 booleans) | High | ~350 |
| ArithDiv | 6 (carry chain × 4 + 2 booleans) | High | ~350 |
| BinaryExtension | ~8 (op_is_shift + chain) | High | ~300 |
| Binary | ~12 (mode bits + per-byte chain) | Very high | ~500 |
| **Total** | | | **~2650** |

(Excludes the ~200 LoC of Spec definitions per AIR.)

## Path forward

Each follow-up PR: one AIR. Order recommended by ascending difficulty:

1. MemAlignReadByte (simplest Spec, 4 constraints)
2. MemAlignByte
3. ArithMul (carry chain — same pattern as BinaryAdd)
4. ArithDiv
5. BinaryExtension
6. MemAlign
7. Mem (memory consistency Spec is subtle)
8. Binary (most complex — chain + mode + table lookup)

Each PR delivers one AIR's full Clean Component and updates this status file.
