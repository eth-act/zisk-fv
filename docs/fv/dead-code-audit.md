# Dead-code audit

> **Historical snapshot.** This audit records the Step-4 dead-code cleanup
> that reduced the ledger from 147 to 122 axioms. It is intentionally kept
> as the recovery index for that cleanup, not as the current trust count.
> Current source-ledger and global-closure counts live in
> [`trusted-base.md`](trusted-base.md) and
> [`axiom-index.md`](axiom-index.md).

Inventory of constants in the `ZiskFv.*` namespace that are
**unreachable** from the project's public proof surface — the entry
points listed in
[`trust/dead-code-entry-points.txt`](../../trust/dead-code-entry-points.txt).

Reachability is computed by
`bin/TrustGate/ConstantClosure.lean` and exposed via the
`lake exe trust-gate find-unused` subcommand. The detector walks the
**syntactic-const closure** under the elaborated environment: for
each entry point, every `Expr.const` Name appearing in its type or
value is recursively followed. A constant is reported "unreachable"
iff it is not in the resulting closure.

The 127 entry points are:

* `ZiskFv.Compliance.zisk_riscv_compliant_program_bus` — the global compliance theorem dispatching all 63 RV64IM opcodes.
* The 63 canonical `equiv_<OP>` theorems (one per opcode).
* The 63 `equiv_<OP>` Compliance wrappers (consumed directly by the global theorem).

The audit is intentionally **not destructive** — this file *reports*
candidates; a separate follow-up PR is required to delete anything.

## Reproducing

```bash
nix develop --command lake build
# Part A: axioms reachable from the global theorem vs. baseline.
nix develop --command lake exe trust-gate print-axiom-closure \
    ZiskFv.Compliance.zisk_riscv_compliant_program_bus \
    2>/dev/null > /tmp/global-axioms.txt
# (baseline-axioms.txt records the unqualified suffix in column 4.)
awk -F. '{print $NF}' /tmp/global-axioms.txt | sort -u > /tmp/global-shortnames.txt
grep -v '^#' trust/baseline-axioms.txt | awk 'NF>=4 {print $NF}' | sort -u > /tmp/baseline-names.txt
comm -23 /tmp/baseline-names.txt /tmp/global-shortnames.txt  # → 25 names

# Part B: unreachable ZiskFv.* constants.
nix develop --command lake exe trust-gate find-unused trust/dead-code-entry-points.txt \
    > /tmp/unreachable-constants.txt
```

## Methodology — confidence + limits

The closure is **syntactic**, not semantic. False positives may arise
from constants that the elaborator inserts implicitly:

* **Type-class instances** reached only through implicit-argument
  synthesis. An instance Name *is* inserted by the elaborator at use
  sites (so call-site terms reference it), but an instance declared
  but never synthesised at any use site reads as unreachable. This is
  rare in `ZiskFv.*` — most instances live in dependencies (Mathlib /
  std / Lean), and the few project instances (`Field FGL` etc.) are
  used pervasively.
* **Tactic-only definitions** surfaced via `by`-block macro expansion
  where no `Expr.const` reference survives. Specific to:
  `simp` lemmas referenced only by simp set membership; `@[ext]`
  / `@[grind]` discharge lemmas. Most opcode proofs use explicit
  term-mode dispatch, so this is again rare.
* **Compiler-internal auxiliaries** (`*.eq_*`, `_proof_*`,
  `*.brecOn`, `*.mk`, `*.rec`, etc.) are *excluded* from the audit
  set by `isCompilerInternal` since they trivially track their
  parent definition. (They are visible in module counts where they
  appear, but flagged consistently — see e.g.
  `Valid_*.multiplicity_def`.)

**Conservative interpretation**: a name in the report MIGHT be live
via one of the false-positive channels above. Before deleting any
candidate, grep the source tree for explicit references; if grep
finds nothing, deletion is safe.

**Aggressive interpretation**: combined with `grep -rn` showing no
textual references in `ZiskFv/`, the candidate is dead.

Counts in this report are produced by the detector and reproducible
with the commands above.

---

## Part A — 25 unreached axioms

`trust/baseline-axioms.txt` lists 147 axioms. The transitive closure
of `zisk_riscv_compliant_program_bus` reaches **122**. The remaining
**25 are unreached by any proof in the project**.

| # | Axiom | File:Line | Classification |
|--:|-------|-----------|----------------|
| 1 | `transpile_BEQ` | `ZiskFv/Trusted/Transpiler.lean:292` | Genuinely dead — branch-family transpile contract |
| 2 | `transpile_BNE` | `ZiskFv/Trusted/Transpiler.lean:344` | Genuinely dead — branch-family transpile contract |
| 3 | `transpile_BLT` | `ZiskFv/Trusted/Transpiler.lean:924` | Genuinely dead — branch-family transpile contract |
| 4 | `transpile_BGE` | `ZiskFv/Trusted/Transpiler.lean:962` | Genuinely dead — branch-family transpile contract |
| 5 | `transpile_BLTU` | `ZiskFv/Trusted/Transpiler.lean:991` | Genuinely dead — branch-family transpile contract |
| 6 | `transpile_BGEU` | `ZiskFv/Trusted/Transpiler.lean:1020` | Genuinely dead — branch-family transpile contract |
| 7 | `transpile_FENCE` | `ZiskFv/Trusted/Transpiler.lean:420` | Genuinely dead — FENCE transpile contract |
| 8 | `transpile_LB` | `ZiskFv/Trusted/Transpiler.lean:2321` | Genuinely dead — signed load transpile contract |
| 9 | `transpile_LH` | `ZiskFv/Trusted/Transpiler.lean:2292` | Genuinely dead — signed load transpile contract |
| 10 | `transpile_LW` | `ZiskFv/Trusted/Transpiler.lean:2263` | Genuinely dead — signed load transpile contract |
| 11 | `transpile_LD` | `ZiskFv/Trusted/Transpiler.lean:515` | Genuinely dead — 64-bit load transpile contract |
| 12 | `transpile_LBU` | `ZiskFv/Trusted/Transpiler.lean:636` | Genuinely dead — unsigned load transpile contract |
| 13 | `transpile_LHU` | `ZiskFv/Trusted/Transpiler.lean:601` | Genuinely dead — unsigned load transpile contract |
| 14 | `transpile_LWU` | `ZiskFv/Trusted/Transpiler.lean:557` | Genuinely dead — unsigned load transpile contract |
| 15 | `transpile_MULW` | `ZiskFv/Trusted/Transpiler.lean:1538` | Genuinely dead — MULW transpile contract |
| 16 | `op_bus_perm_sound_ArithMul` | `ZiskFv/Airs/OperationBus/Bridge.lean:120` | Genuinely dead — superseded op-bus perm-soundness axiom |
| 17 | `op_bus_perm_sound_ArithMulSecondary` | `ZiskFv/Airs/OperationBus/Bridge.lean:158` | Genuinely dead — superseded op-bus perm-soundness axiom |
| 18 | `op_bus_perm_sound_ArithDiv` | `ZiskFv/Airs/OperationBus/Bridge.lean:181` | Genuinely dead — superseded op-bus perm-soundness axiom |
| 19 | `op_bus_perm_sound_ArithDivSecondary` | `ZiskFv/Airs/OperationBus/Bridge.lean:197` | Genuinely dead — superseded op-bus perm-soundness axiom |
| 20 | `memory_bus_register_write_perm_sound` | `ZiskFv/Airs/MemoryBus/LaneMatch.lean:138` | Genuinely dead — superseded mem-bus perm-soundness axiom |
| 21 | `memory_bus_register_write_perm_sound_store_pc` | `ZiskFv/Airs/MemoryBus/LaneMatch.lean:329` | Genuinely dead — superseded mem-bus perm-soundness axiom |
| 22 | `lookup_consumer_matches_provider_store` | `ZiskFv/Airs/MemoryBus/MemBridge.lean:179` | Genuinely dead — superseded store-side lookup bridge |
| 23 | `row_models_sail_state_store` | `ZiskFv/ZiskCircuit/MemModel.lean:152` | Genuinely dead — superseded mem-state bridge for stores |
| 24 | `arith_table_op_div_rem_signed_w_main_selector_pin` | `ZiskFv/Airs/Arith/Ranges.lean:898` | Genuinely dead — ArithTable W-mode selector pin |
| 25 | `arith_table_op_div_rem_unsigned_w_main_selector_pin` | `ZiskFv/Airs/Arith/Ranges.lean:869` | Genuinely dead — ArithTable W-mode selector pin |

All 25 are confirmed dead. Cross-check: the wrapper theorems that
consume them (`transpile_*_consumer` in
`Fundamentals/TranspileConsumers.lean`,
`arith_{mul,div}_discharge_conservative` in
`Equivalence/Bridge/Arith.lean`, etc.) are themselves in the
unreachable set, so the chain is dead end-to-end — no live theorem
syntactically references the closure terminating at these axioms.

### Why each is dead — quick narrative

* **Branch transpile contracts (BEQ/BNE/BLT/BGE/BLTU/BGEU).** The
  branch `equiv_<OP>` proofs were rewritten to consume a unified
  branch archetype rather than per-opcode transpile contracts; the
  legacy contracts remain in the ledger but no theorem references
  them.
* **FENCE transpile contract.** Same pattern — the FENCE proof
  consumes a more general predicate.
* **Signed/unsigned/D loads transpile contracts (LB/LH/LW/LD/LBU/LHU/LWU).**
  Load proofs were closed via the cross-entry rd-value derivation
  chain (`Circuit/LoadDerivation.lean`,
  `Circuit/SextLoadBridge.lean`, `Airs/MemoryBus/MemAlignBridge.lean`)
  rather than transpile contracts.
* **`transpile_MULW`.** MULW now derives its row shape from the
  ArithMul archetype, not a bespoke transpile axiom.
* **`op_bus_perm_sound_Arith{Mul,Div}{,Secondary}` (4).** Superseded
  by the generic op-bus perm-soundness axiom; the legacy specialised
  forms are unreferenced.
* **`memory_bus_register_write_perm_sound{,_store_pc}` (2),
  `lookup_consumer_matches_provider_store`, `row_models_sail_state_store`.**
  Superseded by the unified memory-bus perm-soundness pipeline that
  the store proofs (SB/SH/SW/SD) actually consume.
* **`arith_table_op_div_rem_{signed,unsigned}_w_main_selector_pin` (2).**
  W-mode ArithTable selector pins replaced by the chain-pin axioms
  the live W-DIV/W-REM proofs consume.

### Suggested cleanup

A follow-up PR can delete the 25 axioms above and regenerate the
baseline. That would reduce the trust-ledger claim from **147 axioms
to 122 axioms** — matching exactly the transitive closure of the
global compliance theorem (`#print axioms` count = 122). The
trust-base.md narrative + `baseline-axioms.txt` regeneration would
need to land in the same commit.

If the consuming wrappers (e.g. `transpile_BEQ_consumer`,
`arith_mul_discharge_conservative`, `lookup_consumer_matches_provider_store`-bridges)
are deleted alongside, several hundred more `ZiskFv.*` constants
become deletion candidates — see Part B.

---

## Part B — Unreachable functions / theorems

The detector reports:

```
# unreachable `ZiskFv.*` constants: 2072
# total auditable `ZiskFv.*` constants: 3381
# entry points: 190
```

i.e. roughly **61 %** of project-namespace constants are
syntactically unreachable from the published proof surface. Note this
includes auto-generated `.eq_N` simp equations for non-recursive
definitions and `Valid_<AIR>.<col>_def` accessor lemmas attached to
unreachable AIR wrappers, so the headline number overstates "human
authored dead code"; see the breakdown below.

### Kind breakdown

| Kind | Count |
|------|------:|
| `theorem` | 1455 |
| `def` | 551 |
| `ctor` | 35 |
| `axiom` | 25 |
| `induct` | 3 |
| `rec` | 2 |
| `opaque` | 1 |
| **Total** | **2072** |

### Top modules by unreachable count

| Module | Count | Notes |
|--------|------:|-------|
| `ZiskFv.Compliance` | 384 | Inferred elaboration auxiliaries of the dispatching theorem; large because the global theorem unfolds 63 arms |
| `ZiskFv.Compliance` | 152 | Auxiliary lemmas attached to the wrapper layer not consumed by the global theorem directly |
| `ZiskFv.Airs.MemAlign` | 129 | MemAlign AIR — large state-machine, many per-column predicates only some of which are consumed |
| `ZiskFv.Airs.Binary.Binary` | 78 | Binary AIR — similar pattern |
| `ZiskFv.Airs.BusShape` | 74 | Bus-shape lemmas — generated en masse, only a slice reached |
| `ZiskFv.Trusted.Transpiler` | 71 | Includes the 15 dead transpile axioms (Part A) + dead `transpile_*` consumers |
| `ZiskFv.Fundamentals.TranspileConsumers` | 66 | Consumer wrappers around the dead transpile axioms (chain-dead with Part A) |
| `ZiskFv.Airs.MemAlignByte` | 62 | MemAlignByte AIR |
| `ZiskFv.Airs.Mem` | 57 | Mem AIR |
| `ZiskFv.Airs.Main` | 53 | Main AIR — many column accessors generated but only a subset used |
| `ZiskFv.Airs.Binary.BinaryExtension` | 43 | BinaryExtension AIR |
| `ZiskFv.Airs.Arith.Mul` | 42 | ArithMul AIR |
| `ZiskFv.Airs.Arith.Div` | 42 | ArithDiv AIR |
| `ZiskFv.Airs.MemAlignReadByte` | 36 | MemAlignReadByte AIR |
| `ZiskFv.Field.GoldilocksPrimality` | 30 | Pratt primality certificate auxiliaries |

The 12 `ZiskFv.Tactics.*Archetype` modules account for ~110
unreachable constants. These are tactic-archetype scaffolding
(`alu_rtype_archetype_*`, `branch_archetype_*`, `jump_archetype_*`,
`load_archetype_*`, etc.) that was authored to support batch
proofs but is not consumed by the canonical opcode equivalences,
which instead inline the relevant template. Several of these
archetypes were likely superseded mid-development and the
predecessors not removed.

### Top 30 highest-confidence "possibly dead" candidates

These are user-authored top-level theorems / defs (not `*.eq_*`
auxiliaries, not constructors, not auto-generated `_def` accessors)
that the detector reports as unreachable. Each survived a quick spot
check for any project-namespace reference; they are high-priority
deletion candidates for follow-up cleanup.

| # | Constant | Category |
|--:|----------|----------|
| 1 | `ZiskFv.Airs.ArithCarryChain.arith_div_signed_carry_identity` | ArithCarryChain — superseded carry-identity lemma |
| 2 | `ZiskFv.Airs.ArithCarryChain.arith_div_unsigned_carry_identity` | ArithCarryChain — superseded carry-identity lemma |
| 3 | `ZiskFv.Airs.ArithCarryChain.arith_div_w_carry_identity` | ArithCarryChain — superseded carry-identity lemma |
| 4 | `ZiskFv.Airs.ArithCarryChain.arith_mul_signed_carry_identity` | ArithCarryChain — superseded carry-identity lemma |
| 5 | `ZiskFv.Airs.ArithCarryChain.arith_mul_unsigned_carry_identity` | ArithCarryChain — superseded carry-identity lemma |
| 6 | `ZiskFv.Airs.ArithCarryChain.arith_mul_w_carry_identity` | ArithCarryChain — superseded carry-identity lemma |
| 7 | `ZiskFv.Airs.ArithDiv.arith_div_signed_packed_correct` | ArithDiv — packed-correctness lemma not consumed |
| 8 | `ZiskFv.Airs.ArithDiv.arith_div_signed_packed_correct_bundled` | ArithDiv — bundled variant not consumed |
| 9 | `ZiskFv.Airs.ArithDiv.arith_div_unsigned_packed_correct` | ArithDiv — packed-correctness lemma not consumed |
| 10 | `ZiskFv.Airs.ArithDiv.arith_div_unsigned_packed_correct_bundled` | ArithDiv — bundled variant not consumed |
| 11 | `ZiskFv.Tactics.ALUITypeArchetype.alu_itype_archetype_c_bus_match` | Tactics archetype — superseded |
| 12 | `ZiskFv.Tactics.ALUITypeArchetype.alu_itype_archetype_circuit_holds` | Tactics archetype — superseded |
| 13 | `ZiskFv.Tactics.ALURTypeArchetype.alu_rtype_archetype_c_bus_match` | Tactics archetype — superseded |
| 14 | `ZiskFv.Tactics.ALURTypeArchetype.alu_rtype_archetype_circuit_holds` | Tactics archetype — superseded |
| 15 | `ZiskFv.Tactics.ALURTypeArchetype.tacticAlu_rtype_archetype_proof` | Tactics archetype — macro never expanded |
| 16 | `ZiskFv.Tactics.ArithSMArchetype.arith_archetype_div_bus_match` | Tactics archetype — superseded |
| 17 | `ZiskFv.Tactics.ArithSMArchetype.arith_archetype_rem_bus_match` | Tactics archetype — superseded |
| 18 | `ZiskFv.Tactics.ArithSMArchetype.div_primary_circuit_holds` | Tactics archetype — superseded |
| 19 | `ZiskFv.Tactics.ArithSMArchetype.rem_secondary_circuit_holds` | Tactics archetype — superseded |
| 20 | `ZiskFv.Tactics.BranchArchetype.branch_archetype_circuit_holds` | Tactics archetype — superseded |
| 21 | `ZiskFv.Tactics.BranchArchetype.branch_archetype_taken` | Tactics archetype — superseded |
| 22 | `ZiskFv.Tactics.BranchArchetype.branch_archetype_not_taken` | Tactics archetype — superseded |
| 23 | `ZiskFv.Tactics.BranchArchetype.branch_archetype_pc_dispatch` | Tactics archetype — superseded |
| 24 | `ZiskFv.Tactics.BranchArchetype.tacticBranch_archetype_proof` | Tactics archetype — macro never expanded |
| 25 | `ZiskFv.Tactics.JumpArchetype.jalr_archetype_pc_advance` | Tactics archetype — superseded |
| 26 | `ZiskFv.Tactics.JumpArchetype.jump_archetype_circuit_holds` | Tactics archetype — superseded |
| 27 | `ZiskFv.Equivalence.Bridge.Arith.arith_mul_discharge_conservative` | Bridge wrapper around dead `op_bus_perm_sound_ArithMul` |
| 28 | `ZiskFv.Equivalence.Bridge.Arith.arith_div_discharge_conservative` | Bridge wrapper around dead `op_bus_perm_sound_ArithDiv` |
| 29 | `ZiskFv.Fundamentals.TranspileConsumers.transpile_BEQ_consumer` | Consumer wrapper around dead `transpile_BEQ` (representative; 14 more in the same module) |
| 30 | `ZiskFv.Compliance.Wrappers.Divw` | Stale Exemplar — superseded by the in-line dispatch arm |

Full list: `/tmp/unreachable-constants.txt` after running
`lake exe trust-gate find-unused trust/dead-code-entry-points.txt`.

### Recommended follow-up sequence

1. **Cleanup PR 1 — dead axioms.** Delete the 25 axioms in Part A;
   regenerate `trust/baseline-axioms.txt`; rewrite the trust-base.md
   headline from "147 axioms" to "122 axioms". Verify
   `lake exe trust-gate check-deps` is still clean.
2. **Cleanup PR 2 — dead transpile-consumer + bridge layer.** Delete
   `Fundamentals/TranspileConsumers.lean` entries that wrap deleted
   axioms; delete `Equivalence/Bridge/Arith.lean::arith_*_discharge_conservative`
   and its sibling files.
3. **Cleanup PR 3 — Tactics archetypes.** Delete unused archetype
   scaffolding under `ZiskFv/Tactics/*Archetype.lean`; some files may
   be deletable in full.
4. **Cleanup PR 4 — AIR `_def` / `*_packed_*` lemmas.** Per-AIR
   sweep: drop unused column-accessor lemmas and `packed_correct*`
   variants. Lowest priority because each deletion is small.

Each PR should rerun `nix run .#test` (full gate) and commit the
`trust/baseline-*.txt` diffs in the same commit as the deletion.

## Cleanup landed

The cleanup landed in commits `607c918` (Batch 1a — 15 transpile
axioms + consumers), `b865710` (Batch 1b — 10 bus/store/ArithTable
axioms + their consumer chains), and `5200d24` (Batch 2+3 —
deleted `Fundamentals/TranspileConsumers.lean` in full plus the
truly textually-dead Tactics archetype scaffolding identified after
cross-checking the detector's reports against `grep -rn`).

Historical final state for this audit: **122 axioms** in
`trust/baseline-axioms.txt`,
matching exactly the transitive closure of
`zisk_riscv_compliant_program_bus`. Several Tactics archetype
constants flagged "unreachable" by the detector turned out to be
false positives — they ARE used through `open Foo + bare
identifier` patterns the const-graph walker does not traverse.
These remain in tree.
