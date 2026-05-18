# Simplification suggestions

Ranked by leverage. Top of the list = touches many files, biggest readability gain.

## Shipped

- #1 — Collapse `dispatch_X` layer (PR #33, −2890 lines).
- #2 — Thread per-shape `Promises` bundles through wrappers + `OpEnvelope` (PR #34, −2971 lines).
- #2b — Bundle every remaining loose recurring binder cluster: `BusRows`, `MainRowPins`, `ModeRegsFull`, `MemAlignWitness`, `BranchInstrOperands`, `BinaryAddWitness`, `ByteBounds` (PR #35; **all 63 opcodes**; canonical caller-burden −299, wrapper caller-burden −309).
- #6 — Hoist within-shape wrapper-body repetition into per-AIR helper modules (`BinaryHelpers`, `BinaryExtensionHelpers`, `ArithHelpers`). 32 wrappers across 3 AIR families shrink by **−2,393 lines**; new helper modules add **+1,405 lines**; net **−988 source lines** plus a clean reusable layer under `Equivalence/Promises/`. BinaryAdd and Mem audited but skipped (no leverage — Mem is pre-discharged at the canonical layer; BinaryAdd's two wrappers are structurally divergent). Trust gate baselines all unchanged.

## Top-leverage wins

### 1. Collapse the three-layer per-opcode stack

Every opcode currently has:

- `equiv_X` in `Equivalence/X.lean` — the real proof.
- `equiv_X_from_trust` in `Compliance/FromTrust/X.lean` — caller-burden reducer.
- `dispatch_X` in `Compliance/Dispatch.lean` — pure pass-through, often 40 lines forwarding 30 parameters.

`dispatch_X` is essentially `equiv_X_from_trust` with a different name. The dispatch layer provides zero abstraction — `dispatch_ADD`'s body is literally `equiv_ADD_from_trust state add_input r1 r2 rd m b r_main …`.

**Suggestion:** delete `dispatch_X` and have `zisk_riscv_compliant_program_bus` call `equiv_X_from_trust` directly. Saves ~2,500 lines in `Dispatch.lean` plus ~700 of `simp only [exec_eq]; exact dispatch_X …` in `Compliance.lean`. `FromTrust/` could then be renamed to `Wrappers/` or folded back next to `equiv_X`.

### 2. Push the `*Promises` struct through `_from_trust` and `OpEnvelope`

You already have `Equivalence/Promises/{RType,IType,Branch,…}.lean` bundling the ~15 recurring structural hypotheses. But the bundle is only used inside `equiv_X` — `equiv_X_from_trust` and `OpEnvelope` re-explode all 15 binders inline.

Threading `(promises : RTypePromises …)` through both layers would shrink `OpEnvelope` (3,181 lines) and each wrapper by ~12 lines per arm, and unify hypothesis names across opcodes automatically.

**Caveat:** this changes the caller-burden ledger and the hypothesis-count baseline. Treat it as a structural-unpacking-in-reverse refactor; refresh both baselines in the same PR.

### 3. Generate the `OpEnvelope` + `exec_eq` + final cases mechanically — *likely deprecated*

All 63 arms of `OpEnvelope` / `exec_eq` / the final `zisk_riscv_compliant_program_bus` are dictated by the `equiv_X_from_trust` signature. The all-six-branches block is the clearest case: `.beq` / `.bne` / `.blt` / `.bge` / `.bltu` / `.bgeu` differ only in the input record name and one `bop.X` constructor.

Two options:

- **Lower-friction:** introduce per-shape envelopes (`BranchEnvelope`, `RTypeBinaryEnvelope`, `RTypeBinaryWEnvelope`, …) parameterized by the opcode-specific `Input` type and `instruction` constructor. `OpEnvelope` collects ~12 shape envelopes instead of 63 opcodes. Branches collapse 6→1.
- **Higher-friction:** Lean macro generating arms from a table of `(opcode, input_type, instruction_ctor, shape)`. Eliminates duplication entirely but adds elaboration weight; do this only if per-shape grouping doesn't get you there.

**Status (post-bundling PR):** *likely deprecated*. Once the bundling pass lands, each per-opcode arm is small enough (~3-5 binders + 1 promises bundle) that the per-opcode match is intuitive and readable. The 6 branches still look near-identical, but the duplication is ~3 lines per arm — below the threshold where metaprogramming or type restructuring pays for itself. Revisit only if a new family of opcodes introduces another wave of duplication.

## Naming and structural cleanups

### 4a. Drop `_from_trust` suffix from wrappers + move `Compliance/FromTrust/` → `Compliance/Wrappers/`

Carved out of the suggestion-#1 follow-up: the per-opcode wrappers under `ZiskFv/Compliance/FromTrust/<Op>.lean` are named `equiv_<OP>_from_trust`. The "from_trust" half is authoring-history vocabulary — every wrapper IS "from trust" by definition. Drop the suffix to `equiv_<OP>` (disambiguated from the canonical `equiv_<OP>` by the `ZiskFv.Compliance` vs `ZiskFv.Equivalence` namespaces) and rename the directory to `Compliance/Wrappers/` to match.

Surface:
- 63 wrapper files: rename `equiv_<OP>_from_trust` → `equiv_<OP>` (in `ZiskFv.Compliance` namespace).
- 63 imports in `Compliance.lean` (`Compliance.FromTrust.<Op>` → `Compliance.Wrappers.<Op>`).
- 63 call expressions in `zisk_riscv_compliant_program_bus`.
- ~19 doc references in CLAUDE.md, README, `docs/fv/*`.
- Baseline refresh: `baseline-wrapper-caller-burden.txt` (every row's theorem name changes).

Cost: ~10-minute bulk find/replace. Sequenced AFTER the bundling pass so the wrapper-baseline only refreshes once each.

### 4. Unify file naming under RISC-V mnemonics

`Equivalence/` is half-RISC-V (`Lb`, `Lh`, `Sb`, `Sd`) and half-English (`LoadBU`, `LoadD`, `BranchEqual`, `StoreB`, `Shift*`). `Compliance/FromTrust/` is already consistent (RISC-V mnemonics).

Rename:

- `Equivalence/BranchEqual.lean` → `Beq.lean`
- `Equivalence/BranchGreaterEqual.lean` → `Bge.lean`
- `Equivalence/BranchGreaterEqualUnsigned.lean` → `Bgeu.lean`
- `Equivalence/BranchLessThan.lean` → `Blt.lean`
- `Equivalence/BranchLessThanUnsigned.lean` → `Bltu.lean`
- `Equivalence/BranchNotEqual.lean` → `Bne.lean`
- `Equivalence/LoadBU.lean` → `Lbu.lean`
- `Equivalence/LoadD.lean` → `Ld.lean`
- `Equivalence/LoadHU.lean` → `Lhu.lean`
- `Equivalence/LoadWU.lean` → `Lwu.lean`
- `Equivalence/StoreB.lean` → `Sb.lean`
- `Equivalence/StoreD.lean` → `Sd.lean`
- `Equivalence/StoreH.lean` → `Sh.lean`
- `Equivalence/StoreW.lean` → `Sw.lean`
- `Equivalence/Shift*.lean` → match RISC-V mnemonics (Sllw / Srlw / Sraw / Slliw / Srliw / Sraiw)

### 5. Strip development-phase vocabulary

Stale or no longer accurate:

- "Pilot wrapper for `equiv_X`" → "Trust-discharged wrapper for `equiv_X`" (or nothing — the file name is the docstring).
- "ADD is the canonical exemplar for the BinaryAdd shape" — authoring history. `Compliance/FromTrust/Add.lean` has ~140 lines of pre-theorem docstring; almost all of it is "why we wrote this opcode first." Move to a CHANGELOG or delete.
- `Compliance.lean:4` "Phase 3 architectural validation" — it's just `Compliance.lean` now.
- `Equivalence/Remuw.lean:28` "Phase 4.alpha.B.uw2: Structural-unpacking refactor…" and a half-dozen siblings. Once the refactor is in, the "why" lives in the commit.
- `OpEnvelope`'s `.and_op` / `.or_op` / `.xor_op` (presumably dodging a name clash) but plain `.add` / `.sub` elsewhere — pick one: either all `_op` suffixed or none. Mixed is the worst.

### 6. Hoist the within-shape repetition inside the wrappers

In `Compliance/FromTrust/Sub.lean` and every Binary-shape sibling:

- The 29-way `m.op r_main = 0x02 ∨ …` disjunction (`Sub.lean:80-89`, ≥10 copies across the tree) belongs in `Airs/OperationBus` as `op_in_Binary_table_of_op_eq`.
- The 8-fold `(v.free_in_c_i r_binary).val < 256` extraction (`Sub.lean:192-223`, repeated 11×) → one helper `binary_consumer_byte_ranges v r_binary` returning the 8-tuple.
- The 8-fold `consumer_byte_match_chain` constructor block (`Sub.lean:151-190`, repeated 11×) → one helper `binary_consumer_chains_of_axiom v r_binary op h_emit_op h_branch`.

These three changes alone shrink the median Binary-shape wrapper from ~290 lines to ~80.

## Architectural critique: what helpers reveal

The helper modules shipped in PR #36 (`BinaryHelpers`, `BinaryExtensionHelpers`, `ArithHelpers`) are a code smell that points at deeper API misfits. The helpers exist because four design boundaries don't line up with caller needs:

1. **Axiom APIs are too wide for their callers.** `op_bus_perm_sound_Binary` takes a 29-way disjunction; every caller already knows their opcode is in the set and just packages singleton-to-membership ceremony. `binary_consumer_byte_match_chain_pin` returns a 29-line tuple; every caller destructures the same way. The axioms were designed to state the most general theorem; callers always want the narrow specialization.

2. **Per-opcode wrappers duplicate shape-level work.** The 14 Binary wrappers' bodies are ~80% identical (varying only by `OP_<X>` constant and one branch witness). Helpers minimize but don't eliminate the duplication. The natural abstraction is one wrapper per **shape** parameterized on opcode, not one per opcode.

3. **Canonical premises are too granular.** `equiv_SUB` takes ~30 binders. The wrapper layer was invented to reduce caller burden by packaging premises — bundling PRs (#34, #35) and the helper PR (#36) are all symptoms of "the canonical surface was designed for proof-internal clarity, not caller ergonomics."

4. **No dispatch mechanism for per-AIR per-opcode parameterization.** A typeclass `[BinaryAirOp op]` providing per-opcode constants (`op_canon`, `byte_chain_branch`, etc.) could turn 14 wrappers into 1 generic theorem instantiated 14 times. Helpers manually inline this dispatch.

### Hierarchy of fixes, smallest blast radius first

| Fix | What it eliminates | Cost |
|---|---|---|
| Rename `*Helpers.lean` → `*FromTrust.lean` | The smelly name | Mechanical |
| Tighten axiom return types (structured records instead of nested tuples) | ~30% of helpers | Touches `Airs/<AIR>/` axioms, CODEOWNER review |
| Tighten axiom input types (singleton + membership instead of N-way disjunction) | Another ~20% of helpers | Same axiom-layer changes, CODEOWNER review |
| Reshape canonical premises into bundles consumed inside the canonical | The wrapper layer's *raison d'être* | Big — every canonical theorem touched |
| **Per-shape wrappers** (collapse 63 wrappers → ~6 per AIR family) | Per-opcode wrapper files entirely | Type-level restructuring across `Compliance/FromTrust/`; this is the "lower-friction" half of #3 |

Helpers were the cheapest local fix that didn't require touching axioms or canonicals. The smell is real and points at #2 and #5 as the *actually* right answer. The reason we shipped helpers instead is that the bigger fixes touch the trust-protected surface (axioms) or invert the API of every canonical theorem.

### Suggestion 7: collapse per-opcode wrappers into per-shape wrappers

Promoted from suggestion #3's "lower-friction" option. Replace the 63 `equiv_<OP>_from_trust` wrappers with ~6 per-shape wrappers (`equiv_binary_from_trust`, `equiv_binary_extension_from_trust`, `equiv_arith_mul_from_trust`, etc.). Each takes an opcode parameter (or typeclass instance) and discharges the shape's AIR plumbing once. The helper modules become the body of the per-shape wrapper.

This is the natural endpoint of the bundling + hoisting sequence. The wrappers we just refactored ARE the call sites the helpers exist for; collapsing them removes the redundancy structurally rather than papering over it with helpers.

Estimated impact: removes ~50 wrapper files; collapses `Compliance/FromTrust/` to ~6 files totaling ~1500 lines. The dispatch theorem `zisk_riscv_compliant_program_bus` changes from a 63-arm match to a per-shape dispatch (~6-12 arms calling each shape's wrapper). Trust-gate impact: changes the wrapper caller-burden ledger entirely (every row goes away or merges).

### Suggestion 8: tighten trust-ledger axiom APIs

Make axioms return what callers need, not what's most-general-to-state. Concretely:
- `op_bus_perm_sound_<AIR>` accept singleton `(op : FGL) + membership : op ∈ binary_op_set` instead of 29-way disjunction.
- `<AIR>_consumer_byte_match_chain_pin` return a structured record (`ChainPinResult` etc.) instead of a 29-line tuple.
- `matches_entry` come with the projection lemmas baked in (or use a structured return type from the start).

This is CODEOWNER-protected work since it touches `Airs/<AIR>/Bridge.lean` axiom signatures. Risk: must verify that the new axiom shape is logically equivalent to the old one (a soundness audit), and `baseline-axioms.txt` source-hashes change for every axiom touched.

## Caveats on the trust gate

The hypothesis-count baseline (`trust/baseline-hypothesis-count.txt`) and caller-burden ledger (`trust/baseline-caller-burden.txt`) lock in per-opcode binder counts. Suggestions 1, 2, and 3 all change those counts; each is a baseline-refresh PR. Suggestion 2 in particular shrinks the number of binders but consolidates them into a struct — that's the structural-unpacking-in-reverse case the gate is built to scrutinize. Mention it explicitly in the PR body.

## Recommended starting point

**#1 (collapse dispatch layer).** Purely mechanical, no trust-gate baselines move, biggest line-count win, and it makes the subsequent refactors much easier to land.
