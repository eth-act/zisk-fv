# Plan — V2 trust-gate hardening (type-walk + per-theorem axiom-closure baseline)

## Context

The V1 trust gate (production today) enforces six checks:

1. **Locality** — trust-leak constructs only in allowlisted files.
2. **Baseline freshness** — source-text-hash diff for every axiom.
3. **Forbidden OUTPUT-EQ parameters** — regex over canonical-theorem parameter substrings.
4. **Floors** — minimum axiom count + canonical theorem count.
5. **Zero sorry** under `Fundamentals/Airs/Circuit/Equivalence/Tactics/Sail`.
6. **Uniformity** — every RV64IM opcode has its canonical `equiv_<OP>`.

Two known gaps:

- **Renamed / aliased OUTPUT-EQ hypotheses** slip past V1. A canonical theorem that takes `(h_secret : sail_rd_val = U64.toBV [e2.x0..])` is V1-clean even though the *type* is OUTPUT-EQ-shaped. Likewise `abbrev SilentSpec := PureSpec.execute_LBU_pure ; (h : (SilentSpec ld).rd = ...)` aliases the Sail entry point past the regex.

- **Per-theorem axiom dependencies are invisible.** `trust/baseline-axioms.txt` records that 84 axioms exist; it does not record which axioms each canonical `equiv_<OP>` transitively consumes. Theorems can silently grow trust dependencies (e.g. an Equivalence proof routing through a helper that newly pulls in `memalign_load_high_bytes_zero`) without any gate signal.

V2 closes both via a Lean meta-program shipped as a Lake exe.

## Design

A new `lake exe trust-gate` runs *after* `lake build` (consumes `.olean`s, no full rebuild). Two outputs:

1. **`trust/baseline-equiv-axiom-deps.txt`** — one sorted line per canonical theorem listing its transitive axiom dependencies. Computed via `Lean.collectAxioms`. CI fails on any unack'd diff.
2. **`check-no-output-eq-v2`** — `forallTelescope` walk over each canonical theorem's parameter binders. Each binder type is `whnf`/`reduceAll`-reduced (unfolds `abbrev`/`def` chains) and scanned for forbidden `Name`s catalogued in a new `trust/forbidden-types.txt`.

The exe runs in seconds on warm cache; no significant CI cost.

## Step-by-step

### Step 1 — Lake exe scaffolding

**New files:**
- `bin/trust-gate/Main.lean` — entry point dispatching subcommands `regenerate-deps`, `check-deps`, `check-no-output-eq-v2`, `all`.
- `bin/trust-gate/CanonicalTheorems.lean` — env walker returning the 63 `Name`s matching `ZiskFv.Equivalence.<File>.equiv_<OP>` where `<OP>` is `[A-Z][A-Z0-9]*` (no underscore-suffix). Mirrors V1's regex semantics in the env, not the source text.
- `bin/trust-gate/AxiomClosure.lean` — `Lean.collectAxioms`-based per-theorem walker.
- `bin/trust-gate/TypeWalk.lean` — binder-type walker.

**Modified:** `lakefile.toml` — add `[[lean_exe]] name = "trust-gate"`.

Estimated size: ~400 lines Lean meta-programming.

### Step 2 — Per-theorem axiom-closure baseline

`AxiomClosure.lean`:
```lean
def axiomDepsForTheorem (env : Environment) (name : Name) : List Name :=
  let kernelAxioms : List Name :=
    [`propext, `Classical.choice, `Lean.ofReduceBool,
     `Lean.trustCompiler, `Quot.sound]
  let st := (Lean.collectAxioms name |>.run {} env).snd
  st.axioms.toList.filter (· ∉ kernelAxioms) |>.qsort (· < ·)
```

`bin/trust-gate/regenerate-deps`:
- Iterate canonical theorems.
- For each, compute `axiomDepsForTheorem` and emit
  `<theorem-name>: <comma-sep axiom names>` to `trust/baseline-equiv-axiom-deps.txt`.
- Sort lines for determinism.

`bin/trust-gate/check-deps`: regenerate to a temp file; `diff` against committed baseline; exit nonzero on any diff.

### Step 3 — Type-walk

`TypeWalk.lean`:
```lean
def checkBinderType (forbidden : List Name) (binderType : Expr)
    : MetaM (Option Name) := do
  let reduced ← Lean.Meta.reduceAll binderType
  for f in forbidden do
    if reduced.find? (·.isConstOf f) |>.isSome then return some f
  return none

def checkTheorem (forbidden : List Name) (name : Name)
    : MetaM (List Violation) := do
  let info := (← getEnv).find? name |>.get!
  Lean.Meta.forallTelescope info.type fun args _ => do
    args.toList.filterMapM fun arg => do
      let bt ← Lean.Meta.inferType arg
      match ← checkBinderType forbidden bt with
      | some f => return some ⟨name, arg, f, ← Lean.Meta.ppExpr bt⟩
      | none   => return none
```

`reduceAll` unfolds `abbrev` chains and `@[reducible] def`s; the aliasing dodge is closed.

### Step 4 — Forbidden-types catalog

**New file:** `trust/forbidden-types.txt` (CODEOWNER-protected). One fully-qualified `Name` per line:

```
PureSpec.execute_ADD_pure
PureSpec.execute_BEQ_pure
… (one per opcode that has a pure spec — ~63)
PureSpec.LbInput.data0
PureSpec.LbInput.data1
… (sail data-field projections that should not surface in canonical theorem parameter types)
LeanRV64D.Functions.execute
LeanRV64D.Functions.execute_instruction
```

Hand-edited; adding entries requires CODEOWNER review (gates against catalog erosion). The list is bounded — one entry per opcode/projection.

### Step 5 — Trust gate integration

**`trust/scripts/check-axiom-deps.sh`** (new): thin wrapper around `lake exe trust-gate check-deps`.

**`trust/scripts/check-no-output-eq-v2.sh`** (new): thin wrapper around `lake exe trust-gate check-no-output-eq-v2`. Reads `trust/forbidden-types.txt`.

**`trust/scripts/check-all.sh`**: append the two new checks.

```
run "7/8 axiom-deps baseline"     "$dir/check-axiom-deps.sh"
run "8/8 forbidden types (V2)"    "$dir/check-no-output-eq-v2.sh"
```

**`trust/scripts/regenerate.sh`**: extend to also run `lake exe trust-gate regenerate-deps` after the existing baseline regeneration.

**Note on build dependency:** V2 checks require `.olean`s; CI must run `lake build` before invoking `check-all.sh`. If `check-all.sh` is currently used pre-build (the existing six checks don't need oleans), split into `check-all-syntactic.sh` (V1, fast) and `check-all-semantic.sh` (V2, requires build). Or gate V2 on a `--full` flag. Recommend the split.

### Step 6 — Documentation

- `trust/README.md`: drop the "V2 future work" entries; add a section describing the new checks. Update the scenario table with the V2-caught entries (renamed-hypothesis, `abbrev`-aliased spec, silent axiom-dep growth).
- `docs/fv/trusted-base.md`: add a "Inspecting per-theorem trust" section pointing at `baseline-equiv-axiom-deps.txt`.
- `CLAUDE.md` trust gate items: add #7 (axiom-deps baseline) and #8 (forbidden types). Bump the count "six things if you break any" to "eight things."
- `.github/CODEOWNERS`: add `/trust/forbidden-types.txt` and `/trust/baseline-equiv-axiom-deps.txt`.

### Step 7 — First-run audit (high-value, do not skip)

After scaffolding lands, run `lake exe trust-gate regenerate-deps` and inspect `baseline-equiv-axiom-deps.txt` *before* committing. Each canonical theorem's axiom list should match expectations:

- ALU opcodes (ADD/SUB/AND/OR/XOR/SLT/SLTU/...): expect `transpile_<OP>` + `bin_table_consumer_wf` + memory-bus axioms. Should NOT see arith-table or MemAlign axioms.
- Loads (LB/LH/LW/LBU/LHU/LWU/LD): expect `transpile_L*` + Mem state-bridge + memory-bus + (for LBU/LHU/LWU) `memalign_load_high_bytes_zero` + (for LB/LH/LW) `signextend_load_c_packed`. Should NOT see arith axioms.
- Branches (BEQ/BNE/...): expect `transpile_B*` + `bin_table_consumer_wf` + memory-bus + `memory_bus_register_write_perm_sound{,_store_pc}`. Should NOT see SEXT or MemAlign axioms.

Any unexpected dependency surfaced here is a real present-state finding that the V1 gate didn't catch. Investigate and fix the underlying proof routing before sealing the baseline.

#### First-run audit results (executed 2026-05-08)

The first-run baseline surfaces several findings that diverge from the
expectations sketched above. Each is a real present-state finding the
V1 gate missed.

**1. The 66 `transpile_<OP>` axioms are mostly not consumed by any canonical theorem.**

Only `transpile_PC_for_AUIPC`, `transpile_PC_for_JAL`, and
`transpile_PC_for_JALR` (3 of the 66) appear as canonical-theorem
dependencies. The other 63 transpile contracts are consumed only by
the `transpile_<OP>_consumer` theorems in
`ZiskFv/Fundamentals/TranspileConsumers.lean`, which the file's own
docstring describes as "not individually load-bearing for any
downstream equivalence proof." The trust-ledger framing in
`docs/fv/trusted-base.md` says "66 transpile contracts (1 class)" —
but the canonical-theorem footprint is actually `{transpile_PC_for_*}`
(3 axioms).

This does NOT mean the 63 unused axioms are dead trust — they
encode the Rust transpiler's lowering and may be referenced by
non-canonical theorems or future proofs. But the V2 baseline lets
reviewers see exactly what each canonical equiv theorem consumes,
which is a more honest picture than the global ledger alone.

**2. ALU/branch/multiplier/divider canonical theorems have small or zero project-axiom footprints.**

`equiv_ADD`, `equiv_ADDI`, `equiv_BEQ`, `equiv_BNE`, `equiv_BLT`,
`equiv_BLTU`, `equiv_BGE`, `equiv_BGEU`, `equiv_DIV*`, `equiv_REM*`,
`equiv_MUL*`, `equiv_FENCE`, `equiv_LUI` all show 0 project axioms.
`equiv_SUB`, `equiv_AND`, `equiv_OR`, `equiv_XOR`, etc. show only
`bin_table_consumer_wf`.

The reason: the canonical theorems take circuit witnesses (carry
chains, byte-range hypotheses, range-table outputs) as parameters
and the proof itself does not need to invoke the lookup-soundness
axioms. The trust enters at the discharge layer (the caller that
materializes the parameters from a real circuit witness). So the
canonical theorem's footprint is genuinely smaller than the project
ledger total — by design, modulo the modular interface.

**3. The 7 loads consume the expected memory + platform axioms.**

| Op  | Memory   | State-bridge   | Platform (PMP/CLINT/PMA) | Closure axiom |
| --- | -------- | -------------- | ------------------------ | ------------- |
| LB  | ✓        | ✓              | ✓                        | `signextend_load_c_packed` |
| LH  | ✓        | ✓              | ✓                        | `signextend_load_c_packed` |
| LW  | ✓        | ✓              | ✓                        | `signextend_load_c_packed` |
| LBU | ✓        | ✓              | ✓                        | `memalign_load_high_bytes_zero` |
| LHU | ✓        | ✓              | ✓                        | `memalign_load_high_bytes_zero` |
| LWU | ✓        | ✓              | ✓                        | `memalign_load_high_bytes_zero` |
| LD  | ✓        | ✓              | ✓                        | (none — Family A pure Lean) |

This matches the V1 plan execution: `LD` is genuinely Lean-proven via
`Circuit/LoadDerivation.lean::load_copyb_e1_e2_bytes_eq`; LB/LH/LW
use the SEXT-closure axiom; LBU/LHU/LWU use the MemAlign zero-pad
axiom. ✓ Expected.

**4. The 4 stores (SB/SH/SW/SD) consume only the 3 platform axioms.**

`row_models_sail_state_store` (the store-side memory state bridge,
class #3 in the trust ledger) is NOT in the canonical store theorems'
closure. The store proofs route through a different, axiom-free path.
This is a real finding — `row_models_sail_state_store` is in the
trust ledger but not consumed by canonical store theorems.

**5. The 12 shift-family theorems each consume `bin_ext_table_consumer_wf` exactly once.**

Expected — shifts use the BinaryExtension AIR.

**6. AUIPC/JAL/JALR carry exactly the PC-related transpile contracts plus, for JALR, `update_elp_state_is_pure_unit` (Zicfilp).**

Expected.

These findings inform follow-up trust-content work (the precedent-based
plan to actually retire `signextend_load_c_packed` /
`memalign_load_high_bytes_zero` discussed in chat, plus a pass to audit
whether the 63 unused transpile contracts and `row_models_sail_state_store`
are still needed). They do NOT block sealing the baseline — the snapshot
itself is the audit surface, and any deviation from this committed file
will fail CI.

### Step 8 — Verification

```
nix develop --command lake build
nix develop --command lake exe trust-gate regenerate-deps
git diff trust/baseline-equiv-axiom-deps.txt    # AUDIT
nix develop --command lake exe trust-gate all
nix develop --command bash trust/scripts/check-all-semantic.sh
nix run .#test
```

All checks must pass. Specifically:
- `check-deps` reports no diff after the baseline is committed.
- `check-no-output-eq-v2` reports zero violations.
- The first-run baseline-deps file is reviewed entry-by-entry.

## Critical files

- **New:** `bin/trust-gate/{Main,CanonicalTheorems,AxiomClosure,TypeWalk}.lean` — Lake exe.
- **New:** `trust/forbidden-types.txt` — CODEOWNER-protected catalog.
- **New:** `trust/baseline-equiv-axiom-deps.txt` — generated baseline.
- **New:** `trust/scripts/check-axiom-deps.sh`, `check-no-output-eq-v2.sh`.
- **Modified:** `lakefile.toml` (add `lean_exe`).
- **Modified:** `trust/scripts/check-all.sh` (or split into `-syntactic` / `-semantic`).
- **Modified:** `trust/scripts/regenerate.sh`.
- **Modified:** `.github/CODEOWNERS`.
- **Modified:** `CLAUDE.md`, `trust/README.md`, `docs/fv/trusted-base.md`.

## Reusable infrastructure

- `Lean.collectAxioms` — Mathlib / core, computes transitive axiom closure of a `Name`.
- `Lean.Meta.forallTelescope`, `Lean.Meta.reduceAll`, `Lean.Meta.inferType`, `Lean.Meta.ppExpr` — standard meta toolkit.
- `Expr.find?` / `Expr.containsConst` — `Expr` traversal.
- The existing CODEOWNER infrastructure (`.github/CODEOWNERS`).

## What V2 catches that V1 misses

| Scenario | V1 result | V2 result |
|---|---|---|
| Renamed hypothesis with same OUTPUT-EQ type | passes | fails (type-walk hits `PureSpec.execute_<OP>_pure`) |
| `abbrev SilentSpec := PureSpec.execute_LBU_pure` aliasing | passes | fails (`reduceAll` unfolds the abbrev) |
| Hypothesis hidden inside a structure field or conjunction | passes | fails (binder-type is the conjunction; type-walk descends) |
| Equivalence proof silently picks up an additional axiom | passes (if the axiom was already in the baseline) | fails (per-theorem deps changed) |
| Equivalence proof's deps shrink (axiom retired) | passes silently | fails (deps changed; explicit ack required) |

The last row matters: even *removing* a dependency without acknowledgement is flagged. That's by design — review wants to see deliberate trust-surface changes.

## What V2 does NOT catch

- **Genuinely novel forbidden types** not in `forbidden-types.txt`. Same expansion problem V1 has, shifted to types. Mitigated by the catalog being CODEOWNER-protected and bounded.
- **Vacuous theorem regressions** (theorem typechecks but no caller can supply the hypotheses). Distinct concern; handled by usability tests, not the gate.
- **Trust beyond the project axioms** (Lean kernel, Mathlib, Sail translation). Out of scope by project trust scoping.

## Trust budget impact

Zero. V2 adds no axioms; it adds two checks and one generated baseline file. The proof tree is unchanged.

## Out of scope

- Replacing V1 entirely. V1's syntactic checks (locality, baseline freshness, source-text-hash, floors, sorry, uniformity) remain — they're orthogonal to V2's semantic checks and run faster (no `lake build` dependency).
- Per-theorem performance baselines (`#print axioms`-style depth, proof term size). Useful but distinct.
- Catching `proof_irrel_heq`-style kernel reductions that fold OUTPUT-EQ content into a non-equation type. Adversarial; out of scope.

## Sequencing

V2 is independent of the Family B / Family C plan in `make-a-plan-to-moonlit-feather.md`. They can land in either order:

- If V2 lands first, the audit step (Step 7) will surface `signextend_load_c_packed` and `memalign_load_high_bytes_zero` as load-equiv dependencies. Subsequent Family B/C work removes/refactors them and the baseline shrinks.
- If Family B/C lands first, V2's first baseline starts cleaner.

Either order works. The Family B/C plan is the higher-value one for trust *content*; V2 is the higher-value one for trust *visibility*.
