# Phase 1 handoff

## What shipped

- **Extractor extensions** (`tools/zisk-pil-extract/`):
  - Constraint-kind differentiation: `every_row` / `first_row` / `last_row` /
    `every_frame_<min>_<max>` suffixes (was: flattened `constraint_N`).
  - New operand-kind support: `FixedCol`, `Challenge`, `AirValue`,
    `AirGroupValue`. Negative `rowOffset` on `WitnessCol`/`FixedCol` and
    constraints mixing `F` (witness cells) with `ExtF` (challenges, exposed
    values) skip-stub instead of failing typecheck downstream.
  - Pilout `Challenge { stage, idx }` → flat index via cumulative
    `num_challenges[0..stage-1]` (PIL2's stage numbering is 1-based).
  - 19 unit tests; integration via `verify-phase1` diff gate against hand
    oracles for both `BinaryAdd` (4 of 9 constraints — same as Phase 0;
    bus/permutation constraints stay stubbed and are abstracted in `Airs/`)
    and `Main` (8 of 146; the ADD subset).
- **`ZiskFv/`** Lean package, full ADD chain, zero `sorry`:
  - `Fundamentals/Goldilocks.lean` — `NatCast FGL`, `BitVec 8/16/32` ↔ `FGL`
    coercions, `isU64_chunks` / `isU64_lanes`, `chunks_to_bv64` /
    `lanes_to_bv64`. Critical note: do NOT shadow `[Field FGL]` as a
    proof-local instance variable (a comment guards against the trap that
    bit `Spec.Add` once).
  - `Fundamentals/Transpiler.lean` — `transpile_ADD` axiom over
    `RV64State`. **Trusted** surface, mirrors
    `vendor/zisk/core/src/riscv2zisk_context.rs::create_register_op`.
  - `Extraction/{Main,BinaryAdd}.lean` (+ `.hand.lean` oracles) — auto-
    regenerable from the extended extractor; diff-gated.
  - `Airs/Main.lean`, `Airs/Binary/BinaryAdd.lean` — named-column
    `Valid_<AIR>` structures (hand-written, not via `#define_subair`) with
    9 named-constraint predicates and `constraint_N_of_extraction` iff
    bridges (one per ADD-subset constraint).
  - `Airs/OperationBus.lean` — 12-field `OperationBusEntry`; sender
    (`opBus_row_Main`) and receiver (`opBus_row_BinaryAdd`) projections.
    Specialized to `m32 = 0`; the 32-bit-op path is out of Phase 1 scope.
  - `Spec/Add.lean` — `add_compositional`: the **first compositional proof**
    in the codebase (Main + BinaryAdd + bus → Goldilocks ADD). Closes via
    `linear_combination` over the two carry-chain equations.
  - `Equivalence/Add.lean` — `equiv_ADD`: composes `add_compositional` with
    the `transpile_ADD` axiom into the per-row equivalence statement.
  - `GoldenTraces/Add.lean` — concrete witness for `3 + 5 = 8`. Four
    `example`-level `decide` checks confirm chunk reassembly, lane
    recombination, and both carry chains hold on the witness.
- **`tools/zisk-fv-harness/`** — fixture-emitter Rust crate. Hardcodes the
  canonical ADD example; emits `ZiskFv/GoldenTraces/Add.lean`. Two unit
  tests cover the rendering and overflow-carry propagation.
- **`vendor/zisk/`** — git submodule pinned at `48cf7ccef` (the commit
  the vendored `pil/zisk.pilout` was built from).
- **`justfile::verify-phase1`** — extractor + harness tests, regenerate +
  diff both extractions, regenerate fixture, full `lake build`. Exits 0
  from a clean checkout.

## What was learned (relevant to the metaplan)

- **The metaplan's "first compositional proof" was not the bottleneck the
  metaplan feared.** `LeanZKCircuit.Interactions` was *not* needed for
  Phase 1 — the whole permutation-argument primitive is cleanly abstracted
  by `OperationBusEntry` (a plain projection-equality between two
  field-valued tuples). The bus-equation constraints were skip-stubbed at
  the extraction layer (mixed `F`/`ExtF` arithmetic doesn't typecheck),
  but the named-constraint layer's `matches_entry` predicate replaces
  them entirely without losing semantic content.
- **`ring` over `Fin p` works — but can be silently shadowed.**
  Declaring `[Field FGL]` as a proof-local variable creates a dummy
  instance that defeats `ring`. The workaround is to declare it once
  globally in `Fundamentals/Goldilocks.lean` and never re-quantify.
- **Coefficients written as `4294967296 * 4294967296` close `ring`;
  written as `18446744073709551616` (the same number) do not.** ring
  treats them as different polynomial atoms, with no automatic
  literal-product recognition. The `equiv_ADD` statement uses the
  factored form for this reason.
- **`(1 - 0) * x` over `Fin p` does not reduce to `x` via `simp` /
  `ring_nf` / `decide`-based rewriting** in the contexts we tried. To
  side-step this, `opBus_row_Main` is specialized to the `m32 = 0` case
  rather than carrying the `(1 - m32) *` factor that the upstream PIL
  uses. Generalizing this is Phase 1.5 work (relevant once the 32-bit
  `*_W` opcodes are in scope).
- **Track A's RV64D port shipped 47 ported files** (`ZiskFv/RV64D/*.lean`)
  with `add.lean` syntactically clean (zero `sorry`) but unbuildable
  pending `Fundamentals/Execution.lean` (a Phase 1.5 Track B deliverable
  per the STATUS.md plan). 43 RV32-specific equivalence proofs went to
  `sorry` — explicitly because they relied on RV32-width tactics, not
  upstream `LeanRV64D` brokenness. One genuine upstream blocker:
  `currentlyEnabled Ext_Zca` doesn't simp-normalize through `SailME.run`,
  blocking `jump_to_equiv` and (transitively) every branch + jump
  equivalence proof.
- **`native_decide` for Goldilocks primality is still ~386s on a cold
  build.** Not addressed in Phase 1 (was deemed Phase 2 work).

## Per-opcode effort estimate (for Phase 2 planning)

ADD took the structure work — reusable across all RV64 R-type ALU ops:
- `Valid_Main` is fully reusable.
- `Valid_BinaryAdd` is template for `Valid_BinaryAnd`, `Valid_BinaryOr`,
  `Valid_BinaryXor`; the carry-chain predicates change but the
  bus-projection shape doesn't.
- `OperationBusEntry` and the named-constraint bridge pattern are reusable.
- `Spec.Add` is the proof template — most opcodes will be a strict
  one-equation rewrite of the carry-chain shape (subtraction is trivially
  ADD-with-2's-complement; bitwise ops are independent per chunk).

**Estimate: ~1 day per ALU opcode** once Phase 2 starts (vs. ~2 weeks
for ADD's pioneering structure work). Macros (`alu_non_imm_proof`
analogue) come once 3-5 opcodes have shipped and the pattern is
crystallized.

## Phase 1.5 backlog

In priority order:

1. **`Fundamentals/Execution.lean`** — port openvm-fv's RV32 Execution
   helpers (~420 lines) to RV64. Unblocks Track A's `RV64D/add.lean`
   and the full Sail-side equivalence chain. Without this, `Equivalence/
   Add.lean` is a "circuit-level" theorem rather than a "Sail-equivalent"
   theorem.
2. **Generalize `opBus_row_Main` to handle `m32 ∈ {0, 1}`.** Either
   (a) prove the `(1 - m32) * x = x` lemma cleanly over `Fin p`, or
   (b) keep the `m32 = 0` specialization and add a parallel `m32 = 1`
   variant for the 32-bit-op path (covers `addw`, `subw`, etc.).
3. **Replace the harness's hardcoded fixture with live `ProverClient`
   output.** Requires a `cargo zisk build`-compiled probe ELF and the
   `proofman_common` dependency tree. Per-instance trace dump verifies
   that real ZisK witnesses satisfy our named-constraint model.
4. **Goldilocks primality via Pratt certificate** — reduce the 386s
   cold-build penalty.
5. **Upstream sail-riscv-lean issue:** `currentlyEnabled Ext_Zca`
   simp normalization through `SailME.run`. Blocks Track A's branch +
   jump equivalence proofs.

## Repro

```bash
cd /home/cody/zisk-fv
git submodule update --init  # if vendor/zisk isn't checked out
just verify-phase1
```

Expected: exit 0. First cold build is ~10 min (Goldilocks primality
dominates).
