# finishing1 — Track N: h_rd_val *retirement*, not rephrasing

**Branch:** `feature/track-n-h-rd-val` (worktree at `/home/cody/zisk-fv/.worktrees/track-n`).
**Source plan:** `/home/cody/.claude/plans/squishy-strolling-catmull.md`.

## Goal — calibrated honestly

For each opcode in this branch's scope, **eliminate the `h_rd_val :`
parameter** from `Equivalence/<Op>.lean`'s metaplan theorems by
*deriving the BitVec rd-write equality from circuit primitives*. Not
by rephrasing it into a byte-sum hypothesis.

This requires composing four ingredients per opcode:

1. **Field-level Spec identity** (per archetype, already shipped; e.g.
   `Spec/Add::add_compositional`, `Spec/MulField::main_mul_unsigned_field_correct`).
2. **BitVec lift** of that field identity to `BitVec 64` (Phase 1
   keystones K1-A / K3 / K4).
3. **Byte decomposition** of `BitVec 64` into the 8 byte lanes of the
   memory-bus rd-write entry.
4. **Lane-match** (K2) tying memory-bus entry lanes back to Main's
   `c_0`/`c_1` columns.

Phase 2 (already shipped) produced **thin-wrapper "Tier-2"** discharge
lemmas that do step 3 only and accept step 1+2's product as an
`h_byte_sum` hypothesis. That is **not trust reduction** — same
trust class as `h_rd_val`, expressed in `Nat` form. The only Tier-1
derivation Phase 2 shipped is **ADD**.

This rewrite adds **Phase 2.5 — Tier-1 upgrade** between the existing
Phase 2 and Phase 3 cleanup.

## The trust chain (so the goal is concrete)

```
[byte-bus rd-write entry e2: 8 byte lanes]
  ↓ K2 writes-side lane-match               ─ closed in finishing3 S4
[Main's c_0, c_1 lanes]
  ↓ operation-bus matches_entry              ─ existing infra
[Secondary AIR's c chunks]
  ↓ field-level Spec identity                ─ shipped per opcode
[Spec result in chunk form]
  ↓ K1-A / K3 / K4 BitVec lift               ─ shipped (Phase 1)
[BitVec spec result]
  ↓ byte decomposition                        ─ Phase 2 thin-wrapper layer
[entry's bytes pack to spec.toNat]
```

**At end of this branch:** the chain is closed from byte-bus entry
back to "Spec field identity + circuit constraints," parameterized
only on K2 (Layer 1 today; closes in finishing2/3). After finishing2
+ finishing3, the chain is closed end-to-end for these opcodes.

## Scope — 10 opcodes (revised down from 23 after Wave B reconnaissance)

After Wave B's reconnaissance (commits `ea9f0a2`, `a063edf`,
DONE_WITH_CONCERNS for both MDR archetypes), the multiplicative
family — MUL, MULHU, DIVU, REMU, MULW, MULH, MULHSU, DIV, DIVW,
DIVUW, REM, REMW, REMUW — **leaves this branch.** Their Tier-1
upgrade requires a **multiplicative no-wrap toolkit** (lifting
`a_packed * b_packed = c_packed + d_packed * 2^64` from FGL to a ℕ
identity over chunk values up to `2^128`). That argument doesn't
factor through a single packed-FGL-`.val` lemma — it requires
chunk-level carry-chain reasoning over up to 16 chunks, plus the
signed `BitVec.toInt` bridges for the signed half. That's a
substantial second toolkit phase, scoped separately from this
branch.

The four SLT family opcodes (SLT, SLTU, SLTI, SLTIU) also stay
out — Tier-1 needs the `Binary` AIR row-constraint extraction
which is a finishing2 deliverable.

Remaining 10, by archetype:

| Archetype | Opcodes (count) |
|---|---|
| ALU-Arith | ADD, ADDI, ADDW, ADDIW, SUB, SUBW (6) |
| Jump-UTYPE | JAL, JALR, LUI, AUIPC (4) |

Both archetypes are *additive* — the FGL identities they consume
(`add_compositional`, `sub_compositional`, `jal_store_value`,
`lui_store_value_*`, etc.) all factor through additions in FGL whose
chunk-bounded forms stay within `GL_prime`. The toolkit phase below
ships exactly the abstraction needed to close them.

## What shipped (Phase 1 — keystones)

| Keystone | File(s) | Commit | Status |
|---|---|---|---|
| K1-A | `Airs/Binary/BinaryAddPackedCorrect.lean` | `f92a1ca` | ✅ |
| K3 | `Fundamentals/PackedBitVec/Extensions.lean` | `74005bf` | ✅ |
| K4 | `Fundamentals/PackedBitVec/Signed.lean` + `Spec/MulFieldSigned.lean` + `Spec/DivFieldSigned.lean` | `919b0a2` | ✅ |
| K2 | `Airs/MemoryBus/LaneMatch.lean` | `2c627ac` | ⚠️ Layer 1; closes in finishing2/3 |

Plus three docs: `track-n-traps.md` (`6016ca1`), `air-inventory.md`
(`7f1aa3b`), `.gitignore` (`f21d3c9`).

## What shipped (Phase 2 — Tier-2 wrappers; insufficient on its own)

| Archetype | File | Commit | Tier |
|---|---|---|---|
| N-ALU-Arith | `Equivalence/RdValDerivation/Arith.lean` | `be7264c` | ADD: Tier-1 ✓; 9 others: Tier-2 |
| N-Jump-UTYPE | `Equivalence/RdValDerivation/JumpUType.lean` | `ec7dd8e` | 4 of 4: Tier-2 |
| N-MDR-unsigned | `Equivalence/RdValDerivation/MulDivRemUnsigned.lean` | `bed62b7` | 4 of 5: Tier-2; **MULHU: `sorry`** (needs K3 high-half lift) |
| N-MDR-signed | `Equivalence/RdValDerivation/MulDivRemSigned.lean` | `23e5669` | 8 of 8: Tier-2 |

Master imports linked at `86ec279`. Full `lake build ZiskFv`: 8150
jobs, 0 errors, **1 expected `sorry`** (MULHU), 1 pre-existing linter
warning (`Bridge1.lean`).

Phase 2 deliverables are **kept** as the Tier-1 lemmas' final layer
(byte decomposition); Phase 2.5 wraps higher-level circuit
hypotheses on top. The byte-decomposition half is real work the
Tier-1 lemmas need.

## Phase 2.5 — Tier-1 upgrade (additive opcodes only)

Discharges `h_byte_sum` (and the `h_input_val` chunk-equality residual
from commit `ea9f0a2`/`a063edf`) from circuit primitives, for the 10
additive opcodes in revised scope.

### Phase 2.5-pre — Goldilocks no-wrap toolkit (built by hand, TDD)

Wave B's reconnaissance showed every blocked / partial agent hit the
same missing abstraction: K1-A solves the FGL→ℕ no-wrap argument
*bespoke* for `BinaryAdd`'s carry chain, but never factored it. So
each per-archetype agent had to rebuild the same tactical chain
(`push_cast; ring` → `congr_arg Fin.val` → `simp [Fin.val_natCast]` →
`omega`) and gave up when the framing didn't fit cleanly.

This sub-phase builds the abstraction once. Built **by hand, not via
agent**, with **TDD discipline** (write lemma signatures + a worked
example using them; verify the example compiles with `sorry` bodies;
then close the proofs).

**Scope — additive only (multiplicative deferred):**

New file `ZiskFv/ZiskFv/Fundamentals/PackedBitVec/NoWrap.lean`. Three
core lemmas:

1. `fgl_eq_to_nat_eq` — abstract no-wrap lift. Given two ℕ values
   `lhs` and `rhs` with `((lhs : ℕ) : FGL) = ((rhs : ℕ) : FGL)` and
   `lhs < GL_prime`, `rhs < GL_prime`, conclude `lhs = rhs`. Pure
   no-wrap argument; closes via `congr_arg Fin.val` + `Fin.val_natCast`
   + `omega`.

2. `fgl_packed_2_lanes_natCast` — `l₀ + l₁ * 2^32 = ((l₀.val + l₁.val * 2^32 : ℕ) : FGL)`
   in FGL. Trivial via `push_cast; ring`. Lets callers cast a
   2-lane FGL packing into Nat-cast form for use with
   `fgl_eq_to_nat_eq`.

3. `fgl_packed_4_chunks_natCast` — same shape for 4×16-bit chunks
   (used by Arith / Main projections).

**Worked example (TDD test):** in the same file, demonstrate the
toolkit by writing a 3-4 line proof of an additive carry-chain
identity (e.g., re-derive `carry_chain_0_nat`'s body using the
toolkit). This validates the abstraction is actually usable
end-to-end before fan-out.

**Verification gate (this sub-phase):**

```bash
cd /home/cody/zisk-fv/.worktrees/track-n/ZiskFv
lake build ZiskFv.Fundamentals.PackedBitVec.NoWrap
lake build ZiskFv  # full
# expected: 0 errors, 0 sorries
```

**Out of scope (deferred to a later branch):**
- Multiplicative no-wrap toolkit (the FGL↔ℕ identity for
  `a_packed * b_packed = c_packed + d_packed * 2^64`). Requires
  carry-chain reasoning across up to 16 chunks and cannot be
  abstracted as a single `.val` lemma.
- Signed `BitVec.toInt` reductions (K4-extension territory).
- 8-chunk and other packing arities not used by the 10 additive
  opcodes in scope.

### Per-archetype Tier-1 upgrade

Two parallel agent dispatches (one per archetype). Each agent rewrites
the existing Tier-2 (or Tier-1.5) form in `Equivalence/RdValDerivation/<X>.lean`
so each `h_rd_val_<archetype>_<op>` takes circuit hypotheses directly
and discharges `h_byte_sum` *and* `h_input_val` internally.

#### N-ALU-Arith — Tier-1 upgrade for 5 opcodes (ADD already Tier-1)

Existing form: `ea9f0a2` (Tier-1.5; ADDI/ADDW/ADDIW/SUB/SUBW each
take an `h_input_val : bus_entry.c_lo.val + bus_entry.c_hi.val * 2^32 = spec_val.toNat`
parameter). Upgrade replaces that parameter with composition through
the corresponding `Spec/<X>::<X>_compositional` theorem + the no-wrap
toolkit.

| Opcode | Field-level input |
|---|---|
| ADDI | `Spec/Addi::addi_compositional` |
| ADDW | `Spec/Addw::addw_compositional` |
| ADDIW | `Spec/Addiw::addiw_compositional` |
| SUB | `Spec/Sub::sub_compositional` |
| SUBW | `Spec/Subw::subw_compositional` |

#### N-Jump-UTYPE — Tier-1 upgrade for 4 opcodes

Existing form: `a063edf` (Tier-1.5; each opcode takes `h_e2_*_val`,
`h_pc_lo_val`, `h_b0_lo`, etc. parameters that should be derived
from circuit + transpile bridges). Upgrade replaces those with
internal composition.

| Opcode | Field-level input |
|---|---|
| JAL | `Spec/Jal::jal_store_value` |
| JALR | `Spec/Jalr::jalr_store_value` |
| LUI | `Spec/LoadUpperImmediate::lui_store_value_lo/hi` |
| AUIPC | `Spec/AddUpperImmediatePC::auipc_store_value_lo` |

### Verification gate (Phase 2.5)

```bash
cd /home/cody/zisk-fv/.worktrees/track-n/ZiskFv
lake build ZiskFv.Equivalence.RdValDerivation.Arith
lake build ZiskFv.Equivalence.RdValDerivation.JumpUType
lake build ZiskFv  # full
```

The hard gate: **`grep -nE '\(h_byte_sum|\(h_input_val|\(h_e2_lo|\(h_e2_hi_val|\(h_pc_lo_val|\(h_b0_lo|\(h_b1_hi' ZiskFv/ZiskFv/Equivalence/RdValDerivation/{Arith,JumpUType}.lean`
returns 0 hits.** The trust gap on the BitVec rd-write equality is
fully discharged from circuit primitives — no chunk-equality, byte-sum,
or "circuit lane = spec half" parameter survives.

## Phase 3 — cleanup of `Equivalence/<Op>.lean`

For each of the 10 in-scope opcodes:

1. Remove `h_rd_val :` from each metaplan theorem signature
   (`_metaplan`, `_metaplan_from_bus`, `_metaplan_bus_self`,
   `_metaplan_op_bus`).
2. Replace its call site with `h_rd_val_<archetype>_<op> ...` from
   the Tier-1 derivation in `RdValDerivation/<archetype>.lean`.
3. Add the new circuit-hypothesis parameters the Tier-1 lemma
   requires — these are the same form already required by the
   Phase-4.5 A-rewire (`add_circuit_holds`-style bundles, byte
   ranges, lane-match) and are already supplied by GoldenTraces
   fixtures + the existing top-level driver.

Best dispatched as one subagent per archetype (4 in parallel — they
edit disjoint file sets).

### Phase 3 verification gate

```bash
# Per-archetype grep gate (10 in-scope opcodes)
for op in Add Addi Addiw Addw Sub Subw \
          Jal Jalr Lui Auipc; do
  echo -n "$op: " ; grep -c 'h_rd_val :' "ZiskFv/ZiskFv/Equivalence/${op}.lean" 2>/dev/null || echo 0
done
# expected: 0 for each

# Final
cd ZiskFv && lake build
# expected: 0 errors, 0 sorries
```

## Trust state at end of branch (for the 10 in-scope opcodes)

After Phase 2.5 + Phase 3 close:

| Trust item | Status at end of finishing1 | Closes in |
|---|---|---|
| `h_rd_val` parameter on metaplan theorems | **retired** ✅ | this branch |
| `h_byte_sum` parameter on Tier-2 wrappers | **retired** ✅ (replaced by composition) | this branch |
| K2 reads-side lane-match (`register_read_*_lanes_match`) | parameterized (Layer 1) | finishing2 S3 |
| K2 writes-side lane-match (`register_write_lanes_match`) | parameterized (Layer 1) | finishing3 S4 |
| Operation-bus `matches_entry` | parameterized; consequence of permutation soundness | trust-scoped (assumed) |
| Range-check / lookup soundness | parameterized | trust-scoped (assumed) |

## Out of scope for this branch

| Item | Why | Where |
|---|---|---|
| SLT, SLTU, SLTI, SLTIU | Tier-1 needs `Binary` AIR row-constraint extraction | finishing2 |
| K1-B (AND/OR/XOR PackedCorrect) | needs `Valid_Binary` | finishing2 |
| K1-C (Shift PackedCorrect) | needs `Valid_BinaryExtension` | finishing2 |
| N-ALU-Binary derivation | needs K1-B + K1-C | finishing2 |
| MUL, MULHU, DIVU, REMU, MULW (5 unsigned) | Tier-1 needs multiplicative no-wrap toolkit | new follow-up; Tier-2 form remains in tree from `bed62b7` |
| MULH, MULHSU, DIV, DIVW, DIVUW, REM, REMW, REMUW (8 signed) | needs multiplicative + signed `BitVec.toInt` toolkit | new follow-up; Tier-2 form remains in tree from `23e5669` |
| K2 Layer-2 closure | needs F-typed memory-bus extraction (reads side) + Mem AIR (writes side) | finishing2/3 |
| Loads / Stores `h_rd_val` retirement | needs Mem AIR | finishing3 |
| Branches | don't write rd | n/a |

## Recommended dispatch (this branch)

**Wave A — K3 high-half extension** ✅ shipped at `92305eb` (closed MULHU sorry).

**Wave B — Tier-2/Tier-1.5 reconnaissance** ✅ shipped at `ea9f0a2`
(N-ALU-Arith Tier-1.5) and `a063edf` (N-Jump-UTYPE Tier-1.5). Two
MDR archetypes escalated DONE_WITH_CONCERNS without commit; the
common gap was the missing FGL→ℕ no-wrap abstraction. Tier-2 forms
remain in tree for the 13 MDR opcodes.

**Wave B.5 — Goldilocks no-wrap toolkit** (built by hand, TDD discipline):
- Ship `Fundamentals/PackedBitVec/NoWrap.lean` with three lemmas
  (`fgl_eq_to_nat_eq`, `fgl_packed_2_lanes_natCast`,
  `fgl_packed_4_chunks_natCast`) plus a worked-example test.
- Verify full `lake build` clean.
- **Multiplicative + signed toolkit explicitly out of scope** for
  this sub-phase to prevent spiral.

**Wave B.6 — Tier-1 upgrade** (2 parallel subagents, gated on Wave B.5):
- N-ALU-Arith full Tier-1 (5 ops; ADD verifies unchanged).
- N-Jump-UTYPE full Tier-1 (4 ops).

**Wave C — Phase 3 cleanup** (2 parallel subagents, gated on Wave B.6):
- ALU-Arith cleanup: 6 opcode files.
- Jump-UTYPE cleanup: 4 opcode files.

**Final wave:** verification gates run, branch closes.

## Status / next action

- Phase 1 keystones complete.
- Phase 2 Tier-2 wrappers complete (commits `be7264c`, `ec7dd8e`,
  `bed62b7`, `23e5669`, `86ec279`).
- Wave A complete (`92305eb`).
- Wave B partial: ALU-Arith and Jump-UTYPE at Tier-1.5 (`ea9f0a2`,
  `a063edf`); MDR escalated.
- **Next step:** Wave B.5 — build the no-wrap toolkit by hand with
  TDD. Then Wave B.6 in parallel.
