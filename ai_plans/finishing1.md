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

## Scope — 23 opcodes (revised down from 27)

The four SLT family opcodes (SLT, SLTU, SLTI, SLTIU) **leave this
branch** because their Tier-1 derivation requires the `Binary` AIR's
row-constraint extraction, which is a finishing2 deliverable. They
move to finishing2 alongside Logic/Shift.

Remaining 23, by archetype:

| Archetype | Opcodes (count) |
|---|---|
| ALU-Arith | ADD, ADDI, ADDW, ADDIW, SUB, SUBW (6) |
| Jump-UTYPE | JAL, JALR, LUI, AUIPC (4) |
| MDR-unsigned | MUL, MULHU, DIVU, REMU, MULW (5) |
| MDR-signed | MULH, MULHSU, DIV, DIVW, DIVUW, REM, REMW, REMUW (8) |

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

## Phase 2.5 — Tier-1 upgrade

For each Tier-2 opcode (22 of them: 9 ALU-Arith + 4 Jump-UTYPE +
4 MDR-unsigned + 8 MDR-signed; minus ADD, MULHU pending K3 extension)
plus the **MULHU sorry fix**, ship a Tier-1 derivation that
discharges `h_byte_sum` from circuit primitives.

### Pre-step: K3 high-half lift (fixes MULHU sorry)

Add to `Fundamentals/PackedBitVec/Extensions.lean`:

```lean
lemma to_bits_truncate128_extractLsb_64_64
    (n : ℕ) :
    BitVec.extractLsb' 64 64 (to_bits_truncate (l := 128) n)
      = BitVec.ofNat 64 (n / 2^64)
```

Parallel to existing `to_bits_truncate128_setWidth64` (low-half).
Then `execute_MUL_pure_hi_eq` closes without `sorry`.

### Per-archetype Tier-1 upgrade structure

Each archetype-X agent rewrites the existing Tier-2 lemmas in
`Equivalence/RdValDerivation/X.lean` so each `h_rd_val_<archetype>_<op>`
now takes circuit hypotheses directly and discharges `h_byte_sum`
internally. The lemma's **conclusion** is unchanged (Phase 3 still
calls it the same way); only the **hypothesis interface** changes
from "parameterized byte-sum" to "circuit constraints + lane-match +
ranges + Sail-input bridges."

### N-ALU-Arith — Tier-1 upgrade for 5 opcodes (ADD already Tier-1)

| Opcode | Field-level input | BitVec bridge | Notes |
|---|---|---|---|
| ADDI | `Spec/Addi::addi_compositional` (verify exists; if not, port from `Spec/Add`) | K1-A | imm folded into `b` lanes |
| ADDW | `Spec/Addw::addw_compositional` | K1-A; m32=1 high-lane zero via `bus_shape_for_main_at_m32_one` | 32-bit; sign-extended low-32 |
| ADDIW | `Spec/Addiw::addiw_compositional` | K1-A + m32=1 | imm + m32=1 |
| SUB | `Spec/Sub::sub_compositional` | K1-A | check whether ZisK SUB negates `b` upstream of BinaryAdd or uses a separate carry chain |
| SUBW | `Spec/Subw::subw_compositional` | K1-A + m32=1 | |

Block any opcode whose `Spec/<X>::<X>_compositional` theorem is missing,
report DONE_WITH_CONCERNS, and document.

### N-Jump-UTYPE — Tier-1 upgrade for 4 opcodes

| Opcode | Field-level input | BitVec bridge |
|---|---|---|
| JAL | `Spec/Jal` (verify field-level identity exists; result = `pc + 4` field-level) | K3 `pc_plus4_bv64_of_bytes` |
| JALR | `Spec/Jalr` | K3 `pc_plus4_bv64_of_bytes` |
| LUI | `Spec/Lui` | K3 `u64_toBV_of_imm20_lanes` + `signExtend_imm20_nat_lanes` |
| AUIPC | `Spec/Auipc` (also `Spec/AddUpperImmediatePC.lean` exists) | K3 byte-bridge + the imm-add field identity |

### N-MDR-unsigned — Tier-1 upgrade for 5 opcodes (MULHU needs K3 ext first)

| Opcode | Field-level input | BitVec bridge |
|---|---|---|
| MUL | `Spec/MulField::main_mul_unsigned_field_correct` (shipped) | K3 `mul_lo_bv64_of_byte_sum`, `execute_MUL_pure_lo_eq` |
| MULHU | same field identity (high half via `d_chunks_packed`) | **K3 high-half lift (pre-step above)** |
| DIVU | `Spec/DivFieldSigned::main_div_unsigned_field_correct` (shipped) | K3 unsigned-div byte bridge |
| REMU | `Spec/DivFieldSigned::main_rem_unsigned_field_correct` (shipped) | same |
| MULW | `Spec/MulField` low-half + 32-bit signExtend | K3 + sign-extension |

### N-MDR-signed — Tier-1 upgrade for 8 opcodes

All consume K4-shipped `Spec/MulFieldSigned` + `Spec/DivFieldSigned`
+ `Fundamentals/PackedBitVec/Signed`. Per opcode:

| Opcode | Field-level input | BitVec bridge |
|---|---|---|
| MULH | `main_mul_signed_field_correct` with `(na=1, nb=1, np=0)` | K4 high-half + sign-case lift |
| MULHSU | same with Track P MULHSU witness disjunction | K4 + Track P case-split |
| DIV | `main_div_signed_field_correct_main_level` | K4 signed-DIV; INT_MIN/-1 via `int_tdiv_overflow_case` |
| DIVW | 32-bit signed; m32=1 path | K4 + 32-bit signExtend |
| DIVUW | unsigned-cast signed-witness path; per agent's note, witnesses pin to zero via `arith_table_div_w_witnesses_from_data` | K4 unsigned route |
| REM | `main_rem_signed_field_correct_main_level` | K4 signed-REM |
| REMW | 32-bit signed | K4 + 32-bit signExtend |
| REMUW | unsigned-cast 32-bit | K4 unsigned + signExtend |

### Verification gate per archetype (Phase 2.5)

```bash
cd /home/cody/zisk-fv/.worktrees/track-n/ZiskFv
# Existing Tier-2 build still passes; Tier-1 upgrade replaces it in-place.
lake build ZiskFv.Equivalence.RdValDerivation.Arith
lake build ZiskFv.Equivalence.RdValDerivation.JumpUType
lake build ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned
lake build ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned
# Final
lake build ZiskFv
# expected: 0 errors, 0 sorries, 0 new warnings
```

The hard gate: **`grep -n 'h_byte_sum' ZiskFv/ZiskFv/Equivalence/RdValDerivation/*.lean`
returns 0 hits** (the byte-sum equality is now a `have`, not a parameter).

## Phase 3 — cleanup of `Equivalence/<Op>.lean`

For each of the 23 in-scope opcodes:

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
# Per-archetype grep gate
for op in Add Addi Addiw Addw Sub Subw \
          Jal Jalr Lui Auipc \
          Mul MulHU Divu Remu MulW \
          MulH MulHSU Div Divw Divuw Rem Remw Remuw; do
  echo -n "$op: " ; grep -c 'h_rd_val :' "ZiskFv/ZiskFv/Equivalence/${op}.lean" 2>/dev/null || echo 0
done
# expected: 0 for each

# Final
cd ZiskFv && lake build
# expected: 0 errors, 0 sorries
```

## Trust state at end of branch (for the 23 in-scope opcodes)

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
| K2 Layer-2 closure | needs F-typed memory-bus extraction (reads side) + Mem AIR (writes side) | finishing2/3 |
| Loads / Stores `h_rd_val` retirement | needs Mem AIR | finishing3 |
| Branches | don't write rd | n/a |

## Recommended dispatch (this branch)

**Wave A — K3 extension fix** (single subagent, ~30 min):
- Ship `to_bits_truncate128_extractLsb_64_64` in `Fundamentals/PackedBitVec/Extensions.lean`.
- Discharge MULHU's sorry in `Equivalence/RdValDerivation/MulDivRemUnsigned.lean`.

**Wave B — Phase 2.5 upgrade** (4 parallel subagents):
- N-ALU-Arith Tier-1 (5 ops + ADD already done; agent verifies ADD still works).
- N-Jump-UTYPE Tier-1 (4 ops).
- N-MDR-unsigned Tier-1 (5 ops; gated on Wave A for MULHU).
- N-MDR-signed Tier-1 (8 ops).

**Wave C — Phase 3 cleanup** (4 parallel subagents, gated on Wave B):
- One per archetype, walking `Equivalence/<Op>.lean` files.

**Final wave:** verification gates run, branch closes.

## Status / next action

- Phase 1 keystones complete.
- Phase 2 Tier-2 wrappers complete (commits `be7264c`, `ec7dd8e`,
  `bed62b7`, `23e5669`, `86ec279`).
- **Next step:** Wave A — dispatch K3 extension fix as a single
  subagent. Then Wave B in parallel.
