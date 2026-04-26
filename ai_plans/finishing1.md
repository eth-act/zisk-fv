# finishing1 — Track N (h_rd_val retirement) closure

**Branch:** `feature/track-n-h-rd-val` (worktree at `/home/cody/zisk-fv/.worktrees/track-n`).
**Source plan:** `/home/cody/.claude/plans/squishy-strolling-catmull.md`.

## Goal

Retire the `h_rd_val :` parameter — the trusted "circuit's bus rd-write
value equals the pure spec's rd value" claim — from
`Equivalence/<Op>.lean` files for the **opcode families whose AIRs are
already extracted**. The Logic / Shift / SLT family is deferred to
`finishing2.md` because their AIRs (`Binary`, `BinaryExtension`) are not
yet extracted.

## What shipped (Phase 1 — keystones)

| Keystone | File(s) | Commit | Status |
|---|---|---|---|
| K1-A | `Airs/Binary/BinaryAddPackedCorrect.lean` | `f92a1ca` | ✅ |
| K3 | `Fundamentals/PackedBitVec/Extensions.lean` | `74005bf` | ✅ (5 lemmas, plan asked for 3) |
| K4 | `Fundamentals/PackedBitVec/Signed.lean` + `Spec/MulFieldSigned.lean` + `Spec/DivFieldSigned.lean` | `919b0a2` | ✅ |
| K2 | `Airs/MemoryBus/LaneMatch.lean` | `2c627ac` | ⚠️ structurally trivial; see "K2 status" below |

`lake build ZiskFv` exits 0 (8145 jobs).

Plus three docs:

| Doc | Commit |
|---|---|
| `docs/fv/track-n-traps.md` (K1-A traps for downstream agents) | `6016ca1` |
| `docs/fv/air-inventory.md` (full 22-AIR table + extraction status) | `7f1aa3b` |
| `.gitignore` `.worktrees/` entry | `f21d3c9` |

### K2 status

K2 shipped at `2c627ac` is structurally trivial — the three theorems
unwrap a `def` whose only content is "the lane-match equality with
sides swapped." The plan-intended derivation (slot-match against an
extracted memory-bus emission, mirroring `Airs/BusShape.lean`) is
**not in this branch**.

Probing the extractor shows there's a partial path forward: of 68
memory-bus emissions on Main, three have F-typed slots and are
extractable as proper specs:

* `bus_emission_Main_0` — register-read for rs1
* `bus_emission_Main_2` — register-read for rs2
* `bus_emission_Main_4` — store_reg previous-value (not the new write)

But two complications block "close K2 properly" inside this branch:

1. **Slot-shape mismatch.** The extracted entries are 6-slot
   `[op, addr, mem_step, bytes, value_lo, value_hi]` with 32-bit lane
   values; `Airs/MemoryBus.lean::MemoryBusEntry` is 12-slot with 8 byte
   lanes. A shim is needed to bridge.
2. **No new-value emission.** The destination register-write isn't an
   F-typed Main bus emission at all — ZisK's memory consistency model
   enforces it implicitly via subsequent reads. Properly closing
   `register_write_lanes_match` requires either a multi-row argument
   involving the Mem AIR, or accepting Layer 1 trust with a documented
   gap.

→ **K2 closure spans two later phases:**
- The reads-side theorems (rs1, rs2) close at Layer 2 in
  `finishing2.md` S3 (against the F-typed extracted Main memory-bus
  emissions).
- The writes-side theorem closes at Layer 2 in `finishing3.md` S4,
  once the Mem AIR is extracted to support the multi-row argument.

This branch leaves all three K2 theorems at Layer 1 (structural
unfolding, commit `2c627ac`) and documents the gap. Phase 2
derivations in this branch consume K2 as-is; trust on
`register_*_lanes_match` propagates upward, exactly as the
operation-bus `matches_entry` does today.

## What's left in this branch

### Phase 2 — per-shape derivation lemmas (4 archetypes)

Each ships one new file in `Equivalence/RdValDerivation/`. Each archetype
takes Main + secondary-AIR circuit hypotheses and produces the `h_rd_val`
fact directly, eliminating the parameter from downstream call sites.

| Archetype | File | Opcodes | Deps |
|---|---|---|---|
| N-ALU-Arith | `RdValDerivation/Arith.lean` | ADD, ADDI, ADDW, ADDIW, SUB, SUBW, SLT, SLTU, SLTI, SLTIU (10) | K2 + K3 + Bridges 1/2/3 (shipped) + add_compositional / sub_compositional (shipped) |
| N-Jump-UTYPE | `RdValDerivation/JumpUType.lean` | JAL, JALR, LUI, AUIPC (4) | K2 + K3 |
| N-MDR-unsigned | `RdValDerivation/MulDivRemUnsigned.lean` | MUL, MULHU, DIVU, REMU, MULW (5) | K2 + K3 + main_mul_unsigned_field_correct (shipped) + ArithTable witnesses (shipped) |
| N-MDR-signed | `RdValDerivation/MulDivRemSigned.lean` | MULH, MULHSU, DIV, DIVW, DIVUW, REM, REMW, REMUW (8) | K2 + K3 + K4 + ArithTable signed witnesses (shipped, Track P) |

**Total opcodes addressed in this branch: 27.**

Note on K2: derivation lemmas in this branch consume K2's structural
form. Trust on `register_*_lanes_match` is propagated up to the
top-level driver / GoldenTraces fixture, exactly as it is today for
the operation-bus `matches_entry`. Concrete content of K2 closure
graduates with `finishing2.md`.

### Phase 3 — cleanup

For each of the 27 `Equivalence/<Op>.lean` files in scope:

1. Remove `h_rd_val :` from each metaplan theorem signature
   (`_metaplan`, `_metaplan_from_bus`, `_metaplan_bus_self`,
   `_metaplan_op_bus`).
2. Replace its call site with the appropriate
   `h_rd_val_<archetype>_<op> ...` discharge lemma from Phase 2.
3. Add the new circuit-hypothesis parameters the discharge lemma
   needs (typically already supplied by GoldenTraces / top-level
   driver).

Best dispatched as one subagent per archetype.

## Verification gates

```bash
# Phase 2 sub-tracks
cd ZiskFv
lake build ZiskFv.Equivalence.RdValDerivation.Arith
lake build ZiskFv.Equivalence.RdValDerivation.JumpUType
lake build ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned
lake build ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned

# Phase 3 grep gate (excluding the 13 Logic/Shift opcodes deferred to finishing2)
for op in Add Addi Addiw Addw Sub Subw Slt Sltu Slti Sltiu \
          Jal Jalr Lui Auipc \
          Mul MulHU Divu Remu MulW \
          MulH MulHSU Div Divw Divuw Rem Remw Remuw; do
  echo -n "$op: " ; grep -c 'h_rd_val :' "ZiskFv/ZiskFv/Equivalence/${op}.lean" || echo 0
done
# expected: 0 for each

# Final: full package + linter-clean
cd ZiskFv && lake build
```

## Out of scope for this branch

| Item | Why deferred | Where it goes |
|---|---|---|
| K1-B (AND/OR/XOR PackedCorrect) | needs `Valid_Binary` (AIR not extracted) | finishing2 |
| K1-C (Shift + SLT PackedCorrect) | needs `Valid_BinaryExtension` (AIR not extracted) | finishing2 |
| N-ALU-Binary derivation (~21 opcodes) | needs K1-B + K1-C | finishing2 |
| Phase 3 cleanup for Logic/Shift opcodes | needs the above | finishing2 |
| K2 Layer-2 closure | extraction gap + slot-shape shim | finishing2 |
| Loads / Stores `h_rd_val` retirement | plan explicitly defers; needs Mem AIR | finishing3 (TBD) |
| Branch opcodes | don't write rd; `h_rd_val` not applicable | n/a |

## Status / next action

- Phase 1 keystones complete (K2 with documented gap).
- **Next step:** dispatch Phase 2 derivation subagents (one per
  archetype, can run in parallel since each writes a distinct new file).
- After Phase 2 verifies, Phase 3 cleanup (one subagent per archetype).
- After full grep gate passes for the 27 in-scope opcodes, close the
  branch and move to `finishing2.md`.
