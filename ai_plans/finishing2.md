# finishing2 — Unextracted-AIR follow-on (Binary, BinaryExtension, K2)

**Branch:** TBD (likely `feature/track-n2-unextracted-airs`).
**Predecessor:** `finishing1.md` closes Track N for the 27 opcodes whose
AIRs are already extracted; this plan handles everything that branch
deferred.

## Goal

Close the three trust / extraction gaps that block:

1. **Tier-1 derivation** (per `finishing1.md`'s revised goal — actual
   trust retirement, not byte-sum rephrasing) for the remaining
   17 RV64IM ALU opcodes whose secondary AIR isn't extracted yet.
   This is **4 SLT-family** opcodes (pulled out of `finishing1` because
   their Tier-1 needs `Binary`) plus ~13 Logic/Shift opcodes.
2. K2's structurally-trivial form (Layer 1) → properly
   slot-match-derived (Layer 2), reads-side only. Writes-side
   continues to finishing3.

Work decomposes into: (a) extract the two missing AIRs (`Binary`,
`BinaryExtension`); (b) ship K1-B / K1-C `PackedCorrect` lifts; (c)
ship Tier-1 discharge lemmas in `Equivalence/RdValDerivation/`; (d)
Phase-3 cleanup of the affected `Equivalence/<Op>.lean` files; (e)
K2 reads-side closure.

## Scope items

### S1. Extract `Binary` AIR

**ZisK details.** Pilout idx 10. 14 constraints, 1049 exprs. Handles
RV64IM logic + compare opcodes (AND/OR/XOR + their I-immediates;
SLT/SLTU and their I-immediates).

**Files to author:**

| File | Mirror of | Notes |
|---|---|---|
| `ZiskFv/Extraction/Binary.lean` | `Extraction/BinaryAdd.lean` | auto-generated via `tools/zisk-pil-extract --air Binary` |
| `ZiskFv/Extraction/Binary.hand.lean` | `Extraction/BinaryAdd.hand.lean` | oracle copy for diff-check by `verify-phase*` |
| `ZiskFv/Airs/Binary/Binary.lean` | `Airs/Binary/BinaryAdd.lean` | named-column `Valid_Binary` wrapper + per-constraint bridge lemmas |
| `ZiskFv/Airs/Binary/BinaryPackedCorrect.lean` | `Airs/Binary/BinaryAddPackedCorrect.lean` | (a.k.a. K1-B+SLT-half-of-K1-C) BitVec lifts: AND/OR/XOR conclude `BitVec.{and,or,xor} 64`; SLT(U) concludes signed/unsigned compare → 0/1 |

`tools/zisk-pil-extract` already handles this AIR — same template as
the existing `BinaryAdd` extraction (which is 9 constraints / 198
exprs / ~150 lines). `Binary` is ~5× larger by exprs but the same
shape; expect a ~400-600 line `Extraction/Binary.lean`.

### S2. Extract `BinaryExtension` AIR

**ZisK details.** Pilout idx 12. 8 constraints, 830 exprs. Handles
shifts (SLL/SRL/SRA + I-immediates + W variants) and sign-extension
for *W byte/half/word loads.

**Files to author:**

| File | Mirror of | Notes |
|---|---|---|
| `ZiskFv/Extraction/BinaryExtension.lean` | `Extraction/BinaryAdd.lean` | auto-generated |
| `ZiskFv/Extraction/BinaryExtension.hand.lean` | `Extraction/BinaryAdd.hand.lean` | oracle copy |
| `ZiskFv/Airs/Binary/BinaryExtension.lean` | `Airs/Binary/BinaryAdd.lean` | `Valid_BinaryExtension` |
| `ZiskFv/Airs/Binary/BinaryExtensionPackedCorrect.lean` | `Airs/Binary/BinaryAddPackedCorrect.lean` | Shift-half-of-K1-C: BitVec lifts for `shiftLeft`, `ushiftRight`, `sshiftRight` |

### S3. Close K2 (Layer-2 memory-bus lane-match)

**Three sub-pieces:**

**S3.1.** Extend `Extraction/Buses.lean` (or new `Extraction/MemoryBuses.lean`)
with the F-typed memory-bus emissions for Main:
* `bus_emission_Main_mem_0` (rs1 register-read)
* `bus_emission_Main_mem_2` (rs2 register-read)
* `bus_emission_Main_mem_4` (store-reg previous-value read)

The extractor produces these directly; `tools/zisk-pil-extract --air Main --bus-emissions --bus-id=10 --skip-unsupported` already works. Copy
the three non-skipped specs into the file (the rest stay
multiplicity=0 stubs, fine).

**S3.2.** Author hand-written named-column projections in
`Airs/MemoryBus.lean` (or a new `Airs/MemoryBus/Projection.lean`):

```lean
def memBus_row_Main_register_read_rs1 (m : Valid_Main C F ExtF) (row : ℕ)
    : MemoryBusEntry F  -- or a new MemoryBusEntry6 with 6 slots
def memBus_row_Main_register_read_rs2 ...
def memBus_row_Main_store_reg_prev   ...
```

**Resolve slot-shape mismatch.** PIL emits 6-slot
`[op, addr, mem_step, bytes, value_lo, value_hi]` with 32-bit lane
values. Existing `MemoryBusEntry` is 12-slot with 8 byte lanes. Two
options:

- **(a)** Introduce `MemoryBusEntry6` for the register-bus path; keep
  `MemoryBusEntry` (12-slot byte form) for the memory-load /
  memory-store paths that go through MemAlign* downstream byte
  decomposition. Bridge: an "explode lo/hi 32-bit lanes into 4 bytes
  each" lemma.
- **(b)** Keep `MemoryBusEntry` and have the projections set
  `x0..x3 = byte-decomposition of value_lo`, `x4..x7 = byte-decomposition
  of value_hi`. Adds byte-range hypotheses to the slot-match path but
  matches the existing API.

Pick (a) if it makes the proof shorter; (b) is what existing callers
expect.

**S3.3.** Slot-match lemmas in a new `Airs/MemoryBus/BusShape.lean`,
mirroring `Airs/BusShape.lean`:

```lean
theorem bus_emission_main_slots_match_memBus_row_Main_register_read_rs1
    (m : Valid_Main C F ExtF) (row : ℕ) : ...
-- + register_read_rs2, store_reg_prev variants
```

Then rewrite `Airs/MemoryBus/LaneMatch.lean`'s three theorems to
derive lane-match from slot-match (replacing the trivial `.symm`
proofs with proper bus-shape compositions).

**Known residual gap (writes side):** `register_write_lanes_match`
has **no F-typed Main bus emission** — destination-write isn't
directly emitted; ZisK's memory protocol consistency-checks via the
*next* read's `prev_value` field. Closing it requires the Mem AIR
+ a multi-row argument.

That work is **explicitly scoped to `finishing3.md` S4** — it
needs the Mem AIR extraction (which finishing3 S1 ships) and is
the natural closing act for K2 once Mem is available.

Within this branch (`finishing2`), the writes-side theorem stays at
Layer 1 (the structural form `2c627ac` shipped). Document the
deferral in `docs/fv/track-n-traps.md`.

### S4. Phase 2.5 — Tier-1 derivation lemmas

After S1 + S2 ship, dispatch Tier-1 discharge lemmas — discharging
`h_rd_val` from circuit primitives (Spec field identity + K1-B/C
BitVec lift + byte decomposition + lane-match), not as a byte-sum
parameter. Same pattern as `finishing1.md`'s Phase 2.5.

| Archetype | File | Opcodes | Deps |
|---|---|---|---|
| N-ALU-Binary-Logic | `Equivalence/RdValDerivation/BinaryLogic.lean` | AND, ANDI, OR, ORI, XOR, XORI (6) | K1-B (S1) + K2 reads (S3) + Spec field identity for AND/OR/XOR (author if not shipped) |
| N-ALU-Binary-Shift | `Equivalence/RdValDerivation/BinaryShift.lean` | SLL, SLLI, SLLW, SLLIW, SRL, SRLI, SRLW, SRLIW, SRA, SRAI, SRAW, SRAIW (12) | K1-C (S2) + K2 |
| N-ALU-Binary-Compare | `Equivalence/RdValDerivation/BinaryCompare.lean` | SLT, SLTU, SLTI, SLTIU (4) — **pulled from finishing1** | K1-B compare-conclusion path + K2; Spec field identity for compare |

**Note on SLT routing:** confirmed via `BusShape.lean::bus_shape_for_SLT`
that SLT/SLTU dispatch on `op_lit = 7` (OP_LT) / `op_lit = 6`
(OP_LTU), `is_external_op = 1`, `m32 = 0`. The proves-side is the
`Binary` AIR (per the bus-emitter list). So K1-B's compare branch is
the BitVec lift these need.

### S5. Phase 3 — cleanup

For each of the **17 Logic/Shift/Compare opcodes** (12 Shift + 6
Logic - 1 carryover... actually 4 SLT-family + 6 Logic + 12 Shift =
22; resolve duplicates: SLLI/SRLI/SRAI overlap; final = AND, ANDI,
OR, ORI, XOR, XORI, SLL, SLLI, SLLW, SLLIW, SRL, SRLI, SRLW, SRLIW,
SRA, SRAI, SRAW, SRAIW, SLT, SLTU, SLTI, SLTIU = 22 opcodes):

1. Remove `h_rd_val :` from metaplan theorem signatures.
2. Replace call sites with the Tier-1 discharge lemma from S4 (a
   real circuit-derived theorem, not a byte-sum wrapper).
3. Add the new circuit-hypothesis parameters the Tier-1 lemma
   requires (Main + Binary / BinaryExtension constraints, byte
   ranges, lane-match — same shape as finishing1's Phase 3).

## Verification gates

```bash
# After S1 (Binary)
cd ZiskFv
lake build ZiskFv.Airs.Binary.Binary
lake build ZiskFv.Airs.Binary.BinaryPackedCorrect

# After S2 (BinaryExtension)
lake build ZiskFv.Airs.Binary.BinaryExtension
lake build ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect

# After S3 (K2 closure)
lake build ZiskFv.Airs.MemoryBus.LaneMatch
# manual: confirm proofs in LaneMatch.lean are no longer trivial .symm chains

# After S4 (derivations)
lake build ZiskFv.Equivalence.RdValDerivation.BinaryLogic
lake build ZiskFv.Equivalence.RdValDerivation.BinaryShift

# After S5 (cleanup) — full grep gate over ALL h_rd_val opcodes (combining
# finishing1 + finishing2 scope, excluding loads/stores per finishing3)
git grep -n 'h_rd_val' ZiskFv/ZiskFv/Equivalence/ \
  | grep -vE '(LoadD|Lw|Lh|Lb|LoadHU|LoadBU|LoadWU|StoreD|StoreW|StoreH|StoreB)\.lean'
# expected: 0 hits

# Final: full package + linter-clean
cd ZiskFv && lake build
```

## Out of scope for this branch

| Item | Why deferred | Where |
|---|---|---|
| Loads / Stores `h_rd_val` retirement | needs Mem AIR + memory-model closure | finishing3 |
| `register_write_lanes_match` Layer-2 closure (option (d) above) | needs Mem AIR multi-row argument | finishing3 |
| Range-check soundness (SpecifiedRanges, VirtualTable) | infra-AIR closure work | finishing3 |
| Permutation-soundness Lean theorem | bus-protocol math | finishing3 |
| Top-level "ZisK execution ≅ Sail interpreter" theorem | per-opcode goal does not require it | finishing3 |
| Transpile contract derivation (riscv2zisk_context.rs port) | trusted surface per CLAUDE.md | finishing3 |

## Status / next action

- Branch not yet started. Wait for `finishing1.md` to close.
- **Recommended order:** S1 + S2 in parallel (independent AIR
  extractions). S3 in parallel with S1/S2 (different files entirely).
  Then S4 (gated on S1/S2/S3). Then S5 cleanup.
