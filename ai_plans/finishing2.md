# finishing2 — Binary + BinaryExtension AIR extraction; ALU/W/Logic/Shift Tier-1

**Branch:** TBD (likely `feature/track-n2-binary-extension`).
**Predecessor:** `finishing1.md` closes Track N for ADD, LUI, ADDI,
SUB. This plan handles everything that branch deferred whose blocker
is **the missing `Binary` and/or `BinaryExtension` AIR extraction**.

## Goal — h_rd_val Tier-1 retirement for 25 opcodes

| Archetype | Opcodes (count) | Why deferred from finishing1 |
|---|---|---|
| ALU-Sub | SUB (1) | bus opcode `OP_SUB = 11` ≠ BinaryAdd's `OP_ADD = 10`; routes through `Binary` AIR's additive path |
| ALU-W | ADDW, ADDIW, SUBW (3) | route through `BinaryExtension`'s additive path |
| Logic | AND, ANDI, OR, ORI, XOR, XORI (6) | route through `Binary`'s logical-op path |
| Shift | SLL, SLLI, SLLW, SLLIW, SRL, SRLI, SRLW, SRLIW, SRA, SRAI, SRAW, SRAIW (12) | route through `BinaryExtension`'s shift path |
| Compare | SLT, SLTU, SLTI, SLTIU (4) | route through `Binary`'s compare-conclusion path |

Plus K2 reads-side Layer-2 closure (writes-side continues to
finishing3 since it needs the `Mem` AIR).

Work decomposes into: (a) extract `Binary` AIR; (b) extract
`BinaryExtension` AIR; (c) author K1-B / K1-C `PackedCorrect` lifts +
the corresponding `_compositional_with_<X>` Spec lemmas;
(d) Tier-1 discharge lemmas in `Equivalence/RdValDerivation/`;
(e) Phase-3 cleanup; (f) K2 reads-side closure.

**Total scope: 26 opcodes** (1 SUB + 3 ALU-W + 6 Logic + 12 Shift + 4 Compare).

## Architectural prerequisite — trust binary lookup tables

After running `zisk-pil-extract` on `Binary` and `BinaryExtension`, we
discovered both AIRs encode their byte-level semantics as **lookup
arguments against virtual fixed tables** (`bus_id=125 BinaryTable`,
`bus_id=124 BinaryExtensionTable`), not as F-typed polynomial
constraints:

* `Binary` (idx 10, 14 constraints): only constraints 0–6 are F-typed
  — booleanity / linearity for the flag columns. Constraints 7–13
  are 8 lookup arguments, one per byte, against `bus_id=125`.
* `BinaryExtension` (idx 12, 8 constraints): **zero** F-typed
  constraints. All 8 are lookups against `bus_id=124`.

This means the K1-B / K1-C BitVec lifts cannot be derived from
extracted F-typed constraints alone; the byte-level relation lives in
the lookup. Two options were considered:

* **(A) Trust the table contents**, mirroring openvm-fv's
  `BitwiseBusEntry` / `RangeTupleCheckerBus` pattern in
  `OpenvmFv/Fundamentals/Interaction.lean`: define a `BusEntry`-style
  contract whose `wf_properties` baking-in the per-op switch from
  `binary_table.pil`. Trusted at the bus-entry definition site.
* **(B) Prove the table** by porting the PIL2 generator switch to
  Lean and verifying each branch.

We pick **(A)**, matching the openvm-fv template (which never proves
its bitwise / range-check / program-bus tables; their semantics are
trusted axioms in the `BusEntry` instance). Trust grows by **two new
bus contracts** — same shape as today's `OperationBus.matches_entry`.
Documented in CLAUDE.md alongside the other trusted-surface items.

(Improving (A) → (B) later by porting the PIL switch is straightforward
and doesn't change downstream proofs — only retires axioms.)

## Scope items

### S0. Trusted bus contracts for the binary tables

**Files to author:**

| File | Notes |
|---|---|
| `ZiskFv/Airs/BinaryTable.lean` | `BinaryTableEntry F` 7-slot structure `(pos_ind, op, a, b, cin, c, flags)`; `binTable_row_Binary_byte_i` projection (`Valid_Binary` row → byte-i `BinaryTableEntry`); `bin_table_consumer_wf` Prop = the trusted per-op switch from `vendor/zisk/state-machines/binary/pil/binary_table.pil` (case-split on `op` literal: AND → `c = a &&& b`; OR → `c = a ||| b`; XOR → `c = a ^^^ b`; LT/LTU/EQ/etc. → cout-as-bool semantics; range conditions on a/b/c). Mirrors openvm-fv's `BitwiseBusEntryInstance.wf_properties`. |
| `ZiskFv/Airs/BinaryExtensionTable.lean` | `BinaryExtensionTableEntry F` 7-slot structure `(op, byte_index, a_byte, shift_amount, c_lo_byte, c_hi_byte, op_is_shift)`; `binExtTable_row_BinaryExtension_byte_i` projection; `bin_ext_table_consumer_wf` Prop = trusted shift-byte semantics from `binary_extension_table.pil` (SLL → `c[i] := a[i] << shift_amount` byte-projected; SRL/SRA → analogous). |

These files contain **only definitions and trusted-surface props** — no
proofs of the `wf_properties`. Both are added to the trusted-surface
list in `CLAUDE.md`.

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
| `ZiskFv/Airs/Binary/BinaryPackedCorrect.lean` | `Airs/Binary/BinaryAddPackedCorrect.lean` | (a.k.a. K1-B+SLT-half-of-K1-C) BitVec lifts: AND/OR/XOR conclude `BitVec.{and,or,xor} 64`; SLT(U) concludes signed/unsigned compare → 0/1. **Derives the byte-level relation from S0's `bin_table_consumer_wf`** (assumed at consumer multiplicity = 1) plus the F-typed booleanity constraints on the auxiliary flags. The 8 byte-tuples are reassembled into 64-bit BitVec lifts via `Fundamentals/PackedBitVec/NoWrap.lean`'s machinery. |

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
| `ZiskFv/Airs/Binary/BinaryExtensionPackedCorrect.lean` | `Airs/Binary/BinaryAddPackedCorrect.lean` | Shift-half-of-K1-C: BitVec lifts for `shiftLeft`, `ushiftRight`, `sshiftRight`. **Derives entirely from S0's `bin_ext_table_consumer_wf`** (consumer-side trust at multiplicity 1) — `BinaryExtension` has zero F-typed constraints, so no booleanity supplements are needed. |

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
| N-ALU-Binary-Sub | `Equivalence/RdValDerivation/Arith.lean` (extends finishing1's file) | SUB (1) | K1-B subtractive path or analog Spec lemma against `Binary` AIR + K2 |
| N-ALU-Binary-Logic | `Equivalence/RdValDerivation/BinaryLogic.lean` | AND, ANDI, OR, ORI, XOR, XORI (6) | K1-B (S1) + K2 reads (S3) + Spec field identity for AND/OR/XOR (author if not shipped) |
| N-ALU-Binary-Shift | `Equivalence/RdValDerivation/BinaryShift.lean` | SLL, SLLI, SLLW, SLLIW, SRL, SRLI, SRLW, SRLIW, SRA, SRAI, SRAW, SRAIW (12) | K1-C (S2) + K2 |
| N-ALU-Binary-Compare | `Equivalence/RdValDerivation/BinaryCompare.lean` | SLT, SLTU, SLTI, SLTIU (4) — **pulled from finishing1** | K1-B compare-conclusion path + K2; Spec field identity for compare |
| N-ALU-Binary-W | `Equivalence/RdValDerivation/Arith.lean` (extends finishing1's file) | ADDW, ADDIW, SUBW (3) | K1-C additive path + K2 |

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
# After S0 (trusted bus contracts)
cd ZiskFv
lake build ZiskFv.Airs.BinaryTable
lake build ZiskFv.Airs.BinaryExtensionTable

# After S1 (Binary)
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
| Proving `BinaryTable` / `BinaryExtensionTable` `wf_properties` from the PIL2 generator (port the `binary_table.pil` switch to Lean) | optional improvement; trusted in `S0` for now per the openvm-fv pattern | future finishing pass |
| Top-level "ZisK execution ≅ Sail interpreter" theorem | per-opcode goal does not require it | finishing3 |
| Transpile contract derivation (riscv2zisk_context.rs port) | trusted surface per CLAUDE.md | finishing3 |

## Status / next action

- Branch: `feature/track-n-h-rd-val` (continues finishing1's worktree).
- **Recommended order:** **S0 first** (trusted bus contracts — small,
  unblocks everything). Then S1 + S2 in parallel (independent AIR
  extractions; both depend on S0). S3 in parallel with S1/S2 (different
  files entirely). Then S4 (gated on S1/S2/S3). Then S5 cleanup.
