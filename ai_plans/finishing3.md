# finishing3 — Loads / stores circuit-correctness (Mem + MemAlign extraction)

**Branch:** TBD (likely `feature/zisk-fv-mem-closure`).
**Predecessor:** `finishing2.md`. By the time this starts, all integer
+ multiplicative + jump + U-type opcodes have full `h_rd_val`-retired
equivalence proofs.

## Goal

Retire the trusted memory-model axioms (`M1`, `M2`, `M4`, `M10`, …
catalogued in `docs/fv/trusted-base.md`) from per-opcode load / store
equivalence theorems by extracting and bridging the `Mem` AIR + the
`MemAlign*` family, producing per-opcode load / store proofs whose
trusted base reduces to the same shape as ALU proofs (transpile
contract + PIL↔Lean model fidelity).

## Trust scoping (project-wide)

This project **assumes proving-system correctness.** That is:
- PLONK-style soundness for plookup, logUp, and permutation arguments
  is taken as given, not proven in Lean.
- Range-check enforcement (via `SpecifiedRanges`, `VirtualTable0/1`)
  is automatic — per-opcode range hypotheses are discharged by the
  lookup arguments downstream.
- Bus-protocol delivery (operation-bus `matches_entry`, memory-bus
  `h_emit`) is automatic — multiset equality of emit/consume sites
  is delivered by the permutation argument.

Under this scoping, the **remaining trust gaps** that finishing3
addresses are:
1. "The Mem / MemAlign* AIRs' row constraints faithfully model the
   memory protocol Sail expects." (Closed by extracting + bridging
   each AIR.)
2. The hand-written named-column projections match what PIL emits.
   (Standard pattern; same trust class as `opBus_row_Main`.)

What this project *does not aim to close*:
- PLONK / plookup / logUp / permutation soundness as Lean theorems
  (would be `finishing4` if it existed; cut by trust scoping).
- Transpile contract `riscv2zisk_context.rs` ↔ `Fundamentals.Transpiler`.
  Per CLAUDE.md, this is **trusted surface**.
- Top-level "ZisK execution ≅ Sail interpreter" theorem. The
  metaplan's stated goal is **per-opcode**.

## What's trusted today (before this branch)

`docs/fv/trusted-base.md` enumerates the "M-family" axioms — one per
load / store opcode. Each says, in essence, "the memory bus delivers
what Sail's memory monad would have." Concretely, each per-opcode
load/store theorem currently has either a parameterized
`h_bus_execute_matches_sail` (the monolithic form) or its decomposed
byte-level `h_rd_val` siblings (the Phase 4.5 A-rewire form for
`LoadD`).

The opcodes affected (from `Equivalence/`):
- **Loads (7):** LD (`LoadD`), LW, LWU, LH, LHU, LB, LBU.
  (`Lw`, `LoadWU`, `Lh`, `LoadHU`, `Lb`, `LoadBU`.)
- **Stores (4):** SD (`StoreD`), SW (`StoreW`), SH (`StoreH`),
  SB (`StoreB`).

Plus the `register_write_lanes_match` residual from `finishing2.md`'s
S3.3 — the destination-write side of K2 that has no F-typed Main
emission. Under the trust-scoping above, this becomes derivable:
"Main emits new value at step S" + (assumed) permutation soundness +
"next register-read at step S' > S consumes value V" pins the write
through Mem's multiset model. Closing it needs Mem AIR + a multi-row
argument (option (d) in finishing2.md S3).

## Scope items

### S1. Extract `Mem` AIR

**ZisK details.** Pilout idx 2. 34 constraints, 415 exprs. Models
RV64IM's memory state machine: each row is one memory-bus entry
(read or write at some step / address) with a continuity constraint
linking consecutive entries at the same address.

**Files to author:**

| File | Mirror of | Notes |
|---|---|---|
| `ZiskFv/Extraction/Mem.lean` | `Extraction/BinaryAdd.lean` | auto-generated via `tools/zisk-pil-extract --air Mem` |
| `ZiskFv/Extraction/Mem.hand.lean` | `Extraction/BinaryAdd.hand.lean` | oracle copy |
| `ZiskFv/Airs/Mem.lean` | `Airs/Binary/BinaryAdd.lean` | named-column `Valid_Mem` wrapper + per-constraint bridge lemmas |

`Mem` is ~2× larger than `BinaryAdd` by exprs (415 vs 198) but the
same shape. Expect ~300-line `Extraction/Mem.lean`, ~200-line
`Airs/Mem.lean`.

### S2. Extract `MemAlign` family (4 AIRs)

The four MemAlign* AIRs handle unaligned-access decomposition: a
single RV-level unaligned load/store gets split into multiple
aligned `Mem` operations. Sail's `read_xreg` / `write_xreg` /
`mem_read` / `mem_write` operate at the byte level; the alignment
shim bridges that to ZisK's multi-byte-lane Mem AIR.

**Files to author** (per AIR):

| AIR | Constraints | Files |
|---|---|---|
| MemAlign | 40 | `Extraction/MemAlign.lean`, `Airs/MemAlign.lean` |
| MemAlignByte | 16 | `Extraction/MemAlignByte.lean`, `Airs/MemAlignByte.lean` |
| MemAlignReadByte | 10 | `Extraction/MemAlignReadByte.lean`, `Airs/MemAlignReadByte.lean` |
| MemAlignWriteByte | 15 | `Extraction/MemAlignWriteByte.lean`, `Airs/MemAlignWriteByte.lean` |

**Open question — RV64IM unaligned access.** The Sail RV64IM
specification's stance on unaligned memory access (allowed with
slowdown, vs. trap) needs to be determined and the bridge written
to match. If Sail's per-opcode model assumes aligned access only,
the MemAlign* extractions become "soundness scaffolding only" — the
load/store equivalence proofs may not invoke them directly. This
question must be resolved before authoring S3 below.

### S3. Memory-model bridge

**Files to author:**

| File | Purpose |
|---|---|
| `ZiskFv/Spec/MemModel.lean` | composes Mem + MemAlign* row constraints with Sail's memory-monad semantics. Provides the lemmas that retire each `M*` axiom. |
| `ZiskFv/Airs/MemoryBus/MemBridge.lean` | bridges Main-side memory-bus lane-match (`memory_load_lanes_match`, `memory_store_lanes_match` from `Airs/MemoryBus.lean`) to Mem-side row constraints — i.e., closes the `h_emit`-style hypothesis for memory-bus entries. |

**Sub-lemmas needed:**
- `mem_load_correct`: given Mem row constraints + permutation match,
  the `MemoryBusEntry` produced on a load consumes the value Sail's
  `mem_read` would return.
- `mem_store_correct`: dual for stores.
- `memalign_load_correct` / `memalign_store_correct`: alignment-shim
  variants if S2 introduces them.

### S4. **K2 — final correct resolution**

This is the explicit closing act for K2. After this section ships,
all three K2 lane-match theorems
(`register_read_rs1_lanes_match_of_bus_emission`,
`register_read_rs2_lanes_match_of_bus_emission`,
`register_write_lanes_match_of_bus_emission`) are proper Layer-2
derivations — none of them is the structurally-trivial `.symm` form
that `2c627ac` shipped.

The reads side (rs1, rs2) ships in `finishing2.md` S3 against the
F-typed extracted memory-bus emissions `bus_emission_Main_0`,
`bus_emission_Main_2`. The writes side has **no F-typed Main bus
emission** (ZisK's memory protocol enforces register-writes
implicitly via the next read's `prev_value` field), so it cannot
be slot-matched directly against a Main emission. The proper
closure is a multi-row argument that needs the Mem AIR's row
constraints — which is why this section sits in finishing3, after
S1 extracts the Mem AIR.

**Argument shape:**
- Main row R writes value V to register at offset off (encoded in
  Main's `c_0`, `c_1` lanes; pinned via `store_offset` column 24).
- Permutation soundness (assumed): every "store-reg" emission on
  bus_id=10 has a unique paired "load-reg-prev" consume.
- Mem AIR's row constraints + the consuming load's `prev_value`
  field carry V forward.
- Therefore `register_write_lanes_match m row e` holds for the
  appropriate `e` constructed from Main's columns.

**File:** new theorem in `Airs/MemoryBus/LaneMatch.lean` (or a
`MemoryBus/RegisterWrite.lean` sibling).

### S5. Per-opcode cleanup

For each of the 11 load / store opcodes:

1. Remove `h_bus_execute_matches_sail` (and its decomposed
   `h_rd_val` siblings for `LoadD`) from metaplan theorem signatures.
2. Replace its call sites with the appropriate discharge lemma from
   S3.
3. Add the new circuit-hypothesis parameters as needed (Mem +
   MemAlign* row constraints).
4. Drop the corresponding M-axiom from `trusted-base.md`.

## Verification gates

```bash
# After S1
cd ZiskFv
lake build ZiskFv.Airs.Mem

# After S2
lake build ZiskFv.Airs.MemAlign
lake build ZiskFv.Airs.MemAlignByte
lake build ZiskFv.Airs.MemAlignReadByte
lake build ZiskFv.Airs.MemAlignWriteByte

# After S3
lake build ZiskFv.Spec.MemModel
lake build ZiskFv.Airs.MemoryBus.MemBridge

# After S5 — full grep gate over loads / stores
git grep -n 'h_bus_execute_matches_sail\|h_rd_val :' \
    ZiskFv/ZiskFv/Equivalence/Lb.lean \
    ZiskFv/ZiskFv/Equivalence/Lh.lean \
    ZiskFv/ZiskFv/Equivalence/Lw.lean \
    ZiskFv/ZiskFv/Equivalence/LoadBU.lean \
    ZiskFv/ZiskFv/Equivalence/LoadHU.lean \
    ZiskFv/ZiskFv/Equivalence/LoadWU.lean \
    ZiskFv/ZiskFv/Equivalence/LoadD.lean \
    ZiskFv/ZiskFv/Equivalence/StoreB.lean \
    ZiskFv/ZiskFv/Equivalence/StoreH.lean \
    ZiskFv/ZiskFv/Equivalence/StoreW.lean \
    ZiskFv/ZiskFv/Equivalence/StoreD.lean
# expected: 0 hits

# Final
cd ZiskFv && lake build
```

## After this branch closes

Combined with `finishing1` + `finishing2`, the project's per-opcode
equivalence theorems for **all of RV64IM** have only the following
trusted base remaining:

1. **Transpile contract** — `Fundamentals.Transpiler.transpile_<OP>`
   axioms (CLAUDE.md "trusted surface").
2. **PIL ↔ Lean model fidelity** — that the auto-extracted
   `Extraction/<X>.lean` files faithfully render the pilout, and
   that the hand-written `Airs/*` named-column wrappers match the
   raw extraction.
3. **Proving-system correctness** — PLONK / plookup / logUp /
   permutation soundness as the meta-claim (cut from scope).

The metaplan's stated goal is met when finishing1 + 2 + 3 are
closed: each in-scope RV64IM opcode has a per-opcode equivalence
theorem `execute_instruction <op-shape> state = (bus_effect ...
state).2` whose proof depends only on items 1–3.

## Status / next action

- Branch not started. Wait for `finishing2.md` to close.
- **Recommended order:** S1 + S2 in parallel (independent AIR
  extractions; S2's four MemAlign* AIRs can also parallelize).
  Resolve the unaligned-access question (S2 paragraph) before S3.
  Then S3 + S4 (S4 may parallelize with S3 since the Mem AIR is the
  only shared dependency). Then S5 cleanup.
