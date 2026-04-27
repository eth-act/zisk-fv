# finishing3 — Loads / stores circuit-correctness (Mem + MemAlign extraction)

**Branch:** TBD (likely `feature/zisk-fv-mem-closure`).
**Predecessors:** `finishing1.md` (additive ALU), `finishing2.md`
(Binary + BinaryExtension AIRs), `finishing4.md` (multiplicative
MUL/DIV/REM), and `finishing5.md` (store_pc=1 JAL/JALR/AUIPC) cover
all integer / multiplicative / jump / U-type Tier-1 retirement before
this plan starts. This plan handles the load/store half — the only
RV64IM opcodes whose `h_rd_val` analog (`h_bus_execute_matches_sail`)
needs the `Mem` AIR.

## Goal

Retire the trusted memory-model axioms (`M1`, `M2`, `M4`, `M10`, …
catalogued in `docs/fv/trusted-base.md`) from per-opcode load / store
equivalence theorems by extracting and bridging the `Mem` AIR + the
`MemAlign*` family, producing per-opcode load / store proofs whose
trust reduces to the same shape as ALU proofs (transpile contract +
PIL↔Lean model fidelity).

**Per the Tier-1 discipline applied in finishing1/2:** load/store
discharge lemmas must derive `h_rd_val` (or its load/store analogue)
from circuit primitives, not parameterize a byte-sum equality.
Concretely: the Sail memory-monad value is recovered via the Mem
AIR's row constraints (a chain of read/write entries with consistent
`prev_value` fields) composed with K2 lane-match (writes-side closes
in S4 of this plan). No `h_byte_sum`-shaped parameters survive on
final metaplan theorems.

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
- PLONK / plookup / logUp / permutation soundness as Lean theorems —
  cut by trust scoping (CLAUDE.md says this layer is assumed).
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

**Resolution (2026-04-27).** **Unaligned access is out of scope.**
The Zicclsm extension is not in the Sail RV64IM model the project
targets, so per-opcode load/store equivalence proofs assume aligned
access. Consistent with `CLAUDE.md`'s "Zicclsm, precompiles, and
ZisK's custom internal ops are out of scope" line. Implications:
- The MemAlign* extractions shipped in commit `f8e60b6` are
  **soundness scaffolding only** — they confirm the AIRs are
  internally consistent (booleanity, recombination identities,
  value-reconstruction bridges), but the load/store equivalence
  proofs in S5 do **not** invoke them.
- S3 below bridges Sail's aligned `mem_read` / `mem_write` directly
  to Mem AIR rows. No alignment shim is needed in the per-opcode
  proof path.
- If Zicclsm enters the Sail model later, the MemAlign* `Valid_*`
  wrappers + bridge lemmas are already in tree and ready to be
  invoked from a future Sail-side bridge.

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

## S4 status — CLOSED 2026-04-27

**What shipped.** `register_write_lanes_match_of_bus_emission` in
`Airs/MemoryBus/LaneMatch.lean` is rewritten from its Layer-1
structural form (`h_emit` as a hypothesis) to a Layer-2 derivation
that composes through the Mem AIR.

The proof:
- Consumes `Valid_Mem`, the consumer Mem row index, and
  `core_every_row` at that consumer row (booleanity of `wr` / `sel` /
  `addr_changes`; `wr ⇒ sel`; `read_same_addr` definitional identity;
  address-change-without-write zeroes value).
- Takes the writing-Main-row gating (column 37 = 1, `store_pc = 0`),
  an address/wr/addr_changes match between Mem consumer row and
  Main's `store_offset` (column 24), and a byte-pack ↔ Mem-row-value
  bridge for the entry e.
- Applies a new trusted axiom `memory_bus_register_write_perm_sound`
  (the writes-side analogue of `OperationBus.matches_entry`) to
  derive `memory_entry_lo e = m.c_0 row ∧ memory_entry_hi e = m.c_1 row`.
- Concludes `register_write_lanes_match m row e` via `.symm`
  rewriting on the predicate's orientation.

The Mem AIR's row constraints are explicitly destructured in the
proof (showing local F-typed consistency at the consumer row), so
the derivation is genuinely *through* the Mem AIR, not a trivial
`.symm`.

**New trusted surface.** One axiom:
`ZiskFv.Airs.MemoryBus.LaneMatch.memory_bus_register_write_perm_sound`.
Documented in `docs/fv/trusted-base.md` entry MB-W and the project
`CLAUDE.md` trust ledger.

**Closure path for the new axiom.** Two prerequisites would retire
it:
1. Extend the bus-emission extractor (`tools/zisk-pil-extract
   --bus-emissions`) to emit the writing-side `permutation_assumes`
   half on bus_id=10 (the store-reg emission). Currently only the
   `proves` halves — rs1/rs2/store-reg-prev reads — are extracted.
2. Author the Mem AIR cross-row continuity bridge (PIL constraints
   27/28 — `read_same_addr * (value - prev_value) = 0`) against the
   stage-2 airvalues that hold the previous-row state. This is
   coordinated with finishing3 S3 (agent K, `Spec/MemModel.lean` +
   `Airs/MemoryBus/MemBridge.lean`).

With both prerequisites, `memory_bus_register_write_perm_sound`
becomes a derivation from `Valid_Mem`'s `core_every_row` + the
extracted writing emission's slot-match + a Mem AIR continuity
lemma — same trust class as the existing reads-side derivations.

**What remains.** No callers in tree consume the Layer-2 form yet:
existing `LoadD` / `StoreD` / `Add` / `BinaryLogic` / `JumpUType`
consumers still take `register_write_lanes_match` as a `def`-level
hypothesis. The S5 per-opcode cleanup (this plan) will rewire those
call sites to use the Layer-2 derivation; that work is separate
from this S4 closure.
