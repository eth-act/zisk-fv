# ZisK AIR inventory and Lean extraction status

Source-of-truth artifact: `build/zisk.pilout` (Docker-built; see repro/).
Tool: `tools/pil-extract/ -- --pilout pil/zisk.pilout --list`.

The pilout contains **22 AIRs**. This table tracks which are extracted
into the `ZiskFv/Extraction/` Lean layer, which have named-column
wrappers in `ZiskFv/Airs/`, and which are currently absorbed into the
trusted base.

## Full inventory

| # | AIR | Constraints | Exprs | RV64IM scope? | `Extraction/` | `Airs/` named wrapper | Notes |
|---|---|---|---|---|---|---|---|
| 0 | Main | 146 | 3651 | yes | ✅ Main.lean | ✅ Valid_Main | central op-bus consumer |
| 1 | Rom | 2 | 68 | not exercised | ❌ | ❌ | program storage; not on per-opcode equivalence path |
| 2 | Mem | 34 | 415 | yes | ❌ | ❌ | load/store SM; **trusted via `h_bus_execute_matches_sail`** |
| 3 | RomData | 23 | 215 | not exercised | ❌ | ❌ | ROM data section |
| 4 | InputData | 24 | 340 | not exercised | ❌ | ❌ | public-input infra |
| 5 | MemAlign | 40 | 606 | yes | ❌ | ❌ | unaligned access; **trusted today** |
| 6 | MemAlignByte | 16 | 352 | yes | ❌ | ❌ | trusted today |
| 7 | MemAlignReadByte | 10 | 235 | yes | ❌ | ❌ | trusted today |
| 8 | MemAlignWriteByte | 15 | 364 | yes | ❌ | ❌ | trusted today |
| 9 | Arith | 65 | 1285 | yes | ✅ Arith.lean | ✅ Valid_ArithMul, Valid_ArithDiv | MUL/DIV/REM family |
| 10 | **Binary** | 14 | 1049 | yes | **❌ row-constraints missing** | ❌ | bus-emission stub only (`bus_emission_Binary_0/1` in `Buses.lean`); **blocks K1-B and SLT half of K1-C** |
| 11 | BinaryAdd | 9 | 198 | yes | ✅ BinaryAdd.lean | ✅ Valid_BinaryAdd | ADD/SUB carry chains |
| 12 | **BinaryExtension** | 8 | 830 | yes | **❌ row-constraints missing** | ❌ | bus-emission stub only; **blocks Shift half of K1-C and *W sign-extension paths** |
| 13 | Add256 | 36 | 1880 | precompile — out of scope | ❌ | ❌ | per CLAUDE.md |
| 14 | ArithEq | 92 | 22544 | precompile — out of scope | ❌ | ❌ | per CLAUDE.md |
| 15 | ArithEq384 | 75 | 32377 | precompile — out of scope | ❌ | ❌ | per CLAUDE.md |
| 16 | Keccakf | 2432 | 92959 | precompile — out of scope | ❌ | ❌ | per CLAUDE.md |
| 17 | Sha256f | 111 | 6144 | precompile — out of scope | ❌ | ❌ | per CLAUDE.md |
| 18 | U256Delegation | 184 | 2320 | out of scope | ❌ | ❌ | custom internal op per CLAUDE.md |
| 19 | SpecifiedRanges | 18 | 677 | yes | ❌ | ❌ | range-check lookup table; **trusted today** (range hypotheses parameterized in opcode proofs) |
| 20 | VirtualTable0 | 6 | 455 | yes | ❌ | ❌ | internal lookup table; trusted today |
| 21 | VirtualTable1 | 6 | 628 | yes | ❌ | ❌ | internal lookup table; trusted today |

(Row count uses `tools/pil-extract -- --list` output formatting:
`rows=2^N, exprs=E, constraints=C`. Numbers verified at branch
`feature/track-n-h-rd-val` HEAD.)

## Sub-extractions

In addition to the per-AIR extraction files, one **lookup-table sub-extraction** exists:

- `Extraction/ArithTable.lean` — extracted from inside the `Arith` AIR. Encodes the 9-opcode `(opcode, m32) ↦ (na, nb, np, nr)` mapping that the arith_table permutation uses (Track P).

## Categories of "not extracted today"

The AIRs without `Extraction/` files break into three categories:

### A. **Out of scope per CLAUDE.md** — won't extract

`Add256`, `ArithEq`, `ArithEq384`, `Keccakf`, `Sha256f`, `U256Delegation`. These are crypto/256-bit precompiles and ZisK-internal ops; CLAUDE.md says: "Zicclsm, precompiles (Keccak, SHA256, …), and ZisK's custom internal ops are out of scope for the initial effort."

### B. **In scope but currently in the trusted base** — eventual extraction

Range-check / lookup-table AIRs whose semantics are absorbed as
hypotheses on per-opcode proofs:

- `SpecifiedRanges` — enforces 16-bit / 8-bit chunk range checks via
  lookup arguments. Today: per-opcode proofs take `chunks_in_range`
  hypotheses directly. Eventually: derive those from the
  SpecifiedRanges row constraints + plookup soundness.
- `VirtualTable0`, `VirtualTable1` — internal lookup tables; same
  trust pattern.

`trusted-base.md` Category 2 ("Arith lookup axioms") tracks this work
as **moderate effort, plookup/logUp soundness in Lean**.

The `Mem`, `MemAlign*` family is also Category B for load/store
correctness — the per-opcode load/store proofs take a monolithic
`h_bus_execute_matches_sail` hypothesis that asserts "the memory-bus
delivers what Sail's memory model says," and the Mem AIR's row
constraints (which would *enforce* that) are not modeled.

### C. **Not on the per-opcode equivalence path** — may never need extraction

`Rom`, `RomData`, `InputData`. These would matter for a top-level
soundness theorem ("ZisK's full program execution from initial
state + public input matches Sail's interpreter"). The current
metaplan only proves per-opcode equivalence given a *decoded*
instruction (`add_input`, `ld_input`, etc.) — it doesn't reason about
how that instruction got there. Extracting Rom/RomData/InputData would
be needed for a top-level theorem; for per-opcode work it's not
load-bearing.

## What's blocking Track N specifically

Of the 22 AIRs, only two are blocking immediate Track N work:

- **Binary (#10)** — 14 constraints, 1049 exprs. Required for K1-B
  (AND/OR/XOR `PackedCorrect` lifts) and the SLT half of K1-C.
  Authoring effort: comparable to `Extraction/BinaryAdd.lean` (9
  constraints / 198 exprs / ~150 lines extracted) but ~5× larger by
  exprs.
- **BinaryExtension (#12)** — 8 constraints, 830 exprs. Required for
  the Shift half of K1-C, and downstream for *W sign-extension paths.
  Authoring effort: comparable to BinaryAdd, ~4× larger by exprs.

Both extractions follow the same pattern as the existing
`BinaryAdd.lean` (raw `Extraction/<X>.lean` + named-column
`Airs/Binary/<X>.lean` wrapper); no new tooling needed — `tools/pil-extract/`
already supports them. They are deferred from Track N proper into a
Track N1.5 "Binary AIR extractions" follow-on phase.

## What's blocking K2 (memory-bus side, separate concern)

K2 surfaced an additional gap: **the memory-bus extraction itself**
(bus_id=10, distinct from the Binary AIR question above) uses PIL2
permutation arguments whose `gsum_debug_data` hints carry ExtF-typed
challenge randomness. The auto-extractor stubs all of those with
`multiplicity = 0`, so there is no `bus_emission_Main_*_mem` analogue
of the operation-bus `bus_emission_Main_0`. K2's three lane-match
"theorems" therefore reduce to structurally-trivial unfoldings; the
real work of deriving them from circuit emission is blocked behind a
deeper extractor change (or a hand-stated permutation soundness layer).
See K2 commit `2c627ac` for the in-tree consequence.
