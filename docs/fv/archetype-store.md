# Store archetype (SD + SW / SH / SB family) — Phase 2 A4 delivery

This note describes the **memory-store proof archetype** that Phase 2
A4 established and that Phase 3 will instantiate across the remaining
RV64IM integer stores (SW / SH / SB). It is the **write-side mirror**
of the A3 load archetype (`archetype-load.md`).

## What a store archetype proof proves

Given an RV64IM integer store opcode `S<w>` (SD = 64-bit, SW = 32-bit,
SH = 16-bit, SB = 8-bit), the archetype closes the **circuit-side**
piece of the metaplan theorem

```
execute_instruction (.STORE (imm, rs2, rs1, width)) state =
  (bus_effect exec_row mem_row state).2
```

reducing it to three hypotheses the caller supplies:

1. a transpile axiom (`transpile_S<w>`) fixing the Zisk
   microinstruction row's opcode (`OP_COPYB = 1`),
   `is_external_op = 0`, `set_pc = 0`, `store_pc = 0`, `m32 = 0`,
   `jmp_offset1 = jmp_offset2 = 4`, and **both** `a` and `b` lane
   populations (`xreg rs1` and `xreg rs2` respectively — SD uses
   `src_b = reg(rs2)`, not `src_b = ind(imm)` like LD does);
2. a Sail-side `execute_<width>_pure_equiv` lemma per opcode — SD is
   scaffolded in Phase 2 with a focused `sorry` on the tactical
   reduction through `vmem_write_addr`'s byte loop (symmetric to A3's
   LD sorry on `vmem_read_addr`; see `RV64D/sd.lean` and the A4 status
   note in `ai_plans/zisk-fv-phase-2.md`). Both sorries should be
   retired together by a single Phase 3 sweep producing
   `vmem_read_aligned_equiv` + `vmem_write_aligned_equiv` bulk lemmas;
3. a memory-bus matching hypothesis `memory_store_lanes_match`
   identifying the Main row's `c_0`/`c_1` lanes with the 32-bit halves
   of the stored 8-byte value (from `bus_effect`'s memory-write
   branch at `BusEffect.lean:90-103`).

## Why all integer stores share `copyb` — no signed/unsigned split

Unlike loads (which split seven ways by sign behaviour at
`riscv2zisk_context.rs:210-216`), the four integer stores all share
one transpilation shape (`riscv2zisk_context.rs:220-223`):

| RV64 opcode | ZisK op          | `OpType`  | External?           |
|-------------|------------------|-----------|---------------------|
| **SD**      | `copyb`  (0x01)  | Internal  | No — constraint 9   |
| **SW**      | `copyb`  (0x01)  | Internal  | No — constraint 9   |
| **SH**      | `copyb`  (0x01)  | Internal  | No — constraint 9   |
| **SB**      | `copyb`  (0x01)  | Internal  | No — constraint 9   |

There are no `signextend_*` store opcodes: a store writes the low
`w` bytes of `rs2` to memory verbatim. Whether the host would later
*read* those bytes as signed or unsigned is a load-side decision.
So the store archetype covers all four opcodes with a single mode
(`OP_COPYB`, `is_external_op = 0`) — Phase 3's SW/SH/SB fan-out
adds only a width-specific "high-byte zeroing" hypothesis on the
memory-bus write entry (SW zeros x4..x7, SH zeros x2..x7, SB zeros
x1..x7).

## Key departures from the LD archetype

Same shape, different *direction*:

| Aspect | LD (A3)                          | SD (A4)                             |
|--------|----------------------------------|-------------------------------------|
| `src_b`      | `ind(imm)` — memory read     | `reg(rs2)` — register read (value)  |
| `store`      | `reg(rd)` — register write   | `ind(imm, ...)` — memory write      |
| Mem entry    | `mult = -1, as = 2` (read)   | `mult = +1, as = 2` (write)         |
| Matching     | `b` lanes — assume side      | `c` lanes — prove side              |
| Pure output  | `rd : Option (idx, value)`   | 8 × `(addr, byte)` memory writes    |
| Sail block   | `write_xreg rd val` or skip  | `set (modify_memory_8 (← get) out)` |

Main AIR constraint subset is **identical**: SD's `store_subset_holds`
is a `def` alias for LD's `load_subset_holds` — both sit in the
`is_external_op = 0, op = 1` mode so constraints 9/16/18/19 + PC
handshake fire with the same signatures. This is why no new Main
columns were needed for A4.

## Archetype deliverables (files landed Phase 2 A4)

* `ZiskFv/Airs/MemoryBus.lean` — extended with:
  * `memory_store_lanes_match` — Main `c`-lanes match the memory-bus
    *write* entry's byte halves (mirror of `memory_load_lanes_match`);
  * `register_read_rs2_lanes_match` — Main `b`-lanes match the
    register-read entry that carries rs2's value (symmetric to LD's
    rs1 register-read).
* `ZiskFv/Spec/StoreD.lean`:
  * `main_row_in_sd_mode` — SD-mode witnesses (identical to LD);
  * `store_subset_holds` — aliases `load_subset_holds`;
  * `store_d_circuit_holds` — full circuit hypotheses;
  * `store_d_compositional` — `main_c_packed = memory_entry_toField
    entry` (the memory-write entry);
  * `store_d_next_pc` / `store_d_next_pc_concrete` — `next_pc = pc + 4`.
* `ZiskFv/Tactics/StoreArchetype.lean`:
  * `store_archetype_copyb_circuit_holds` — parametric circuit-holds;
  * `store_archetype_copyb_c_packed` — parametric packed-c theorem;
  * `store_archetype_copyb_next_pc` — parametric next-pc theorem;
  * `store_archetype_proof` — convenience tactic macro.
* `ZiskFv/Fundamentals/Transpiler.lean` — `axiom transpile_SD`
  (reuses `OP_COPYB = 1` from A3).
* `ZiskFv/Equivalence/StoreD.lean`:
  * `equiv_SD` — circuit-level;
  * `equiv_SD_sail` — Sail-level (wraps pure-equiv);
  * `equiv_SD_metaplan` — metaplan-shape end-to-end theorem.
* `ZiskFv/RV64D/sd.lean` — pure spec + `SdInput`/`SdOutput` +
  `modify_memory_8` helper + Sail equivalence skeleton (with one
  focused `sorry` symmetric to A3 — see "Known gaps").
* `ZiskFv/GoldenTraces/SD.lean` — hand-witness `by decide` fixture.

## Known gaps

* **`execute_STORED_pure_equiv` tactical reduction (1 focused `sorry`).**
  Sail's `execute_STORE` at `width = 8` reduces through an 8-iteration
  `untilFuelM` byte loop in `vmem_write_addr` — the structural twin
  of the `vmem_read_addr` loop that blocks A3's LD sorry. Recommended
  resolution: a single Phase 3 sweep session producing both
  `vmem_read_aligned_equiv` and `vmem_write_aligned_equiv` as bulk
  lemmas in `RV64D/Auxiliaries.lean`, closing the entire RV64 8-byte
  memory-op family (LD + SD) and unlocking SW/SH/SB when their own
  byte-width variants are added. Estimated 1-2 days. The
  **circuit-side** archetype stack (`Spec.StoreD`, `Equivalence.StoreD`,
  `Tactics.StoreArchetype`, the golden-trace fixture) is zero-`sorry`
  and consumes this lemma parametrically.
* **Operation-bus parameterization.** `equiv_SD_metaplan` carries an
  `h_bus_execute_matches_sail` hypothesis rather than deriving it from
  PIL-level bus emission. Same decision as A1-B / A2-B / A3-B;
  Phase 4 audit work.

## Usage pattern for Phase 3 fan-out

```lean
-- SW case (32-bit store — hypothesis sketch):
theorem equiv_SW_metaplan
    (sw_input : PureSpec.SwInput)  -- same shape as SdInput, 4-byte writes
    ...
    (h_bus_bytes_zero : entry.x4 = 0 ∧ entry.x5 = 0 ∧ entry.x6 = 0 ∧ entry.x7 = 0)
    ... := by
  -- Use store_archetype_copyb_c_packed, then simp with h_bus_bytes_zero
  -- to zero out the high lanes of memory_entry_toField.
  have := store_archetype_copyb_c_packed m r_main next_pc entry h_circuit
  -- ...
```

SH and SB follow the same pattern with more high-byte zero-witnesses.

## Cross-reference

* Load-side archetype: `docs/fv/archetype-load.md`.
* Shared memory-bus infrastructure: `ZiskFv/Airs/MemoryBus.lean` (read
  the header docstring — it covers both directions).
* Phase 2 plan recon: `ai_plans/zisk-fv-phase-2.md` sections
  "Reconnaissance A3 (LD)" and "Reconnaissance A4 (SD)".
