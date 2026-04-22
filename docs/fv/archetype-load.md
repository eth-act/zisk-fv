# Load archetype (LD + LWU / LHU / LBU zero-ext family) — Phase 2 A3 delivery

This note describes the **memory-load proof archetype** that Phase 2 A3
established and that Phase 3 will instantiate across the remaining RV64IM
zero-extension loads (LWU / LHU / LBU).

## What a load archetype proof proves

Given an RV64IM zero-extension load opcode `L<w>u` (LD = 64-bit,
LWU = 32-bit, LHU = 16-bit, LBU = 8-bit), the archetype closes the
**circuit-side** piece of the metaplan theorem

```
execute_instruction (.LOAD (imm, rs1, rd, is_unsigned, width)) state =
  (bus_effect exec_row mem_row state).2
```

reducing it to three hypotheses the caller supplies:

1. a transpile axiom (`transpile_L<w>u`) fixing the Zisk
   microinstruction row's opcode (`OP_COPYB = 1`),
   `is_external_op = 0`, `set_pc = 0`, `store_pc = 0`, `m32 = 0`,
   `jmp_offset1 = jmp_offset2 = 4`, and the `a` lane population
   (`xreg rs1`);
2. a Sail-side `execute_<width>u_pure_equiv` lemma per opcode — LD
   is scaffolded in Phase 2 with a focused `sorry` on the tactical
   reduction through `vmem_read_addr`'s byte loop (see `RV64D/ld.lean`
   and the A3 status note in `ai_plans/zisk-fv-phase-2.md`). The
   *semantic* content is complete; only the Sail tactical chain for
   width = 8 is pending Phase 3 sweep work;
3. a memory-bus matching hypothesis `memory_load_lanes_match`
   identifying the Main row's `b_0`/`b_1` lanes with the 32-bit
   halves of the loaded 8-byte value (from `bus_effect`'s memory-read
   branch).

## Why zero-extension loads (copyb) are the archetype, not signed loads

The Zisk transpiler splits the seven integer loads by sign behaviour
(`core/src/riscv2zisk_context.rs:210-216`):

| RV64 opcode | ZisK op          | `OpType`  | External?           |
|-------------|------------------|-----------|---------------------|
| **LD**      | `copyb`  (0x01)  | Internal  | No — constraint 9   |
| **LWU**     | `copyb`  (0x01)  | Internal  | No — constraint 9   |
| **LHU**     | `copyb`  (0x01)  | Internal  | No — constraint 9   |
| **LBU**     | `copyb`  (0x01)  | Internal  | No — constraint 9   |
| LW          | `signextend_w`   | BinaryE   | Yes — BinaryExt bus |
| LH          | `signextend_h`   | BinaryE   | Yes — BinaryExt bus |
| LB          | `signextend_b`   | BinaryE   | Yes — BinaryExt bus |

Zero-ext loads use Zisk's `copyb` op (`OpType::Internal`), which does
**not** hop the operation bus. Main constraint 9
(`(1 - is_external_op) * op * (b - c) = 0`) forces `c = b` directly —
the Binary SM is skipped. That makes zero-ext loads *simpler* than ADD
(which goes through BinaryAdd) at the circuit level: the compositional
theorem collapses to a trivial `rw` chain after destructuring the
internal-op=1 constraint forms.

The signed loads (LW/LH/LB) *do* hop the bus, to the BinaryExtension
SM. They're Phase 3 scope — the archetype for them is the composition
of the A3 memory-bus machinery + the A6 (SLLW) BinaryExtension-SM
machinery.

## Archetype deliverables (files landed Phase 2 A3)

* `ZiskFv/Airs/MemoryBus.lean` — new module with:
  * `memory_entry_toField` — packs 8 byte-lanes into a 64-bit `FGL`;
  * `memory_entry_lo` / `memory_entry_hi` — low / high 32-bit lanes;
  * `memory_entry_toField_lo_hi` — recombination identity;
  * `matches_memory_entry` — field-wise `MemoryBusEntry` equality;
  * `memory_load_lanes_match` — Main `b`-lanes match bus-entry halves;
  * `register_write_lanes_match` — Main `c`-lanes match register-write
    bus entry (used by Phase 4 audit + A4 SD).
* `ZiskFv/Spec/LoadD.lean`:
  * `main_row_in_ld_mode` — LD-mode witnesses (`is_external_op = 0,
    op = 1, m32 = 0, set_pc = 0`);
  * `load_subset_holds` — the 5 Main constraints a LD row satisfies;
  * `load_d_circuit_holds` — full circuit hypotheses;
  * `load_d_compositional` — `main_c_packed = memory_entry_toField entry`;
  * `load_d_next_pc` / `load_d_next_pc_concrete` — `next_pc = pc + 4`.
* `ZiskFv/Tactics/LoadArchetype.lean`:
  * `load_archetype_copyb_circuit_holds` — parametric circuit-holds;
  * `load_archetype_copyb_c_packed` — parametric packed-c theorem;
  * `load_archetype_copyb_next_pc` — parametric next-pc theorem;
  * `load_archetype_proof` — convenience tactic macro.
* `ZiskFv/Fundamentals/Transpiler.lean` — `OP_COPYB = 1` literal +
  `axiom transpile_LD`.
* `ZiskFv/Equivalence/LoadD.lean`:
  * `equiv_LD` — circuit-level (`main_c_packed = memory_entry_toField`);
  * `equiv_LD_sail` — Sail-level (wraps pure-equiv);
  * `equiv_LD_metaplan` — metaplan-shape end-to-end theorem.
* `ZiskFv/RV64D/ld.lean` — pure spec + Sail equivalence skeleton
  (with one focused `sorry`; see "Known gaps" below).
* `ZiskFv/GoldenTraces/LD.lean` — hand-witness `by decide` fixture.

## Known gaps

* **`execute_LOADD_pure_equiv` tactical reduction (1 focused `sorry`).**
  Sail's `execute_LOAD` at `width = 8` reduces through an 8-iteration
  `untilFuelM` byte loop in `vmem_read_addr`. openvm-fv's 4-byte `lw`
  proof uses a short simp-chain; porting to 8 bytes surfaces two
  specific tactical issues documented in-situ (alignment `omega`
  failure + `if_pos` target mismatch). Both are tractable in an
  estimated 1-2 day sweep. The **circuit-side** archetype stack
  (`Spec.LoadD`, `Equivalence.LoadD`, `Tactics.LoadArchetype`, the
  golden-trace fixture) is zero-`sorry` and consumes this lemma
  parametrically.
* **Operation-bus parameterization.** `equiv_LD_metaplan` carries an
  `h_bus_execute_matches_sail` hypothesis rather than deriving it
  from PIL-level bus emission. Same decision as A1-B / A2-B; Phase 4
  audit work.

## A3 → A4 (SD) bridge note

**SD is the near-mirror of LD.** Same memory-bus infrastructure; only
the multiplicity (`+1` vs `-1`) and direction (Main proves the memory
store vs. Main assumes the memory load) flip. The `Airs/MemoryBus.lean`
predicates (`matches_memory_entry`, `memory_entry_toField`) are
already write-side-symmetric. A4 will add:

* a `store_subset_holds` predicate (constraint 10's store-side `mem_op`
  instead of constraint 9's load-side);
* a `memory_store_lanes_match` predicate asserting `value = b` (Sail
  `wX_bits rs2` → memory) rather than `value = c` (memory → Sail
  `wX_bits rd`);
* a `transpile_SD` axiom (`store_op` instead of `load_op`).

Most of A3's scaffolding carries over verbatim — budget A4 at half a
day after A3 lands.

## Usage pattern for Phase 3 fan-out

```lean
-- LWU case (32-bit zero-extension load — hypothesis sketch):
theorem equiv_LWU_metaplan
    (ld_input : PureSpec.LdInput)  -- same shape, just data0..3 nonzero
    ...
    (h_bus_bytes_zero : entry.x4 = 0 ∧ entry.x5 = 0 ∧ entry.x6 = 0 ∧ entry.x7 = 0)
    ... := by
  -- Use load_archetype_copyb_c_packed, then simp with h_bus_bytes_zero
  -- to zero out the high lanes of memory_entry_toField.
  have := load_archetype_copyb_c_packed m r_main next_pc entry h_circuit
  -- ...
```

LH/LHU and LB/LBU follow the same pattern with more high-byte
zero-witnesses.

## Simp-race cleanup (deferred)

A3 did not touch the `currentlyEnabled Ext_Zca` simp race documented in
`RV64D/Auxiliaries.lean`. LD doesn't exercise that path
(`jump_to`-adjacent). The cleanup decision belongs to whichever
archetype first needs clean `jump_to_equiv` behaviour — A2 (JAL) or
the Phase 3 jump-family sweep.
