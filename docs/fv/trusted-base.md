# zisk-fv — trusted base

Canonical registry of axioms in the zisk-fv development. Every axiom here
is load-bearing: it is consumed by the per-opcode equivalence proofs, it
is **not** derived from any earlier result, and changes to it require
re-auditing against the cited provenance.

Two broad categories:

1. **Transpiler contracts** — pure specs of the Rust code that lowers
   RISC-V instructions to Zisk microinstructions. Home:
   `ZiskFv/Fundamentals/Transpiler.lean` under the
   `ZiskFv.Trusted` namespace. Not covered here (that file's docstrings
   are self-sufficient).
2. **Memory-model reductions** — property assertions about
   `LeanRV64D.Functions.{vmem_read_addr, vmem_write_addr}` that are
   semantically derivable but require extensions to
   `RISC_V_assumptions` that have not yet been worked out. The two
   entries below fall into this category.

## Memory-model axioms (Phase 2.5 D1, path (b) — 2026-04-22)

### Entry M1: `PureSpec.execute_LOADD_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/ld.lean`
- **Statement (informal):** under `RISC_V_assumptions` +
  `ld_state_assumptions` (eight `state.mem[addr+i]? = .some data_i`
  facts, address below `2^29`, 8-byte alignment), the Sail
  `execute_LOAD imm rs1 rd false 8` threaded through the standard
  `writeReg nextPC (PC+4); execute …` prelude reduces to the pure-spec
  `execute_LOADD_pure` evaluation (`+4` to PC; conditional little-endian
  doubleword write to `rd`; retire-success).
- **Consumers:** `PureSpec.execute_LOADD_pure_equiv` (the lemma in the
  same file); which in turn is consumed by
  `ZiskFv/Equivalence/LoadD.lean::equiv_LD_sail`.
- **Provenance:** `LeanRV64D/VmemUtils.lean::vmem_read_addr` +
  `LeanRV64D/InstsEnd.lean::execute_LOAD` (lines 251 and 67179 in the
  vendored `sail-riscv-lean@ext-zca-simp-lemmas`).

### Entry M2: `PureSpec.execute_STORED_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/sd.lean`
- **Statement (informal):** symmetric to M1 for
  `execute_STORE imm rs2 rs1 8`. Under `RISC_V_assumptions` +
  `sd_state_assumptions`, reduces to: `+4` to PC; the eight
  `state.mem.insert` chain encoded by `modify_memory_8`;
  retire-success.
- **Consumers:** `PureSpec.execute_STORED_pure_equiv`; consumed by
  `ZiskFv/Equivalence/StoreD.lean::equiv_SD_sail`.
- **Provenance:** `LeanRV64D/VmemUtils.lean::vmem_write_addr` +
  `LeanRV64D/InstsEnd.lean::execute_STORE`.

## Why these two axioms exist

Both reduce the same underlying Sail memory-model infrastructure. The
obstruction is a platform-config gap between the vendored LeanRV64D and
the assumptions currently recorded in `RISC_V_assumptions`:

| Platform constant | LeanRV32D | LeanRV64D | Impact |
|-------------------|-----------|-----------|--------|
| `sys_pmp_count`   | 0         | 16        | `pmpCheck` unfolds to a 16-iteration `forIn` loop over `pmpcfg_n` / `pmpReadAddrReg`. In the RV32 case, the `== 0` short-circuit takes the `pure none` branch immediately; in the RV64 case, `simp` cannot reduce the loop without register-state assumptions that `RISC_V_assumptions` does not currently provide. |
| `plat_clint_base` | 0         | `2^25 = 33_554_432` | `within_clint` can return `true` for `addr ∈ [2^25, 2^25 + 786432)`, which lies entirely within the `< 2^29 = 536_870_912` envelope enforced by `OpenVM_address_space_size`. Under a `true` result, `checked_mem_read`/`checked_mem_write` diverts to `mmio_read`/`mmio_write`, bypassing `state.mem[...]?` entirely. |
| `plat_clint_size` | 0         | 786432    | Companion of `plat_clint_base`; see above. |

Three reusable lemmas would suffice to eliminate both axioms:

1. `pmpCheck_none_of_all_off` — given
   `∀ i < 16, (state.regs.get? pmpcfg_n).get? i |>.A = OFF`
   plus `priv = Machine`, the 16-iteration loop returns `pure none`.
2. `within_clint_false_of_addr_disjoint` — given
   `addr + width ≤ plat_clint_base ∨ plat_clint_base + plat_clint_size ≤ addr`,
   `within_clint addr width state = (ok false, state)`.
3. `pmaCheck_none_of_single_region` — the existing
   `RISC_V_assumptions` clauses on `pmaRegion` plus width-alignment
   already discharge `pmaCheck`; this is essentially a direct port from
   openvm-fv's RV32D proof.

Add the PMP-OFF and CLINT-disjoint hypotheses to `RISC_V_assumptions`;
prove (1)-(3); then derive `vmem_{read,write}_addr_aligned_equiv` as
mechanical unfolds. Both axioms become theorems.

## Audit procedure

When accepting a new trusted axiom:

1. Record the axiom's file + name + consumers + provenance in a new
   section of this file.
2. State informally what the axiom asserts and why it cannot currently
   be derived (missing hypotheses on `RISC_V_assumptions`, missing
   platform config assumptions, etc.).
3. Sketch the closure path: which lemmas would eliminate the axiom,
   roughly how long they are, and which phase could reasonably tackle
   them.
4. Cross-link from the axiom's docstring back to the entry here.

## History

- **2026-04-22 — Phase 2.5 D1.** M1 and M2 introduced after Attempt 1's
  diagnosis revealed a platform-config gap in the A3/A4 Phase 2 proofs.
  Path (a) — extend `RISC_V_assumptions` and prove (1)-(3) — estimated
  300-500 lines per lemma; path (b) (this file) — 100 lines total for
  the two axioms plus this doc. Phase 3 may revisit.
