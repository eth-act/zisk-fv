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

### Entry M3: `PureSpec.execute_LOADWU_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/lwu.lean`
- **Statement (informal):** narrow companion of M1 for
  `execute_LOAD imm rs1 rd true 4` (width 4, `is_unsigned = true`).
  Under `RISC_V_assumptions` + `lwu_state_assumptions` (four source
  bytes pinned, 4-byte alignment, address below `2^29`), reduces to
  `+4` to PC; conditional little-endian word-concatenation zero-extended
  to 64 bits into `rd`; retire-success.
- **Consumers:** `PureSpec.execute_LOADWU_pure_equiv`; consumed by
  `ZiskFv/Equivalence/LoadWU.lean::equiv_LWU_sail`.
- **Provenance:** `LeanRV64D/VmemUtils.lean::vmem_read_addr` +
  `LeanRV64D/InstsEnd.lean::execute_LOAD` (width 4, zero-extend path).

### Entry M4: `PureSpec.execute_STOREW_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/sw.lean`
- **Statement (informal):** narrow companion of M2 for
  `execute_STORE imm rs2 rs1 4`. Under `RISC_V_assumptions` +
  `sw_state_assumptions`, reduces to `+4` to PC; four
  `state.mem.insert` writes encoded by `modify_memory_4`; retire-success.
- **Consumers:** `PureSpec.execute_STOREW_pure_equiv`; consumed by
  `ZiskFv/Equivalence/StoreW.lean::equiv_SW_sail`.
- **Provenance:** `LeanRV64D/VmemUtils.lean::vmem_write_addr` +
  `LeanRV64D/InstsEnd.lean::execute_STORE` (width 4 path).

## Why M1-M4 exist

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
mechanical unfolds. M1-M4 become theorems.

## Control-flow axioms (Phase 2.5 D4b, path (b) — 2026-04-22)

### Entry C1: `PureSpec.execute_JALR_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/jalr.lean`
- **Statement (informal):** under the standard register-state
  hypotheses (imm/rs1/rd alignment, PC readable, misa readable,
  machine privilege, mseccfg readable), the Sail
  `execute_JALR imm rs1 rd` threaded through the standard
  `writeReg nextPC (PC+4); execute …` prelude reduces to the pure-spec
  block: (a) on bit-1 misalignment of the `0xFFFFFFFE`-masked target,
  raise `E_Fetch_Addr_Align`; (b) otherwise write
  `nextPC := 0xFFFFFFFE &&& (rs1 + signExtend imm)`, write link address
  `PC+4` to rd (if rd ≠ 0), retire success.
- **Consumers:** `PureSpec.execute_JALR_pure_equiv` (the lemma in the
  same file); consumed by the JALR equivalence proof downstream.
- **Provenance:** `LeanRV64D/InstsEnd.lean::execute_JALR` (line 67189)
  + `LeanRV64D/ZicfilpRegs.lean::update_elp_state` (line 224)
  + `LeanRV64D/Types.lean::currentlyEnabled Ext_Zicfilp` (line 531).

### Why C1 exists

Unlike JAL (whose RV64 proof closes via `jump_to_equiv` under a misa[C]=0
witness), JALR invokes `update_elp_state rs1` before the jump. In RV64D
that helper consults `currentlyEnabled Ext_Zicfilp`, which unfolds to
`currentlyEnabled Ext_Zicsr && hartSupports Ext_Zicfilp && get_xLPE
cur_privilege`. In machine privilege, `get_xLPE` reads
`_get_Seccfg_MLPE (mseccfg)`; in User privilege it branches further on
`currentlyEnabled Ext_S` to read `senvcfg` or `menvcfg`. The RV32
companion (`OpenvmFv/RV32D/jalr.lean::execute_JALR_pure_equiv`) closes
directly because its `hartSupports Ext_Zicsr` simp-chain reduces without
additional register-state assumptions; the RV64 chain introduces CSR
register-read probes not currently witnessed by `RISC_V_assumptions`.

**Closure path.** Extend `RISC_V_assumptions` with a disabling witness
for `Ext_Zicfilp` (either `mseccfg.MLPE = 0` or a direct
`currentlyEnabled Ext_Zicfilp state = ok false state` equation).
Machine-privilege-only proofs can adopt the simpler `mseccfg.MLPE = 0`
hypothesis; with it, `update_elp_state` collapses to `pure ()` and the
rest of the proof is the RV32 port with `signExtend 32 → signExtend 64`
and the RV64 `jump_to_equiv`'s misa-bit-2-zero witness (already
available as `h_misa`). Estimated: 40-60 lines, same shape as
`execute_JAL_pure_equiv`.

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
- **2026-04-22 — Phase 2.5 D4c/D4d.** M3 (LWU) and M4 (SW) introduced as
  narrow width-4 companions of M1/M2, blocked by the same platform-config
  gap. Retiring `vmem_{read,write}_addr_aligned_equiv` would retire all
  four M-entries together.
- **2026-04-22 — Phase 2.5 D4b-patch.** C1 introduced (JALR). Distinct
  obstruction class from M1-M4: control-flow rather than memory-model,
  blocked on `currentlyEnabled Ext_Zicfilp` rather than PMP/CLINT. Would
  close directly under an `mseccfg.MLPE = 0` extension to
  `RISC_V_assumptions`.
