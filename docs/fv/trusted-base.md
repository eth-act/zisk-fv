# zisk-fv — trusted base

Canonical registry of axioms in the zisk-fv development. Every axiom here
is load-bearing: it is consumed by the per-opcode equivalence proofs, it
is **not** derived from any earlier result, and changes to it require
re-auditing against the cited provenance.

Three broad categories:

1. **Transpiler contracts** — pure specs of the Rust code that lowers
   RISC-V instructions to Zisk microinstructions. Home:
   `ZiskFv/Fundamentals/Transpiler.lean` under the
   `ZiskFv.Trusted` namespace. Not covered here (that file's docstrings
   are self-sufficient).
2. **Platform-feature assertions (Phase 3.5)** — narrow universal
   axioms encoding that `LeanRV64D` Sail features out of RV64IM scope
   (PMP, CLINT MMIO, Zicfilp landing pads) are inert in ZisK's target.
   Home: `ZiskFv/RV64D/Auxiliaries.lean` under the
   `ZiskFv.PlatformScope` namespace. Entries P1-P4 below. As of the
   Phase 3.5 final state these axioms replace the former per-opcode
   memory / control-flow axioms in the M/C families — M1-M4, M7, M9,
   M10, M11, C1, C3a-c, C4 are then theorems derived from P1-P4 + the
   `execute_*` refactor triples in `Fundamentals/Execution.lean`.
3. **Memory-model reductions** (legacy Phase 2.5 framing; retained for
   audit trail) — property assertions about
   `LeanRV64D.Functions.{vmem_read_addr, vmem_write_addr}`. Phase 3.5
   promoted all such former axioms to theorems. Their entries below
   are marked **[promoted to theorem in Phase 3.5]**.

## Platform-feature assertions (Phase 3.5 — 2026-04-22)

Four narrow universal axioms encode ZisK's RV64IM scope commitments:
the vendored `LeanRV64D` models PMP (16 entries), CLINT MMIO
(`plat_clint_base = 2^25`, `plat_clint_size = 786432`), PMA checks,
and the Zicfilp landing-pad extension as active Sail features, but
ZisK's target excludes all four. Each axiom is a single `= pure …`
reduction encoding the scope-honest inert behavior.

Together P1-P4 retire 9 of the 16 Phase-3A-era Sail-equivalence
axioms (M1-M4, M7, M9, M10, M11, C1) via two bridging lemmas
(`vmem_{read,write}_addr_aligned_equiv`) and a direct port of
openvm-fv's RV32D JALR proof.

### Entry P1: `ZiskFv.PlatformScope.pmpCheck_is_pure_none`

- **File:** `ZiskFv/RV64D/Auxiliaries.lean`
- **Statement:** `∀ addr width acc priv state,
  pmpCheck addr width acc priv state = EStateM.Result.ok none state`.
- **Consumers:** `vmem_read_addr_aligned_equiv`,
  `vmem_write_addr_aligned_equiv` (Auxiliaries.lean). Also re-exported
  as a descriptive field of `RISC_V_assumptions`.
- **Scope claim:** ZisK never programs a PMP entry — all `pmpcfg_n[i]`
  entries have `A = OFF`. The 16-iteration `forIn` loop in
  `LeanRV64D.Functions.pmpCheck` (PmpControl.lean:253) therefore
  always yields `PMP_NoMatch`, and in machine privilege the final
  `if priv == Machine then pure none` branch closes with
  `(ok none, state)`.
- **Closure path if promoted to theorem:** extend `RISC_V_assumptions`
  with a witness `∀ i < 16, _get_Pmpcfg_ent_A (pmpcfg_n[i]) = OFF` and
  prove the 16-iteration loop reduces via simp under that witness
  (estimated 150-200 lines).

### Entry P2: `ZiskFv.PlatformScope.within_clint_is_false`

- **File:** `ZiskFv/RV64D/Auxiliaries.lean`
- **Statement:** `∀ addr width state,
  within_clint addr width state = EStateM.Result.ok false state`.
- **Consumers:** `vmem_read_addr_aligned_equiv`,
  `vmem_write_addr_aligned_equiv` (Auxiliaries.lean). Re-exported as a
  descriptive field of `RISC_V_assumptions`.
- **Scope claim:** ZisK-generated programs address flat user memory
  only; CLINT MMIO is never referenced. `within_clint` is inert under
  this scope (`LeanRV64D.Platform.lean:198`).
- **Closure path if promoted to theorem:** thread an `addr + width ≤
  plat_clint_base ∨ plat_clint_base + plat_clint_size ≤ addr`
  precondition into every memory-op state assumptions bundle
  (per-opcode threading; estimated 50-80 lines per opcode).

### Entry P3: `ZiskFv.PlatformScope.pmaCheck_is_pure_none`

- **File:** `ZiskFv/RV64D/Auxiliaries.lean`
- **Statement:** `∀ paddr width acc rc state,
  pmaCheck paddr width acc rc state = EStateM.Result.ok none state`.
- **Consumers:** `vmem_read_addr_aligned_equiv`,
  `vmem_write_addr_aligned_equiv` (Auxiliaries.lean). Re-exported as a
  descriptive field of `RISC_V_assumptions`.
- **Scope claim:** the existing `RISC_V_assumptions` A2 clauses
  (single PMA region, base 0, size ≥ 2^29, readable, writable,
  `AlignmentFault`) already suffice to reduce `pmaCheck` under the
  operand alignment each opcode witnesses. Axiomatized in the
  inert-for-all-inputs form for symmetry with P1 / P2 and to avoid
  threading alignment into each call site of the vmem lemmas.
- **Closure path if promoted to theorem:** prove
  `pmaCheck_none_of_single_region` from the A2 clauses + alignment;
  this is a direct port from openvm-fv's RV32D proof (estimated
  60-100 lines).

### Entry P4: `ZiskFv.PlatformScope.update_elp_state_is_pure_unit`

- **File:** `ZiskFv/RV64D/Auxiliaries.lean`
- **Statement:** `∀ rs1,
  update_elp_state rs1 = (pure () : SailM Unit)` — in monadic form.
- **Consumers:** `PureSpec.execute_JALR_pure_equiv` (jalr.lean).
- **Scope claim:** ZisK targets RV64IM and does not enable the
  Zicfilp landing-pad extension. The `currentlyEnabled Ext_Zicfilp`
  guard in `LeanRV64D.Functions.update_elp_state`
  (`ZicfilpRegs.lean:224`) is taken on the `false` branch, making the
  helper a no-op. Under that scope `update_elp_state` is inert.
- **Closure path if promoted to theorem:** extend
  `RISC_V_assumptions` with `mseccfg.MLPE = 0` (or equivalently a
  direct `currentlyEnabled Ext_Zicfilp state = ok false state`
  witness) and prove the helper collapses via the `get_xLPE` Machine
  branch (estimated 60-80 lines).

## Memory-model axioms (Phase 2.5 D1, path (b) — 2026-04-22)

**All entries below are now theorems (Phase 3.5 — 2026-04-22).** M1-M4,
M7, M9-M11 each close via a direct port of openvm-fv's RV32 proof, with
the `@[simp high]` P1-P3 platform axioms in `ZiskFv.PlatformScope`
discharging the 16-entry PMP loop / CLINT MMIO check / PMA alignment
chain that previously blocked simp reduction. The historical entries
are retained below for audit trail; each `*_pure_equiv_axiom` axiom
declaration has been deleted from its RV64D/*.lean file, and the
`*_pure_equiv` lemma is now proved directly.

### Entry M1 *(promoted to theorem 2026-04-22)*: `PureSpec.execute_LOADD_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/ld.lean`
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
  vendored `sail-riscv-lean@81c8c84f`).

### Entry M2 *(promoted to theorem 2026-04-22)*: `PureSpec.execute_STORED_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/sd.lean`
- **Statement (informal):** symmetric to M1 for
  `execute_STORE imm rs2 rs1 8`. Under `RISC_V_assumptions` +
  `sd_state_assumptions`, reduces to: `+4` to PC; the eight
  `state.mem.insert` chain encoded by `modify_memory_8`;
  retire-success.
- **Consumers:** `PureSpec.execute_STORED_pure_equiv`; consumed by
  `ZiskFv/Equivalence/StoreD.lean::equiv_SD_sail`.
- **Provenance:** `LeanRV64D/VmemUtils.lean::vmem_write_addr` +
  `LeanRV64D/InstsEnd.lean::execute_STORE`.

### Entry M3 *(promoted to theorem 2026-04-22)*: `PureSpec.execute_LOADWU_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/lwu.lean`
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

### Entry M4 *(promoted to theorem 2026-04-22)*: `PureSpec.execute_STOREW_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/sw.lean`
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

## Phase 3A Track S memory-model axioms (2026-04-22)

The SH (store halfword) and SB (store byte) sibling fan-out ships
two additional trusted memory-model axioms — narrow companions of
M2 (SD) / M4 (SW). Structurally identical to M2/M4 modulo the
`width` parameter and the `modify_memory_{1,2}` primitive; jointly
closable with M1-M4 under the same PMP/CLINT extension to
`RISC_V_assumptions` (see "Why M1-M4 exist" above).

### Entry M10 *(promoted to theorem 2026-04-22)*: `PureSpec.execute_STOREH_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/sh.lean`
- **Statement (informal):** narrow companion of M2/M4 for
  `execute_STORE imm rs2 rs1 2` (width 2). Under `RISC_V_assumptions`
  + `sh_state_assumptions` (rs1/rs2 readable, PC readable, address
  below `OpenVM_address_space_size`, **2-byte alignment**), reduces
  to: `+4` to PC; the two `state.mem.insert` writes encoded by
  `modify_memory_2`; retire-success.
- **Consumers:** `PureSpec.execute_STOREH_pure_equiv`; consumed by
  `ZiskFv/Equivalence/StoreH.lean::equiv_SH_sail` and transitively
  `equiv_SH_metaplan`.
- **Provenance:** `LeanRV64D/VmemUtils.lean::vmem_write_addr` +
  `LeanRV64D/InstsEnd.lean::execute_STORE` (width 2 path).

### Entry M11 *(promoted to theorem 2026-04-22)*: `PureSpec.execute_STOREB_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/sb.lean`
- **Statement (informal):** narrowest of the store family; companion
  of M2/M4/M10 for `execute_STORE imm rs2 rs1 1` (width 1). Under
  `RISC_V_assumptions` + `sb_state_assumptions` (rs1/rs2 readable,
  PC readable, address below `OpenVM_address_space_size` — **no
  alignment condition** since SB is byte-aligned), reduces to: `+4`
  to PC; the single `state.mem.insert` write encoded by
  `modify_memory_1`; retire-success.
- **Consumers:** `PureSpec.execute_STOREB_pure_equiv`; consumed by
  `ZiskFv/Equivalence/StoreB.lean::equiv_SB_sail` and transitively
  `equiv_SB_metaplan`.
- **Provenance:** `LeanRV64D/VmemUtils.lean::vmem_write_addr` +
  `LeanRV64D/InstsEnd.lean::execute_STORE` (width 1 path).

### Why M10-M11 exist

Identical obstruction class to M1-M4 — the same platform-config gap
in `RISC_V_assumptions` blocks closure via `simp`-reduction of the
Sail `execute_STORE` body through `vmem_write_addr`. The narrower
widths (2 and 1 bytes) are strictly simpler than the 4-byte SW / 8-byte
SD cases: SB even drops the alignment divisibility hypothesis from
`sb_state_assumptions`. A successful
`vmem_write_addr_aligned_equiv` lemma built from the PMP-OFF /
CLINT-disjoint / pma-writable witnesses would simultaneously retire
M2 (SD), M4 (SW), M10 (SH), and M11 (SB) — they share the exact same
Sail write-path skeleton, differing only in loop-bound / width
arguments.

No new closure machinery is required beyond what M1-M4 already need;
the four store axioms form a single jointly-closable cluster under
the memory-model extension catalogued in "Why M1-M4 exist".

## Control-flow axioms (Phase 2.5 D4b, path (b) — 2026-04-22)

### Entry C1 *(promoted to theorem 2026-04-22)*: `PureSpec.execute_JALR_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/jalr.lean`
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

## Phase 3A Branch control-flow axioms — **RETIRED 2026-04-23 (Phase 4 T-BR)**

C2a (BLT), C2b (BGE), C2c (BLTU), C2d (BGEU) were four narrow
single-opcode axioms introduced in Phase 3A alongside the branch-family
fan-out. Phase 4 Track T-BR replaced each with a direct proof port of
the BNE skeleton — no shared BitVec-bridge helper was needed because
Sail's `zopz0z*` comparators unfold directly to `.toInt`/`.toNatInt`
forms that align with the pure specs under the existing simp set.

Closures: `RV64D/{blt,bge,bltu,bgeu}.lean::execute_<OP>_pure_equiv`
are now direct lemmas (no axiom). `equiv_<OP>_metaplan`'s
`#print axioms` no longer shows any branch-family `*_pure_equiv_axiom`.
Gate surface shrank by 4.

## Phase 3A Load-family memory-model axioms (2026-04-22)

Track L fans out the five RV64IM sibling loads (LB, LBU, LH, LHU, LW)
off the shipped `LoadArchetype` macro (the zero-extension "copyb"
archetype validated by LWU / D4c). Of the five, only the three
**zero-extension** loads (LBU, LHU, LWU-sibling) fit the macro
directly — the three **signed-extension** loads (LB, LH, LW)
transpile to Zisk external ops `signextend_{b,h,w}` with
`is_external_op = 1` and route through the Binary Extension SM; the
macro's `load_archetype_copyb_circuit_holds` hardcodes
`is_external_op = 0`, `op = OP_COPYB = 1`.

Phase 3A Track L therefore ships only the two remaining copyb loads —
LHU (L3) and LBU (L5) — with corresponding memory-model axioms M7 and
M9. LW (L1), LH (L2), LB (L4) are **flag-and-stop** for a new
sign-extension-load archetype (Phase 3B or later); the axiom slots
M5 / M6 / M8 are reserved but not yet introduced.

### Entry M7 *(promoted to theorem 2026-04-22)*: `PureSpec.execute_LOADHU_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/lhu.lean`
- **Statement (informal):** narrow companion of M1 / M3 for
  `execute_LOAD imm rs1 rd true 2` (width 2, `is_unsigned = true`).
  Under `RISC_V_assumptions` + `lhu_state_assumptions` (two source
  bytes pinned, 2-byte alignment, address below `2^29`), reduces to
  `+4` to PC; conditional little-endian halfword-concatenation
  zero-extended into `rd`; retire-success.
- **Consumers:** `PureSpec.execute_LOADHU_pure_equiv`; consumed by
  `ZiskFv/Equivalence/LoadHU.lean::equiv_LHU_sail` and transitively
  `equiv_LHU_metaplan`.
- **Provenance:** `LeanRV64D/VmemUtils.lean::vmem_read_addr` +
  `LeanRV64D/InstsEnd.lean::execute_LOAD` (width 2, zero-extend path).

### Entry M9 *(promoted to theorem 2026-04-22)*: `PureSpec.execute_LOADBU_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/lbu.lean`
- **Statement (informal):** narrowest companion of M1 / M3 / M7 for
  `execute_LOAD imm rs1 rd true 1` (width 1, `is_unsigned = true`).
  Under `RISC_V_assumptions` + `lbu_state_assumptions` (one source
  byte pinned, address below `2^29`; 1-byte alignment is vacuous),
  reduces to `+4` to PC; conditional byte-zero-extension into `rd`;
  retire-success.
- **Consumers:** `PureSpec.execute_LOADBU_pure_equiv`; consumed by
  `ZiskFv/Equivalence/LoadBU.lean::equiv_LBU_sail` and transitively
  `equiv_LBU_metaplan`.
- **Provenance:** `LeanRV64D/VmemUtils.lean::vmem_read_addr` +
  `LeanRV64D/InstsEnd.lean::execute_LOAD` (width 1, zero-extend path).

### M5-M9 closure path (shared with M1 / M3)

M7 and M9 — together with M5, M6, M8 once the sign-extension load
archetype lands — share the M1 / M3 platform-config gap exactly: each
is a width / sign-extension specialization of the same
`vmem_read_addr_aligned_equiv` reduction blocked by ZisK's (absent)
PMP-OFF and CLINT-disjoint witnesses in `RISC_V_assumptions`. A single
Phase 2.6 / Phase 4 extension of `RISC_V_assumptions` with the
PMP-OFF + CLINT-disjoint hypotheses, plus the three reusable lemmas
enumerated in the "Why M1-M4 exist" section above, would retire M1,
M2, M3, M4, M7, M9 (and any future M5, M6, M8) together — the closure
is uniform over the `(width, is_unsigned)` axes and does not need a
per-opcode axiom chase.

### Phase 3A Track L flag-and-stop — LW / LH / LB

The signed-extension load opcodes LW (L1), LH (L2), LB (L4) transpile
via `riscv2zisk_context.rs:214,215,210` to Zisk `signextend_w` /
`signextend_h` / `signextend_b` — `BinaryE` external ops (opcodes
0x29 / 0x28 / 0x27; `zisk_ops.rs:419-421`). These route through the
operation bus to the Binary Extension SM, materially unlike the
copyb-shape loads the shipped `LoadArchetype` macro validates:

* mode is `is_external_op = 1`, `op = OP_SIGNEXTEND_{B,H,W}` (not
  pinned in `Transpiler.lean` yet);
* `c_packed` is populated by the BinaryE SM's bus reply, not by
  Main constraint 9 (`c = b`);
* the Main row's `b` lanes feed off the memory bus; the
  sign-extension step happens on the SM side.

Closing the signed-load family therefore requires either:

1. extending `LoadArchetype` with a new `load_archetype_signext_*`
   variant for the external-op path (parametric over the
   Op-literal ∈ {`OP_SIGNEXTEND_B`, `OP_SIGNEXTEND_H`,
   `OP_SIGNEXTEND_W`}), following the SLLW / `Spec.Shift` pattern for
   external-op Main-row spec with a bus match; or
2. authoring three per-opcode specs that combine a `matches_entry`
   bus-match hypothesis with the memory-bus `memory_entry_toField`
   packing.

Either path introduces a new `Tactics/*Archetype.lean` variant (or an
extension to `LoadArchetype` — **read-only per Phase 3A scope**) and
is out of scope for Phase 3A. LW / LH / LB are deferred to Phase 3B
alongside the ALU-ITYPE / DIV / UTYPE archetype work.

## Control-flow axioms (Phase 3A H2b/c/d, path (b) — 2026-04-22)

### Entry C3a *(promoted to theorem 2026-04-22)*: `PureSpec.execute_SHIFTIWOP_slliw_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/slliw.lean`
- **Statement (informal):** under the standard register-state
  hypotheses (r1 readable, rd mapping, PC readable), the Sail
  `execute_instruction (.SHIFTIWOP (shamt, r1, rd, sopw.SLLIW))`
  threaded through `state` reduces to the pure-spec block: write
  `nextPC = PC + 4`, conditionally write `sign_extend (shift_bits_left
  (extractLsb r1_val 31 0) shamt)` to `rd` (or no-op when `rd = 0`),
  retire success.
- **Consumers:** `PureSpec.execute_SHIFTIWOP_slliw_pure_equiv`;
  consumed by `ZiskFv/Equivalence/ShiftLI.lean::equiv_SLLIW_sail`.
- **Provenance:** `LeanRV64D/InstsEnd.lean::execute_SHIFTIWOP`
  (line 65520).

### Entry C3b *(promoted to theorem 2026-04-22)*: `PureSpec.execute_SHIFTIWOP_srliw_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/srliw.lean`
- **Statement (informal):** same as C3a with `sopw.SLLIW → sopw.SRLIW`
  and `shift_bits_left → shift_bits_right`.
- **Consumers:** `PureSpec.execute_SHIFTIWOP_srliw_pure_equiv`;
  consumed by `ZiskFv/Equivalence/ShiftRLI.lean::equiv_SRLIW_sail`.
- **Provenance:** same as C3a.

### Entry C3c *(promoted to theorem 2026-04-22)*: `PureSpec.execute_SHIFTIWOP_sraiw_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/sraiw.lean`
- **Statement (informal):** same as C3a with `sopw.SLLIW → sopw.SRAIW`
  and `shift_bits_left → shift_bits_right_arith`.
- **Consumers:** `PureSpec.execute_SHIFTIWOP_sraiw_pure_equiv`;
  consumed by `ZiskFv/Equivalence/ShiftRAI.lean::equiv_SRAIW_sail`.
- **Provenance:** same as C3a.

### Why C3a-C3c exist

Unlike SLLW/SRLW/SRAW (register-variant W-shifts), whose Sail-side
equivalence closes directly against `execute_RTYPEW'` —
a refactored form of `execute_RTYPEW` provided by
`Fundamentals/Execution.lean::execute_RTYPEW'` + the `@[simp]` lemma
`execute_RTYPEW_eq_execute_RTYPEW'` — the W-variant immediate shifts
route through Sail's `execute_SHIFTIWOP`, for which no such refactor
triple exists in `Fundamentals/Execution.lean`. The Phase 3A H2
invariants forbid mutating `Fundamentals/Execution.lean`, so the
Sail-level equivalence is axiomatized pointwise per-opcode.

**Closure path.** Add `execute_SHIFTIWOP_pure` + `execute_SHIFTIWOP'`
+ `execute_SHIFTIWOP_eq_execute_SHIFTIWOP'` to `Fundamentals/Execution.
lean` (mechanical port of the existing `execute_RTYPEW_pure` /
`execute_RTYPEW'` / `execute_RTYPEW_eq_execute_RTYPEW'` triple,
adjusted for the `BitVec 5` shamt signature and the `sopw` opcode
enum). Under that refactor, each C3x axiom becomes a direct `simp`
closure mirroring `sllw.lean::execute_RTYPE_sllw_pure_equiv` with the
`r2` register-read step dropped (the shift amount is an immediate,
not a register read). Estimated 60-80 lines total across the three
opcodes — same shape as the openvm-fv SLLI/SRLI/SRAI proofs.

### Entry C4 *(promoted to theorem 2026-04-22)*: `PureSpec.execute_MULW_pure_equiv_axiom`

- **File:** `ZiskFv/RV64D/mulw.lean`
- **Statement (informal):** under the standard register-state
  hypotheses (r1/r2 readable, rd mapping, PC readable), the Sail
  `execute_instruction (.MULW (r2, r1, rd))` threaded through the
  `writeReg nextPC (PC+4); execute …` prelude reduces to the pure-spec
  block: write `nextPC = PC + 4`, conditionally sign-extend the
  low-32-bit signed product of `r1_val` / `r2_val` to 64 bits and
  write to `rd` (or no-op when `rd = 0`), retire success.
- **Consumers:** `PureSpec.execute_MULW_pure_equiv`; consumed by
  `ZiskFv/Equivalence/MulW.lean::equiv_MULW_sail` and transitively
  `equiv_MULW_metaplan`.
- **Provenance:** `LeanRV64D/InstsEnd.lean::execute_MULW` (line 66799).

### Why C4 exists

Parallels C3a-C3c exactly: `Fundamentals/Execution.lean` provides
`execute_RTYPEW_pure` / `execute_RTYPEW'` / `execute_RTYPEW_eq_…`
for SLLW/SRLW/SRAW but no analogous triple for MULW. The Phase 3A
invariants forbid mutating `Fundamentals/Execution.lean`, so MULW's
Sail equivalence is axiomatized pointwise pending a future
`execute_MULW_pure` / `execute_MULW'` / `execute_MULW_eq_…` refactor
(mechanical port of the `execute_RTYPEW` triple, adjusted for
`to_bits_truncate` / `sign_extend` plumbing). Estimated 40-60 lines
once that refactor lands.

## Phase 3C T-RT transpile axioms (2026-04-22)

Six transpile axioms for the Phase 3C ALU-RTYPE fan-out (SUB, AND, OR,
XOR, SLT, SLTU). All six mirror `transpile_ADD`'s shape: one Main-AIR
row from `create_register_op`, `is_external_op = 1`, `m32 = 0`,
`set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`,
`a`/`b` lanes = `xreg(rs1)`/`xreg(rs2)`. SUB / AND / OR / XOR
additionally pin `flag = 0` (their Binary-SM `op_*` functions always
return `(_, false)`); SLT / SLTU leave `flag` unconstrained because
the Binary SM writes the comparison verdict into it.

### Entry T-RT transpile row: `transpile_SUB`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Sub.equiv_SUB_metaplan` (indirect,
  via bus-match + `Spec.Sub.sub_compositional`).
- **Provenance:** `zisk/core/src/riscv2zisk_context.rs:134`
  (`"sub" → create_register_op(..., "sub", 4)`) +
  `zisk/core/src/zisk_ops.rs:393` (opcode `0x0b = 11`).
- **Closure path:** trusted (transpiler-contract axiom; not a proof
  obligation). Retires only if ZisK's Rust transpiler is replaced.

### Entry T-RT transpile row: `transpile_AND`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.And.equiv_AND_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:152` +
  `zisk_ops.rs:396` (opcode `0x0e = 14`).
- **Closure path:** trusted.

### Entry T-RT transpile row: `transpile_OR`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Or.equiv_OR_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:141-150` +
  `zisk_ops.rs:397` (opcode `0x0f = 15`).
- **Closure path:** trusted.

### Entry T-RT transpile row: `transpile_XOR`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Xor.equiv_XOR_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:138` +
  `zisk_ops.rs:398` (opcode `0x10 = 16`).
- **Closure path:** trusted.

### Entry T-RT transpile row: `transpile_SLT`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Slt.equiv_SLT_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:136` +
  `zisk_ops.rs:389` (opcode `0x07 = 7`, shared with BLT / BGE).
- **Closure path:** trusted. Note: `flag` is left as an unconstrained
  Binary-SM output (vs. pinned = 0 for SUB/AND/OR/XOR) because
  `op_lt` returns `(1, true)` when `a < b`.

### Entry T-RT transpile row: `transpile_SLTU`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Sltu.equiv_SLTU_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:137` +
  `zisk_ops.rs:388` (opcode `0x06 = 6`, shared with BLTU / BGEU).
- **Closure path:** trusted. Same `flag`-unconstrained treatment as
  SLT.

## Phase 3C T-W transpile axioms (2026-04-23)

Three transpile axioms for the Phase 3C RTYPEW + ADDIW fan-out
(ADDW, SUBW, ADDIW). All three mirror the `m32 = 1` path taken by
the shift archetype (SLLW / SRLW / SRAW), dispatching to the
**Binary** SM (not `BinaryExtension`) via distinct `OP_ADD_W` /
`OP_SUB_W` literals. `flag = 0` is pinned for all three (their
Binary-SM `op_*` hooks return `(_, false)` — `zisk_ops.rs:572`,
`zisk_ops.rs:596`). ADDIW shares `OP_ADD_W + m32 = 1` with ADDW at
the operation-bus layer; the only difference is the source-b routing
(register for ADDW, sign-extended 12-bit imm for ADDIW).

### Entry T-W transpile row: `transpile_ADDW`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Addw.equiv_ADDW_metaplan` (indirect,
  via bus-match + `Spec.Addw.addw_compositional`).
- **Provenance:** `zisk/core/src/riscv2zisk_context.rs:153`
  (`"addw" → create_register_op(..., "add_w", 4)`) +
  `zisk/core/src/zisk_ops.rs:408` (opcode `0x1a = 26`, type
  `Binary`).
- **Closure path:** trusted (transpiler-contract axiom; not a proof
  obligation). Retires only if ZisK's Rust transpiler is replaced.

### Entry T-W transpile row: `transpile_SUBW`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Subw.equiv_SUBW_metaplan`.
- **Provenance:** `zisk/core/src/riscv2zisk_context.rs:154`
  (`"subw" → create_register_op(..., "sub_w", 4)`) +
  `zisk/core/src/zisk_ops.rs:409` (opcode `0x1b = 27`, type
  `Binary`).
- **Closure path:** trusted.

### Entry T-W transpile row: `transpile_ADDIW`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Addiw.equiv_ADDIW_metaplan`.
- **Provenance:** `zisk/core/src/riscv2zisk_context.rs:184-194`
  (`"addiw" → immediate_op(..., "add_w", 4)`, line 192) +
  `zisk/core/src/zisk_ops.rs:408` (opcode `OP_ADD_W = 0x1a =
  26`, shared with ADDW). **Routing note.** Per `create_imm_op`
  inspection, ADDIW emits `OP_ADD_W + m32 = 1` (not `OP_ADD + m32 =
  1`); this pins the T-W pre-flight finding. A degenerate
  `rd = 0 ∧ rs1 = 0 ∧ imm = 0` nop case is shunted to `self.nop(i,
  4)` at line 190 and is outside this axiom's nominal row shape.
- **Closure path:** trusted.

## Phase 3C T-RT Sail-equivalence escape-hatch axioms — **RETIRED 2026-04-23 (Phase 4 T-SLT)**

C5 (slt) and C6 (sltu) — Phase 3B shipped `RV64D/{slt,sltu}.lean` with a
`dite_cond_eq_false` residual on `BitVec.setWidth 64 (if .toInt < …)` vs.
`if .slt …`. Phase 4 T-SLT closed the bridge with a standalone `h_bridge`
lemma (`by_cases` on the signed comparison, then `simp` on both forms)
and replaced the escape-hatch axioms with direct `execute_RTYPE_slt_pure_equiv` /
`execute_RTYPE_sltu_pure_equiv` lemmas.

## Phase 3C T-IT transpile axioms (2026-04-23)

Six transpile axioms for the Phase 3C ALU-ITYPE fan-out (ADDI, ANDI,
ORI, XORI, SLTI, SLTIU). All six route through
`immediate_op` / `immediate_op_or_x0_copyb` and reuse the
corresponding RTYPE sibling's Zisk opcode literal (ADDI uses `OP_ADD`,
ANDI uses `OP_AND`, etc. — the Binary SM cannot distinguish the
register-register from the register-immediate variant). The only
structural difference from the T-RT siblings is the `b` lane source:
`b_lo` / `b_hi` are caller-supplied Goldilocks representatives of
the sign-extended 12-bit ITYPE immediate's 32-bit lanes (the same
treatment `transpile_LUI` applies to its u20 immediate). `m32 = 0`
across all six (ITYPE is 64-bit on RV64I; ADDIW uses `OP_ADD_W`
under Track T-W).

### Entry T-IT transpile row: `transpile_ADDI`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Addi.equiv_ADDI_metaplan`.
- **Provenance:** `zisk/core/src/riscv2zisk_context.rs:160-174`
  (`"addi" → immediate_op_or_x0_copyb(..., "add", 4)` on the
  non-degenerate path) + `zisk/core/src/zisk_ops.rs` opcode
  `OP_ADD = 10` (shared with ADD).
- **Closure path:** trusted (transpiler-contract axiom; not a proof
  obligation). Retires only if ZisK's Rust transpiler is replaced.

### Entry T-IT transpile row: `transpile_ANDI`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Andi.equiv_ANDI_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:182`
  (`"andi" → immediate_op(..., "and", 4)`) + `OP_AND = 14` (shared
  with AND).
- **Closure path:** trusted.

### Entry T-IT transpile row: `transpile_ORI`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Ori.equiv_ORI_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:181`
  (`"ori" → immediate_op_or_x0_copyb(..., "or", 4)` non-degenerate
  path) + `OP_OR = 15` (shared with OR).
- **Closure path:** trusted.

### Entry T-IT transpile row: `transpile_XORI`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Xori.equiv_XORI_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:178`
  (`"xori" → immediate_op_or_x0_copyb(..., "xor", 4)` non-degenerate
  path) + `OP_XOR = 16` (shared with XOR).
- **Closure path:** trusted.

### Entry T-IT transpile row: `transpile_SLTI`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Slti.equiv_SLTI_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:176`
  (`"slti" → immediate_op(..., "lt", 4)`) + `OP_LT = 7` (shared with
  BLT / BGE / SLT).
- **Closure path:** trusted. Like SLT, `flag` is unconstrained — the
  Binary-SM writes the signed comparison verdict.

### Entry T-IT transpile row: `transpile_SLTIU`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Sltiu.equiv_SLTIU_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:177`
  (`"sltiu" → immediate_op(..., "ltu", 4)`) + `OP_LTU = 6` (shared
  with BLTU / BGEU / SLTU).
- **Closure path:** trusted. SLTIU's immediate is still sign-extended
  on the bus (per the RV64I spec); only the Binary-SM's comparator is
  unsigned. `flag` unconstrained per SLT/SLTU precedent.

## Phase 3C T-IT Sail-equivalence escape-hatch axioms — **RETIRED 2026-04-23 (Phase 4 T-SLT)**

C7 (slti) and C8 (sltiu) — same BitVec.setWidth / .slt residual as
C5/C6, closed by the same `h_bridge` lemma pattern. `SltiEquivHelper`
deleted; `execute_ITYPE_slti_pure_equiv` and
`execute_ITYPE_sltiu_pure_equiv` are now direct lemmas in the
respective RV64D files.

## Phase 3C T-SL transpile axioms (2026-04-23)

Three transpile axioms for the Phase 3C signed-load fan-out (LW, LH,
LB). All three mirror the load-family structure of `transpile_LWU` /
`transpile_LHU` / `transpile_LBU` but use the `OP_SIGNEXTEND_*`
external ops (`zisk_ops.rs:419-421`, type `BinaryE`) instead of
`OP_COPYB` / internal op. The Main row pins `is_external_op = 1`,
`flag = 0`, `set_pc = 0`, `store_pc = 0`,
`jmp_offset1 = jmp_offset2 = 4`, `a` lanes = `xreg(rs1)`; `m32 = 1`
for LW (the `"signextend_w"` string contains `"_w"`), `m32 = 0` for
LH / LB.

Three new Zisk-opcode constants ship alongside the transpile axioms:
`OP_SIGNEXTEND_B = 39`, `OP_SIGNEXTEND_H = 40`, `OP_SIGNEXTEND_W = 41`.
These are simp-attribute `@[simp] def` definitions in
`Fundamentals/Transpiler.lean`, not axioms — they are trusted only
via the transpile axioms that reference them (same treatment as
`OP_COPYB` / `OP_EQ` / `OP_SLL_W` etc.).

### Entry T-SL transpile row: `transpile_LW`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Lw.equiv_LW_metaplan` (indirect,
  via bus-match + `Spec.LoadWord.lw_compositional`).
- **Provenance:** `zisk/core/src/riscv2zisk_context.rs:214`
  (`"lw" → load_op(..., "signextend_w", 4, 4)`) +
  `zisk/core/src/zisk_ops.rs:421` (opcode `0x29 = 41`).
- **Closure path:** trusted (transpiler-contract axiom; not a proof
  obligation). Retires only if ZisK's Rust transpiler is replaced.

### Entry T-SL transpile row: `transpile_LH`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Lh.equiv_LH_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:212` + `zisk_ops.rs:420`
  (opcode `0x28 = 40`).
- **Closure path:** trusted.

### Entry T-SL transpile row: `transpile_LB`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Lb.equiv_LB_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:210` + `zisk_ops.rs:419`
  (opcode `0x27 = 39`).
- **Closure path:** trusted.

## Phase 3C T-SL Sail-equivalence escape-hatch axioms — **RETIRED 2026-04-23 (Phase 4 T-LW)**

C9 (lw) — Phase 3B shipped a theorem statement with
`is_unsigned = true` in the Sail `LOAD` call; that flag makes Sail
zero-extend while the pure spec sign-extends, so the theorem was
actually false. Phase 4 T-LW fixed the statement (`is_unsigned =
false`, matching RV64 LW's signed-load semantics) — after the fix,
the existing tactic chain closes. `LoadEquivHelper` deleted;
`execute_LOADW_pure_equiv` consumed directly. LH / LB never needed
escape-hatches; they still close under their original tactic
skeletons.

## Phase 3C T-D transpile axioms (2026-04-23)

Four transpile axioms for the Phase 3C DIV/REM fan-out (DIV, DIVU,
REM, REMU). All four mirror `transpile_MUL`'s shape: one Main-AIR row
from `create_register_op`, `is_external_op = 1`, `m32 = 0`,
`set_pc = 0`, `store_pc = 0`, `jmp_offset1 = jmp_offset2 = 4`,
`a`/`b` lanes = `xreg(rs1)`/`xreg(rs2)`. The Main `flag` column is
left unconstrained by all four — it is populated on the Arith SM's
`div_by_zero` output rather than pinned by the Main transpile
contract (Phase 4 audit handles the div-by-zero path).

### Entry T-D transpile row: `transpile_DIVU`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Divu.equiv_DIVU_metaplan`
  (indirect, via bus-match + `Spec.Divu.divu_compositional`).
- **Provenance:** `zisk/core/src/riscv2zisk_context.rs:249`
  (`"divu" → create_register_op(..., "divu", 4)`) +
  `zisk/core/src/zisk_ops.rs:430` (opcode `0xb8 = 184`).
- **Closure path:** trusted (transpiler-contract axiom). Retires only
  if ZisK's Rust transpiler is replaced.

### Entry T-D transpile row: `transpile_REMU`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Remu.equiv_REMU_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:253` +
  `zisk_ops.rs:431` (opcode `0xb9 = 185`).
- **Closure path:** trusted.

### Entry T-D transpile row: `transpile_DIV`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Div.equiv_DIV_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:248` +
  `zisk_ops.rs:432` (opcode `0xba = 186`).
- **Closure path:** trusted. Signed / unsigned distinction lives
  inside the Arith SM witnesses (`na`/`nb`/`np`/`nr`) — the Main
  transpile contract is uniform across signed and unsigned DIV.

### Entry T-D transpile row: `transpile_REM`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Consumer:** `ZiskFv.Equivalence.Rem.equiv_REM_metaplan`.
- **Provenance:** `riscv2zisk_context.rs:252` +
  `zisk_ops.rs:433` (opcode `0xbb = 187`).
- **Closure path:** trusted.

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
- **2026-04-22 — Phase 3A L3/L5.** M7 (LHU) and M9 (LBU) introduced —
  narrow width-2 and width-1 zero-extension load siblings of M1/M3.
  Retiring `vmem_read_addr_aligned_equiv` (the shared closure for
  M1-M4) retires M7 and M9 together. LW / LH / LB (M5 / M6 / M8 slots
  reserved) deferred as flag-and-stop — they transpile to Zisk
  external `signextend_*` ops, incompatible with the copyb-only
  `LoadArchetype` macro; a new sign-extension-load archetype is
  Phase 3B work.
- **2026-04-22 — Phase 3A B1-B4.** C2a-C2d introduced (BLT / BGE / BLTU
  / BGEU). Distinct from both M1-M4 and C1: no platform-config gap and
  no CSR-read chain — these are structurally closable via the BNE-style
  skeleton with a per-opcode comparator case-split, axiomatized in
  lockstep to keep Track B tractable. Estimated consolidated closure
  ≈1 day total; no `RISC_V_assumptions` extension needed.
- **2026-04-22 — Phase 3A S1-S2.** M10 (SH) and M11 (SB) introduced
  as narrow width-2 / width-1 companions of M2 (SD) / M4 (SW). Same
  obstruction class (PMP/CLINT platform-config gap); jointly closable
  with M1-M4 under a single `vmem_write_addr_aligned_equiv` lemma.
  Total store-family trusted axioms now: M2 (SD), M4 (SW), M10 (SH),
  M11 (SB).
- **2026-04-22 — Phase 3A H1-H6.** **No Sail-equivalence axioms
  introduced.** SLL / SRL / SRA / SLLI / SRLI / SRAI shipped six new
  transpile axioms (`transpile_SLL`, `transpile_SRL`, `transpile_SRA`,
  `transpile_SLLI`, `transpile_SRLI`, `transpile_SRAI` in
  `Fundamentals/Transpiler.lean`) and associated `OP_SLL = 33`,
  `OP_SRL = 34`, `OP_SRA = 35` Zisk-opcode constants plus a
  `shamt_b_lo : BitVec 6 → FGL` helper for the immediate-shamt lane
  encoding. The pure-spec Sail equivalences all closed directly via
  the SLLW/SRLW precedent (`execute_RTYPE'` for registers,
  `execute_SHIFTIOP'` for immediates). Per-opcode effort matched the
  ½-day estimate from Phase 2.5 D4. All transpile axioms are pure
  specs of the Rust transpiler; no RISC_V_assumptions or LeanRV64D
  chain obstructions encountered.
- **2026-04-22 — Phase 3A H2b.** C3a (SLLIW) introduced. Obstruction:
  `Fundamentals/Execution.lean` lacks a
  `execute_SHIFTIWOP_pure`/`'`/`_eq_` refactor triple analogous to
  the `execute_RTYPEW` triple that SLLW/SRLW/SRAW use. The Phase 3A
  H2 invariants forbid mutating `Fundamentals/Execution.lean`, so
  C3a is added pointwise; C3b/C3c will follow in sibling commits.
- **2026-04-22 — Phase 3A M3 (salvage).** C4 (MULW) introduced.
  Same obstruction class as C3a-C3c: missing `execute_MULW_pure` /
  `execute_MULW'` / `execute_MULW_eq_…` refactor triple in
  `Fundamentals/Execution.lean`. The Track M agent returned with an
  incomplete proof referencing unqualified `to_bits_truncate` /
  `sign_extend` identifiers; salvage axiomatized per the C3 precedent.
- **2026-04-22 — Phase 3A H2c.** C3b (SRLIW) introduced. Same
  obstruction class as C3a (SLLIW), same closure path — a future
  commit that adds the `execute_SHIFTIWOP` refactor triple to
  `Fundamentals/Execution.lean` retires C3a and C3b together.
- **2026-04-22 — Phase 3A H2d.** C3c (SRAIW) introduced, completing
  the W-variant immediate-shift triple. Retiring the C3a/b/c group
  requires one Execution.lean extension (the `execute_SHIFTIWOP`
  refactor) plus three mechanical ~20-line proofs per opcode.
- **2026-04-22 — Phase 3C Track T-U.** **No Sail-equivalence axioms
  introduced.** LUI and AUIPC shipped two new transpile axioms
  (`transpile_LUI`, `transpile_AUIPC` in
  `Fundamentals/Transpiler.lean`) with the existing `OP_COPYB = 1`
  and `OP_FLAG = 0` Zisk-opcode constants (both already catalogued).
  The Phase 3B pure-spec equivalences closed directly against
  `LeanRV64D.Functions.execute_UTYPE` — LUI via
  `wX_write_xreg_{zero,non_zero}_equiv`; AUIPC via the same plus
  `readReg_succ (writeReg_read_diff h_input_pc (PC ≠ nextPC))` to
  bridge the `get_arch_pc` read-after-write-nextPC. No new M/C/P
  axioms required. Archetype macros: `UTypeArchetype.lean` (new,
  two sub-archetypes — `lui_archetype_*` and `auipc_archetype_*`),
  no secondary-SM bus entry on either path. The metaplan bus
  closure consumes the existing shape-(c)
  `bus_effect_matches_sail_jump_rrw` with no modifications.

  The transpile axioms encode:
  * `transpile_LUI`: `op = OP_COPYB, is_external_op = 0,
    set_pc = 0, store_pc = 0, m32 = 0, jmp_offset1 = 4,
    jmp_offset2 = 4, a_lo = a_hi = 0, b_lo = imm_lo,
    b_hi = imm_hi`. **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
    **Consumer:** `ZiskFv.Equivalence.Lui.equiv_LUI_metaplan`.
    **Provenance:** `zisk/core/src/riscv2zisk_context.rs:1009`
    (`fn lui`). **Closure path:** trusted spec of Rust transpiler;
    audit scope — any change to `fn lui` requires re-signing this
    axiom against the Rust source.
  * `transpile_AUIPC`: `op = OP_FLAG, is_external_op = 0,
    set_pc = 0, store_pc = 1, m32 = 0, jmp_offset1 = 4,
    jmp_offset2 = imm_offset, a_lo = a_hi = b_lo = b_hi = 0`.
    **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
    **Consumer:** `ZiskFv.Equivalence.Auipc.equiv_AUIPC_metaplan`.
    **Provenance:** `zisk/core/src/riscv2zisk_context.rs:907`
    (`fn auipc`). **Closure path:** trusted spec of Rust transpiler;
    audit scope.
- **2026-04-22 — Phase 3C T-RT.** Six transpile axioms shipped for
  ALU-RTYPE fan-out (SUB, AND, OR, XOR, SLT, SLTU). SLT / SLTU
  additionally triggered the new **C5 / C6** escape-hatch axioms —
  the Phase 3B `execute_RTYPE_slt_pure_equiv` /
  `execute_RTYPE_sltu_pure_equiv` proofs shipped with an unclosed
  `BitVec.setWidth` / `BitVec.slt` bridge (the main branch hides
  this because no module imports those two RV64D files). C5 and C6
  are catalogued in `ZiskFv/RV64D/SltEquivHelper.lean` alongside
  lightly-renamed `SltInput'` / `SltuInput'` / `slt_pure` /
  `sltu_pure` reprints so the broken upstream file stays untouched
  per the Phase 3C read-only invariant. Same transpile-only-plus-
  narrow-Sail-axiom shipping pattern as Phase 3A H1-H6.
- **2026-04-23 — Phase 3C T-IT.** Six transpile axioms shipped for
  ALU-ITYPE fan-out (ADDI, ANDI, ORI, XORI, SLTI, SLTIU). SLTI /
  SLTIU additionally triggered the new **C7 / C8** escape-hatch
  axioms — same `BitVec.setWidth` / `BitVec.slt` obstruction as
  C5 / C6 (the Phase 3B `execute_ITYPE_slti_pure_equiv` /
  `execute_ITYPE_sltiu_pure_equiv` proofs inherit the SLT / SLTU
  failure shape verbatim). C7 / C8 are catalogued in
  `ZiskFv/RV64D/SltiEquivHelper.lean` alongside lightly-renamed
  `SltiInput'` / `SltiuInput'` / `slti_pure` / `sltiu_pure` reprints.
  The archetype reuses `Tactics.ALURTypeArchetype` verbatim (the
  circuit-level `main_c_packed = bus_entry.c_lo + c_hi * 2^32`
  identity is b-source-agnostic); `ALUITypeArchetype.lean` is a
  shallow rebranded alias to keep track-T-IT consumer sites
  textually symmetric with T-RT. No new OP constants introduced
  (all six ITYPE opcodes piggyback on their RTYPE siblings'
  literals). ADDIW is **not** a T-IT deliverable — per
  `riscv2zisk_context.rs:184-193` `addiw` emits
  `immediate_op(..., "add_w", 4)` (OP_ADD_W, m32=1), so it belongs
  to Track T-W.
- **2026-04-23 — Phase 3C T-D.** **No Sail-equivalence axioms
  introduced.** DIV, DIVU, REM, REMU shipped four new transpile
  axioms (`transpile_DIV`, `transpile_DIVU`, `transpile_REM`,
  `transpile_REMU` in `Fundamentals/Transpiler.lean`) alongside the
  `OP_DIV = 186` / `OP_DIVU = 184` / `OP_REM = 187` / `OP_REMU = 185`
  Zisk-opcode constants. The Phase 3B pure-spec equivalences
  (`execute_DIVREM_{div,divu,rem,remu}_pure_equiv`) closed directly
  against `LeanRV64D.Functions.execute_DIV'` / `execute_REM'` with
  no obstruction. Archetype macros live in
  `ZiskFv/Tactics/ArithSMArchetype.lean` (new for T-D,
  mirroring `MulArchetype`): two archetype lemmas —
  `arith_archetype_div_bus_match` (primary, quotient in `a[]`) and
  `arith_archetype_rem_bus_match` (secondary, remainder in `d[]`).
  Both discharge the Main+Arith bus-match identity by destructuring
  `matches_entry` only; the Arith-internal carry-chain correctness
  (division chains 31–38 under `div = 1`) is **not** axiomatized
  separately — it enters the end-to-end proof exclusively via the
  structural bus / rd-match hypotheses on `equiv_*_metaplan` (same
  treatment as the MUL family). Retiring those structural hypotheses
  is Phase 4 audit scope.
- **2026-04-23 — Phase 4 T-BR.** **4 axioms retired** (C2a–d, branches).
  BLT/BGE/BLTU/BGEU `execute_<OP>_pure_equiv` are now direct lemmas —
  port of the BNE skeleton with the case-split predicate swapped to
  the per-opcode comparator. No shared BitVec bridge was needed: Sail's
  `zopz0z{I,KzJ}_{s,u}` unfold directly to the `.toInt`/`.toNatInt`
  forms the pure specs already use, and simp closes the
  `Int.ofNat` / `Nat.lt`-vs-`Int.lt` coercion on its own. Confirmed via
  `#print axioms ZiskFv.Equivalence.BranchLessThan.equiv_BLT_metaplan`
  — only LeanRV64D platform + kernel axioms remain.
- **2026-04-23 — Phase 4 T-SLT.** **4 axioms retired** (C5, C6, C7,
  C8 — slt/sltu/slti/sltiu). Each Phase 3B `execute_<Op>_pure_equiv`
  was failing on the final `BitVec.setWidth 64 (if .toInt < …)` ↔
  `if .slt …` equivalence. Closed via a standalone `h_bridge` lemma
  per file (`by_cases` on the comparator, then `simp` reduces both
  forms), taking `maxHeartbeats 400000`. The three helper files
  (`Slt`/`Slti`-EquivHelper) were deleted; 5 consumer `Equivalence/*`
  files rewired to import the upstream RV64D modules and call the
  lemmas directly.
- **2026-04-23 — Phase 4 T-LW.** **1 axiom retired** (C9, lw). The
  Phase 3B theorem statement passed `is_unsigned = true` to Sail's
  `LOAD` — that flag makes Sail zero-extend, but the pure spec
  sign-extends, so the theorem was structurally false and `grind`
  rightly refused. Phase 4 fixed the statement (`is_unsigned =
  false`, matching RV64 LW's signed-load semantics); the existing
  proof then closed without further intervention.
  `LoadEquivHelper` deleted, `Equivalence/Lw` rewired.

---

## Trust surface analysis — 2026-04-25

**Audience.** This section is for someone trying to determine
which axioms and *active hypotheses* must change for confidence
that ZisK correctly implements RV64IM. It supplements the
opcode-level entries above with a categorization by the kind of
trust each item embodies.

### Active axiom inventory (76 total — 2026-04-25 snapshot; see "Inventory update — 2026-04-27" below for current state)

Full list via:

```
grep -rh "^\s*axiom " ZiskFv/ --include="*.lean" \
  | grep -v "axiom itself" | awk '{print $2}' | sort -u
```

Categorized:

| # | Category | Count | Confidence-blocking? | Retirement path |
|---|---|---|---|---|
| 1 | Transpile axioms | 63 | **Yes — most** | Independent audit of `riscv2zisk_context.rs` (or Rust-side proof framework) |
| 2 | Arith lookup axioms | 4 | **Yes — moderate** | Formalize plookup / grand-product soundness in Lean |
| 3 | Platform axioms | 4 | Mild (scope-honest) | Only retire if ZisK's deployment changes |
| 4 | Sail-equivalence axioms | 5 | **No — pure tech debt** | Unfold the corresponding Sail bodies (mechanical) |

### Category 4 in depth — Sail-equivalence axioms ARE NOT trust expansion

The 5 axioms (`execute_FENCE_pure_equiv_axiom`,
`execute_DIVREM_{divuw,divw,remuw,remw}_pure_equiv_axiom`) all have
the shape

```
execute_instruction (instruction.<X> …) state =
  (do Sail.writeReg Register.nextPC <pc+4>; <result>) state
```

This is a **Sail-internal reduction** — what `execute_instruction`
computes when applied to a specific instruction. We could prove it
by unfolding the Sail definition (which is a Lean `def` produced
by Sail's auto-translation) and `simp`-ing through 100–300 lines
of monadic boilerplate. We took the shortcut and asserted the
result instead.

Important: **this does not add Sail to the trust base beyond what
"Sail RISC-V is the spec" already entails.** The Sail spec is the
specification regardless. The axiom asserts a *consequence* of the
spec, not a new claim about RV64IM. Retirement = mechanical proof
work; zero confidence gain.

These axioms exist for FENCE and the four `*W` divides because
their Sail bodies have CSR reads + barrier matches (FENCE) or
nested let/if/`Int.tdiv`-style logic (`*W` divides) that are
syntactically painful to unfold even though semantically trivial.

### Category 3 — platform axioms

`pmpCheck_is_pure_none`, `pmaCheck_is_pure_none`,
`within_clint_is_false`, `update_elp_state_is_pure_unit`. Each says
"this Sail privileged-mode feature is inert in ZisK's
configuration." Won't retire unless ZisK's deployment turns on the
feature; out of RV64IM scope by definition.

### Category 2 — Arith lookup axioms

Four axioms in `Airs/Arith/{ArithTable,ArithRangeTable}.lean`. They
encode plookup soundness in a tightly bundled form:
`arith_table_row_witness_unsigned` directly states "if Lean trace
columns `(op, m32)` take certain values, then sign-witness columns
`(na, nb, np, nr)` are forced to zero." This packages **two
distinct claims**:

1. **Table content correctness** — that the `arith_table.pil`
   row for `(MULU, m32=0)` really has `(0, 0, 0, 0)` in the
   sign-witness columns. Mechanically extractable from
   `arith_table.pil`; we don't currently extract it.
2. **Lookup-linkage soundness** — that the trace's claim "I'm row
   X of the table" is enforced by the grand-product polynomial.
   This is plookup / logUp soundness; standard ZK math.

Cleaner factorization (not yet implemented):

- Extract the arith_table rows into a Lean `def` (constant data).
- One `axiom` for plookup soundness ("if grand-product check
  passes, multiset inclusion holds").
- Per-opcode theorems derive the witness mapping from the data + 1
  axiom.

This would split a soundness-relevant axiom (lookup linkage) from
a verifiable claim (table content), letting the latter be checked
by inspection / extraction. Not yet shipped.

### Category 1 — transpile axioms (the elephant)

63 axioms, one per RV64IM opcode. Each says "the Rust function in
`zisk/core/src/riscv2zisk_context.rs` for this opcode emits
a Main AIR row with these specific column values."

**These are unverified against the Rust source.** A mismatch
(misread arm, Rust code change, typo) silently makes the whole
proof chain about a phantom row that the implementation never
actually emits.

Retirement options:

- **Audit by inspection.** Person reads each Rust arm, verifies
  the axiom matches. ~weeks of careful work; doesn't scale to
  refactors.
- **Rust-side proof framework.** Use Aeneas / Verus / a
  Rust-verifying tool that proves properties of `*.rs` source. Our
  axioms become theorems with Rust-source provenance. Substantial
  infrastructure effort; not a current ZisK direction.
- **Trace-based testing.** Run real binaries, compare emitted AIR
  rows against axiom claims. Provides counterexample detection,
  not a formal proof.

This is the **biggest unverified surface** for "ZisK ↔ RV64IM."
Bounded above by the correctness of a 63-row hand-transcription
from Rust to Lean.

### Active hypotheses — also part of the trust surface

The active hypotheses on metaplan theorems are NOT axioms but they
behave like per-application axioms: callers must supply them, and
if a hypothesis is too strong (excludes valid inputs) or false
(asserts something the implementation doesn't satisfy), the proof
delivers no useful guarantee.

Re-evaluated for confidence impact (correcting earlier glib
dismissals):

| Hypothesis | Active form | Confidence concern | Severity |
|---|---|---|---|
| `h_exec_len`, `h_e*_mult`, `h_m*_*` | bus-shape structural | Says "ZisK's PIL emits this exact bus shape on this opcode." Should derive from a PIL bus-emission spec; not yet extracted. If wrong → proof about phantom shape. | ⚠️ real |
| `h_rd_val` | bus rd-write encodes pure-spec result | **The actual circuit-correctness claim.** Should derive from `<op>_compositional` + bus-match + Phase 4.5 Bridges 1/2/3. We have the pieces; the gluing isn't shipped. If wrong → buggy circuit accepted as correct. | ⚠️⚠️ real, biggest |
| `h_input_r1`, `h_input_r2` (branches/JALR) | rs1/rs2 read via op bus | We model the *memory* bus's read predicates via `chip_bus_hyps_*`; the *operation* bus that branches/JALR use for rs reads has no analogous derivation. | ⚠️ real |
| `h_not_throws`, `h_success` | branch happy-path | Restricts theorem to non-faulting inputs. Soundness-safe but **completeness gap**: real binaries with faulting branches not covered. Analogous to the JALR-alignment example. | ⚠️ completeness |
| `h_input_misa`, `h_misa_c`, `h_cur_privilege`, `h_mseccfg` | privileged CSR reads | Caller must establish the harness's CSR setup. Restricts theorem to specific privilege configs. | ⚠️ completeness |
| `h_r1_ptr`, `h_r2_ptr`, `h_rd_ptr` | Sail register ↔ bus ptr correspondence | Says "the AIR's register-pointer column equals the Sail rs-operand." Should derive from an `rs_address` extension to transpile axioms; not yet done. | ⚠️ real |
| `h_input_imm`, `h_input_pc`, `h_input_rd` | input-from-bus matches | Become `rfl` in `_bus_self` companions (via `<Op>Input_of_bus` constructor). On the older non-`_bus_self` paths, they're scenario-binding harness conditions. | ✅ for `_bus_self`; ⚠️ otherwise |

### What we DON'T verify about the bus

The bus is critical infrastructure and partly axiomatized
indirectly:

- We define `OperationBusEntry`, `MemoryBusEntry`, `bus_effect`,
  `opBus_row_*` projections, and `matches_entry` predicates.
- We **prove** the 5 `bus_effect_matches_sail_<shape>` lemmas
  (memory-bus shape → Sail state transition) and the 5
  `chip_bus_hyps_<shape>` lemmas (memory-bus precondition → read
  equalities).
- We **don't prove** that the actual AIR's bus emissions match the
  `matches_entry` predicate. Caller asserts this on each
  invocation.
- We **don't prove** that the operation bus's permutation argument
  enforces multiset equality between Main's emissions and the
  secondary SM's consumptions. Same plookup-style issue as the
  Arith lookup axioms.
- We **don't prove** that `bus_effect`'s definition (multiplicity
  encoding, address-space encoding) matches PIL2 bus semantics.

Net: bus correctness = (proven shape lemmas) + (trusted PIL
bus-emission correspondence) + (trusted permutation-argument
soundness).

### What's out of scope for confidence purposes

- **GPU code paths.** ZisK's CUDA acceleration is performance
  infrastructure; the AIR/PIL2 constraint system being verified is
  identical CPU-vs-GPU. Bugs in GPU code produce traces that fail
  verification, not false positives.
- **AOT-to-x86_64 compilation.** ZisK compiles RV64 binaries AOT
  for fast execution at proving time; proofs are about the
  PIL2/AIR not the AOT path. Out of scope.
- **SNARK protocol soundness.** Cryptographic protocol analysis is
  a separate project; we assume verifier-accept ⇒ claim-true with
  full literal force.
- **Sail spec correctness.** Sail RISC-V is THE spec; trusted by
  definition.
- **LeanRV64D inherited axioms.** Floating-point primitives,
  reservation-set ops, `plat_term_write`, `get_16_random_bits` —
  imported from `LeanRV64D`. Trusted as part of accepting the Sail
  spec import.

### Priority list for retirement to maximize confidence in "ZisK ↔ RV64IM"

1. **Audit the 63 transpile axioms** against
   `zisk/core/src/riscv2zisk_context.rs`. Biggest unverified
   surface; outside Lean. ~weeks of careful reading.
2. **Compose `h_rd_val` derivation** for each opcode via the
   existing `<op>_compositional` + `matches_entry` + Phase 4.5
   Bridges + Phase 5 arith_table. Pieces shipped; gluing not.
   ~days per shape family.
3. **Extract the PIL bus-emission spec** to derive `h_exec_len`,
   `h_m*_*` from the AIR rather than parameterize on them.
4. **Factor the Arith lookup axioms** into table-data + plookup
   soundness; extract the table mechanically.
5. **Author `chip_op_bus_hyps_*`** (operation-bus analogue) to
   derive `h_input_r1`/`h_input_r2` for branches/JALR.
6. **Retire the 5 Sail-equivalence axioms** by unfolding. Pure
   tech debt; zero confidence gain but cleans up the surface.
7. **Cover the not-happy-path** for branches/jumps (faulting
   alignment cases) — closes completeness gaps.
8. **Formalize plookup / grand-product soundness** to retire the
   Arith lookup axioms' linkage piece. Substantial; standard math.

**Items 1, 2, 3, 5 are the biggest confidence wins.** Items 6–8
are cleanup or out-of-scope for "RV64IM correctness."

---

## Phase 6 — trust-base closure (in progress 2026-04-25)

Implementing the closure plan from
`/home/cody/.claude/plans/squishy-strolling-catmull.md`. Six tracks:
N (h_rd_val composition), O (PIL bus-emission extraction), P (lookup
table data), Q (op-bus effect), R (Sail-eq retirement), T
(not-happy-path coverage).

### Track P shipped (2026-04-25, commit `597c6f7`)

**P1.** Extracted 74-row arith_table data from
`zisk/state-machines/arith/src/arith_table_data.rs::ARITH_TABLE`
into `ZiskFv/Extraction/ArithTable.lean`. Each row decoded with the
12-bit FLAGS column unpacked per `arith_table.pil:209-211`
(m32, div, na, nb, np, nr, sext, div_by_zero, div_overflow,
main_mul, main_div, signed). Table content now verifiable by
inspection against the Rust source.

**P2.** Added 2 plookup-soundness axioms in
`ZiskFv/Airs/Arith/ArithTable.lean`:
- `arith_table_lookup_sound_mul` — every `Valid_ArithMul` row's
  `(op, m32, na, nb, np, nr)` tuple matches some row in
  `arith_table`.
- `arith_table_lookup_sound_div` — same for `Valid_ArithDiv`.

These are the irreducible protocol-soundness statements (standard
plookup / logUp from the ZK literature; Lean formalization of the
underlying protocol is out of scope per the SNARK out-of-scope
declaration).

**P3 follow-up.** The deprecated specialized witness axioms
(`arith_table_row_witness_unsigned`, `_unsigned_div`) remain in place;
their consumers still compile. Retirement requires rederiving
`arith_table_mulu_witnesses` etc as theorems via 74-row case
analysis on the extracted data — mechanical but ~100-200 lines per
opcode. Once shipped, the 2 deprecated axioms retire and the trust
base returns to 76.

**Trust-base impact (current):** 76 → 78 axioms (+2 plookup
soundness; deprecated axioms remain during transition). Once P3
completes: 78 → 76. Net delta is zero in axiom count but
*content* improves substantially: table-data correctness becomes
verifiable by inspection rather than bundled into the witness
axiom.

### Track R deferred

Track R (Sail-equivalence axiom retirement) was started but
revealed an unexpected complication: `execute_FENCE_pure_equiv_axiom`
implicitly assumes `cur_privilege ∈ {Machine, Supervisor, User}`
because Sail's `is_fiom_active` (`SysRegs.lean:1102`) calls
`internal_error` for VirtualUser/VirtualSupervisor privileges. The
axiom is currently overstated for adversarial states. Retirement
requires either:
- Adding a `cur_privilege` hypothesis to `equiv_FENCE_metaplan` (and
  the 4 `*W` divides analogously), OR
- Strengthening the axiom statement to assume the privilege bound.

Either path is a real semantic refinement, not just "lazy proof"
cleanup. Deferred pending a decision on the cleaner factor.

### Tracks N, O, Q, T pending

- **N (h_rd_val composition)** — blocked on Track O for the
  bus-byte-to-Main-column connection. Re-evaluable after O ships.
- **O (PIL bus-emission extraction)** — substantial Rust extractor
  extension + Lean derivation lemmas. Multi-session.
- **Q (op-bus effect)** — substantial new infrastructure. ~2000 lines.
- **T (not-happy-path)** — completeness extension. Needs Sail
  fault-path semantics modeled (likely overlaps with R's
  privilege-condition refinement).

### Tracks O, Q, T shipped via parallel-subagent POCs (2026-04-26)

Three additional Phase 6 closure tracks landed POCs via parallel
worktree-isolated subagents. All build green; zero new project-level
axioms across the three.

**Track O — PIL bus-emission extraction** (commit `d0ab622`).
- Extended `tools/pil-extract/` with `--bus-emissions` mode
  (~450 lines + 5 unit tests, 28/28 passing). Walks pilout's
  `gsum_debug_data` Hint payloads to extract bus-emission tuple
  shapes (bus id, multiplicity expression, per-slot named expressions).
- Auto-emitted `ZiskFv/Extraction/Buses.lean` (63 lines) with
  `bus_emission_Main_0 : BusEmissionSpec` for the Main AIR's
  operation-bus emission. Tuple: `op, a[0], (1-m32)*a[1], b[0],
  (1-m32)*b[1], c[0], c[1], flag` with multiplicity =
  `is_external_op`.
- Authored `ZiskFv/Airs/BusShape.lean` (158 lines) with two
  derivation theorems:
  - `bus_emission_main_slots_match_opBus_row_Main` — slot-by-slot
    equality between extracted spec and hand-written
    `opBus_row_Main`.
  - `bus_shape_for_ADD` — ADD-specific specialization under
    `op = OP_ADD ∧ is_external_op = 1 ∧ m32 = 0`.
- Verifies the extraction pipeline: `#print axioms` lists kernel
  only (propext + Classical.choice + Quot.sound). No new ZisK
  axioms.
- Follow-on: drop the hand-written `Airs/OperationBus.opBus_row_Main`
  and rebind downstream callers (Spec.Add etc.) to consume a
  generic `BusEmissionSpec`.

**Track Q — operation-bus effect model** (commit `4bd806c`).
- New `ZiskFv/Airs/OpBusEffect.lean` (85 lines): `op_bus_effect`
  for branch shape, encoding read_xreg equalities from
  operation-bus `a_lo/a_hi/b_lo/b_hi` lane reconstructions
  (analogous to `bus_effect`'s memory-bus model but for op-bus's
  value-carrying entries).
- New `ZiskFv/Airs/OpBusHypotheses.lean` (76 lines) with
  `chip_op_bus_hyps_branch` lemma proving (not axiomatizing) that
  `(op_bus_effect ...).1 → read_xreg rs1 state = ok ... ∧ ...`.
- Modified `ZiskFv/Equivalence/BranchEqual.lean` (+66 lines) with
  `equiv_BEQ_metaplan_op_bus` companion: drops
  `h_input_r1`/`h_input_r2` in favor of `h_op_bus` + match hyps.
- Zero new project-level axioms (only `Lean.ofReduceBool` /
  `Lean.trustCompiler` from decide-based tactics).
- Pattern fans out to BNE/BLT/BGE/BLTU/BGEU + JALR mechanically.

**Track T — not-happy-path coverage (BLT misaligned)** (commit
`9345092`).
- Added `equiv_BLT_metaplan_misaligned` (bit-1 misaligned target →
  `Memory_Exception (Virtaddr (PC + sext imm), E_Fetch_Addr_Align)`)
  and `equiv_BLT_metaplan_misaligned_bit0` (bit-0 misaligned →
  Sail `Assertion` from RVI-mode pre-check) in
  `Equivalence/BranchLessThan.lean` (+172 lines).
- Both proven from existing `equiv_BLT_sail` + `simp` on
  `PureSpec.execute_BLT_pure` with bit-level hypotheses.
- Zero new axioms.
- **Critical finding (documented in theorem docstring, lines
  237-322).** ZisK's PIL emits **no fault-flag column** anywhere
  on the bus (verified by grep over `zisk/pil/zisk.pil`).
  `RV64D/BusEffect.lean:115-121` hardcodes the post-fold result to
  `EStateM.Result.ok (Retire_Success ()) state'`. So the
  metaplan-shape equation `LHS = (bus_effect …).2` is **literally
  false** in misaligned cases — a constructor mismatch even when
  post-states agree. The companions therefore prove only the
  Sail-side reduction; closing the bus-side requires either
  extending `bus_effect` with a fault-flag, projecting to the
  `state` field only, or settling for Sail-only completeness.
- Generalizes mechanically to BEQ/BNE/BLTU/BGE/BGEU/JAL/JALR — all
  blocked on the same bus-effect gap.

### Track R — POC failed; not yet retired

Agent attempted retirement with privilege hypothesis added but
proof tactics didn't close (syntax error in `set_option ... in
lemma` form + unsolved `simp` goals on the 11-arm barrier match
unfolding). Discovery from earlier session confirmed: retirement
requires a real semantic refinement (`cur_privilege ∈ {Machine,
Supervisor, User}` hypothesis), but executing the proof needs
substantial Sail-side machinery (per-arm barrier reductions, fiom
CSR read state-preservation, `effective_fence_set` simplification).
Multi-day effort, not 2-3 hours. Worktree cleaned up.

### Phase 6 trajectory (post-2026-04-26)

| Track | POC | Round-2 fan-out | Trust impact |
|---|---|---|---|
| **N** (h_rd_val) | Pending — depends on O composition | — | Unblocked by O ship |
| **O** (PIL bus-emission) | ✅ POC shipped | Pending: multi-AIR + 63-opcode fan-out | 0 new axioms |
| **P** (lookup tables) | ✅ POC shipped | ✅ `ff7aef8` — 4 unsigned witness theorems (MULUH/MUL_W/DIVU/REMU) + 2 deprecated axioms retired | -2 axioms net |
| **Q** (op_bus_effect) | ✅ POC shipped | ✅ `569cdad` — op_bus companions for BNE/BLT/BGE/BLTU/BGEU/JALR | 0 new axioms |
| **R** (Sail-eq retirement) | ✅ `114094d` — FENCE retired (2nd attempt with explicit commit) | Pending: 4 *W divide axioms | -1 axiom (FENCE) |
| **T** (not-happy-path) | ✅ Sail-side POC shipped | ✅ `15d03a8` — misaligned companions for BEQ/BNE/BGE/BGEU/BLTU/JAL/JALR (13 theorems) | 0 new axioms; bus-effect fault-flag gap remains |

**Round-2 (2026-04-26 evening) summary.** Trust base 79 → 77 axioms. All
fan-outs landed on main and build green (8138 jobs).

**Track R FENCE retirement details.** First agent attempt built green
but did not commit before its worktree was cleaned up — recipe was
captured from the report and a second agent reproduced + committed.
Final proof shape: under `cur_privilege = Machine` hypothesis,
`is_fiom_active_machine` reduces to `pure false`, then
`execute_FENCE_machine_pure` closes the 11-arm barrier match by
`generalize` + `interval_cases np <;> interval_cases nq <;> rfl` over
the 16 (BitVec 2 × BitVec 2) pairs (every arm reduces to `pure ()`
after `sail_barrier _` unfolds). New `h_input_priv` parameter
threaded through `equiv_FENCE_sail`, `equiv_FENCE_metaplan`,
`equiv_FENCE_metaplan_from_bus`, `equiv_FENCE_metaplan_bus_self`.

**Next-step priorities:**
1. Track P signed witness cases (MULSUH/MUL/MULH/DIV/REM/MULW/REMW signed) — bit-extraction work.
2. Track O multi-AIR fan-out (Arith/Binary/Memory bus emissions + 63-opcode `bus_shape_for_<OP>` lemmas).
3. Track R remaining 4 axioms (DIVW/DIVUW/REMW/REMUW). FENCE pattern transfers but each needs ~200 lines of bit-extract + sign-extension reasoning.
4. Track N `h_rd_val` composition — depends on Track O bus-shape derivation being available across opcodes. **Track N6 deferral note (2026-04-26):** Jump/UTYPE shape attempted; needs (a) Track O register-write-lanes-match bridge, (b) FGL→BitVec immediate bridge for transpile_LUI/AUIPC, (c) FGL→BitVec PC bridge for transpile_JAL/JALR. See "Track N6 deferral analysis" section below.

### Track T scope clarification (2026-04-26)

The original Phase 6 plan suggested Track T would also need a "bus-side
fault-flag column" extension to mirror the Sail-side misaligned-target
companions. Investigation closes this as architecturally absent rather
than unfinished work:

- ZisK's PIL (`zisk/state-machines/main/pil/main.pil`) emits no
  fault-flag column. `OperationBusEntry` has no fault field, and
  `bus_effect.2` returns `Retire_Success` unconditionally.
- This is by design: ZisK's circuit constrains *valid execution
  traces only*. A misaligned branch would never appear in a witness
  the prover can satisfy — the PC-alignment constraint at extraction
  blocks it. There is no bus shape to extend because the circuit
  cannot encode misaligned execution at all.
- The metaplan theorems remain *vacuously sound* on misaligned inputs:
  the bus-match precondition (`bus_effect _ _ state).1`) cannot hold
  for a witness with misaligned PCs, so the implication is trivially
  satisfied. The Sail-side companions (`equiv_<OP>_metaplan_misaligned`)
  document what Sail would compute *if such a trace existed*.
- The "exclusion" guarantee — "no satisfying witness has a misaligned
  PC" — properly belongs to Track O (extracted PIL constraint set
  includes the alignment check), not Track T.

**Track T closure:** Sail-side completeness extension shipped (POC +
fan-out, 8 opcodes total: BLT/BEQ/BNE/BGE/BGEU/BLTU/JAL/JALR). No
bus-side work remains within Track T's scope. Misaligned-execution
exclusion as a circuit-level guarantee is inherited from Track O's
PIL constraint extraction.

### Track N6 deferral analysis: Jump/UTYPE `h_rd_val` (2026-04-26)

**Status: deferred** — Track N (`h_rd_val` retirement) was attempted on
the Jump/UTYPE shape (JAL/JALR/LUI/AUIPC) under the hypothesis that the
shape is "simplest" because there's no Arith / BinaryAdd intermediary.
Investigation found the derivation requires more new infrastructure
than initially scoped. Concrete blockers:

1. **No bus-emission lane-match exposed for the rd-write entry.** The
   `chip_bus_hyps_jump_rrw` lemma (`Airs/BusHypotheses.lean:167`)
   produces only the PC-read fact from the bus precondition; it does
   not expose the rd-write entry's bytes as matching the Main row's
   `store_value[0]` / `store_value[1]` lanes. Phase 4 / Track O is the
   right home for that bridge — it requires a `register_write_lanes_match`
   form analogous to the existing load-side `memory_load_lanes_match`,
   but tied to the *store_value expression* (`store_pc * (pc + jmp_offset2 - c_0) + c_0`)
   rather than to a column directly. No such bridge exists today.

2. **No FGL→BitVec immediate bridge for transpile_LUI.** The axiom
   `transpile_LUI` pins `m.b_0 = imm_lo` and `m.b_1 = imm_hi` where
   `imm_lo`/`imm_hi` are caller-supplied **Goldilocks representatives**
   of the LUI immediate. Closing the rd-byte equation
   `U64.toBV [bytes] = BitVec.signExtend 64 (imm ++ 0#12)`
   needs an architectural bridge `(imm_lo + imm_hi * 2^32 : FGL).val
   = (BitVec.signExtend 64 (imm ++ 0#12)).toNat`, which is not
   currently in the trust base. Same for AUIPC's `jmp_offset2`
   carrying the immediate.

3. **No FGL→BitVec PC bridge for transpile_JAL/JALR.** The Sail-side
   `jal_input.PC : BitVec 64` connects to the Main row `m.pc r_main : FGL`
   only via the bus-derived `BitVec.ofNat 64 (exec_row[0]!.pc).val`
   path. For h_rd_val we need the full `m.pc r_main + 4 (FGL) → PC + 4
   (BitVec)` bridge, which crosses the same lane-recombine + carry
   reasoning as `lane_lo_lane_hi_recombine_eq_toNat` —
   tractable but a non-trivial new lemma per opcode.

**Path forward.** Track N6 should land *after* Track O Phase 3
publishes per-opcode bus-emission witness theorems exposing the
`store_value` ↔ `e_rd` bytes correspondence. With that bridge in
hand, the four wrappers reduce to: spec `*_store_value*` theorem +
bus-emission lane match + Bridge 3 (`u64_toBV_eq_ofNat_fgl_val`) +
the immediate/PC bridge axioms (added to the trust base alongside
`transpile_*`). Estimated 4 × ~80 lines (one wrapper per opcode), but
**only** after the prerequisite infrastructure is in place.

No new code shipped under Track N6 in this round; trust-base axiom
count unchanged. The four `h_rd_val` parameters in
`equiv_{JAL,JALR,LUI,AUIPC}_metaplan*` remain as Phase-4-derivable
obligations.

### Track N7 deferral analysis: MUL/DIV/REM family `h_rd_val` (2026-04-26)

**Status: deferred** — Track N (`h_rd_val` retirement) was attempted on
the MUL/DIV/REM family (15 opcodes: MUL, MULH, MULHU, MULHSU, MULW,
MULU, MULUH, DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW) under
the hypothesis that the just-shipped Track P signed witness theorems
(`arith_table_<op>_witnesses_from_data`) plus Phase 4.5 Bridges 1/2/3
plus the `_table_closed` wrappers would compose into a complete
`h_rd_val` derivation. Investigation found the composition is genuinely
blocked on the same memory-bus emission infrastructure that Track N6
flagged for Jump/UTYPE, plus an additional Goldilocks-to-`BitVec 64`
multiplicative-reduction step that Bridge 3 alone does not provide.
Concrete blockers:

1. **Memory-bus emission lane-match for the rd-write entry is a
   compositional hypothesis, not a derived theorem.**
   `Airs/MemoryBus.lean::register_write_lanes_match m row e` is a
   `Prop` definition that asserts `m.c_0 row = memory_entry_lo e ∧
   m.c_1 row = memory_entry_hi e`. The compositional ADD/MUL/DIV
   metaplan companions today *don't even take* this as a hypothesis —
   they take `h_rd_val` directly, treating the entire lane-to-byte
   bridge as a parameter. Retiring `h_rd_val` requires either (a)
   adding `register_write_lanes_match` to every metaplan companion's
   signature (just substituting one black-box for another), or (b)
   deriving it from a PIL-level memory-bus emission spec — which is
   Track O Phase 4 scope.

2. **No FGL→BitVec multiplicative reduction lemma for the MUL family.**
   The Bridge 2 closure `Spec/MulField.lean::main_mul_unsigned_field_correct`
   produces an *FGL* identity:
   ```
   main_a_packed * main_b_packed
     = main_c_packed + d_chunks_packed * (65536^4)    (over FGL)
   ```
   What `h_rd_val` requires is a `BitVec 64` identity:
   ```
   BitVec.ofNat 64 (main_c_packed m r_main).val
     = execute_MUL_pure r1_val r2_val .MUL
   ```
   The lift requires (i) a range bound on `main_a_packed.val`,
   `main_b_packed.val`, `main_c_packed.val`, `d_chunks_packed.val`
   that pins each below `2^64`, plus a no-wrap bound
   `main_c_packed.val + d_chunks_packed.val * 2^64 < GL_prime` so
   that `(c + d * 2^64) % p` doesn't reduce; (ii) a Nat-level
   identity `main_c.val % 2^64 = (main_a.val * main_b.val) % 2^64`
   derived from (i); (iii) a connection to
   `execute_MUL_pure`'s `to_bits_truncate (Sail.BitVec.toNatInt op1 *
   toNatInt op2)` shape via `Sail.BitVec.toNatInt = .toNat` for
   non-negative BVs. None of these lemmas exist in
   `Fundamentals/PackedBitVec.lean` today; Bridge 3 ships only the
   *byte-pack* lift (`u64_toBV_eq_ofNat_fgl_val`), not the
   *multiplication* lift.

3. **Signed cases (MULH, MULHSU, DIV, REM) require additional
   `BitVec.toInt` reasoning and `Int.tdiv` overflow handling for
   `INT_MIN / -1`.** Even with blockers (1) and (2) resolved for
   unsigned MUL, the signed variants need a separate path: Bridge 2
   produces a *signed* field identity (`Spec/MulField` lemma:
   `(1 - 2*np) * (c_packed + d_packed * B^4) = ...`) that lifts to a
   `BitVec.toInt`-mod-2^64 equation, requiring sign-bit case analysis
   on `np`. DIV's special cases (`x / 0 = -1`, `INT_MIN / -1 = INT_MIN`)
   need explicit witness mapping at the wrapper layer.

4. **Operand-side `r1_val = U64.toBV [e0 bytes]` is also not currently
   derivable** without the same memory-bus lane-match hypothesis on
   `e0` and `e1` (analogous to (1) for the read side). The `chip_bus_hyps_alu_rrw`
   lemma exposes `read_xreg`-equality, not byte-level lane matching.

**Path forward.** Track N7 should land *after*:

- Track O Phase 4 publishes per-opcode bus-emission lane-match
  theorems (rd-write, rs1-read, rs2-read) deriving
  `register_write_lanes_match`-shaped facts from the PIL constraint
  set + bus permutation soundness;
- A new `Fundamentals/FieldBVMul.lean` or extension to
  `Fundamentals/PackedBitVec.lean` ships the FGL→BitVec
  multiplicative reduction under chunk-range bounds;
- The arith_table chunk-range constraints (Phase 4 deferred
  `range_ab` / `range_cd` / `inv_sum_all_bs` lookups) are exposed
  as theorems pinning `c_chunks_packed.val < 2^64` and similar.

With those prerequisites, the wrappers reduce to per-opcode
`Spec/<Op>RdVal.lean` files of ~50 lines each (unsigned) /
~120 lines each (signed) that compose:
- Bridges 1+2 (existing) → field-level packed identity;
- Bus-emission lane match (new in Track O) → Main lanes = e2 bytes;
- Bridge 3 byte-pack (existing) → `U64.toBV [bytes]`;
- Field-BV multiplicative reduction (new in N7) → `BitVec.ofNat 64`
  of the field product equals the BV product low/high half.

No new code shipped under Track N7 in this round; trust-base axiom
count unchanged. The 60 `h_rd_val` parameters in
`equiv_{MUL,MULH,MULHU,MULHSU,MULW,MULU,MULUH,DIV,DIVU,DIVW,DIVUW,REM,REMU,REMW,REMUW}_metaplan*`
(15 files × 4 companions) remain as Phase-4/Track-O-derivable
obligations. The Track P witness theorems shipped in commit `ab9c0f9`
remain ready to consume as soon as the bus-emission and field-BV-mul
prerequisites land.

## Lookup-table bus contracts (finishing2 S0 — 2026-04-27)

The Binary AIR (pilout idx 10) and BinaryExtension AIR (pilout idx 12)
encode their byte-level semantics as **lookup arguments against virtual
fixed tables** (`bus_id = 125 BinaryTable`, `bus_id = 124 BinaryExtensionTable`),
not as F-typed polynomial constraints. Following the openvm-fv pattern
in `Fundamentals/Interaction.lean::BitwiseBusEntry`, the per-row
semantic relation `wf_properties` is **trusted at the bus-entry
definition site**. openvm-fv never proves its bitwise / range-checker
/ program-bus tables; the relation is asserted as part of the
`BusEntry` instance. The two axioms below adopt the same convention.

### Entry BT-B: `ZiskFv.Airs.BinaryTable.bin_table_consumer_wf`

- **File:** `ZiskFv/Airs/BinaryTable.lean`.
- **Statement:** every entry the Binary AIR consumes against
  `bus_id = 125` (multiplicity = 1) satisfies `wf_properties`. The
  `wf_properties` predicate is the conjunction of per-op clauses
  encoding the byte-level switch from
  `zisk/state-machines/binary/pil/binary_table.pil`'s `for`
  loop: AND/OR/XOR bitwise ops, LT/LTU/EQ/GT/LE/LEU comparison
  byte-chain rules, ADD/SUB carry/borrow byte semantics, and
  SEXT_00/FF byte sign-extends.
- **Consumers:** all 12 K1-B BitVec lifts in
  `Airs/Binary/BinaryPackedCorrect.lean` (binary AND/OR/XOR via S1;
  LTU/LT/SUB/ADDW chain lifts via E commit `3e437f5`). Each lift
  pulls its op's clause out of `wf_properties` via the byte-relation
  extractors `byte_relation_{AND,OR,XOR,LTU,LT,SUB,ADD,SEXT_00,SEXT_FF}`.
- **Provenance:** PIL2 plookup soundness on `bus_id = 125` plus the
  table-content correctness of `binary_table.pil`'s deterministic
  generator switch. Trust class: bus-protocol soundness +
  table-content correctness, both project-trusted (`CLAUDE.md` "Trust
  scoping").
- **Why axiomatic:** the openvm-fv pattern. Closing it would split
  into (a) plookup soundness as a Lean theorem and (b) a
  metaprogram-derived `def` enumerating `binary_table.pil`'s rows.
  The metaplan's stated goal is per-opcode and is met without that
  closure.
- **Mirrors:** the operation-bus pattern at `bus_id = 5000`
  (`OperationBus.matches_entry`). Differs in carrying multiple ops
  in one entry rather than one op per bus.

### Entry BT-X: `ZiskFv.Airs.BinaryExtensionTable.bin_ext_table_consumer_wf`

- **File:** `ZiskFv/Airs/BinaryExtensionTable.lean`.
- **Statement:** every entry the BinaryExtension AIR consumes against
  `bus_id = 124` satisfies `wf_properties`. The predicate's per-op
  clauses encode the byte-level shift semantics from
  `zisk/state-machines/binary/pil/binary_extension_table.pil`'s
  for-loop switch: SLL/SRL/SRA 64-bit shifts and SLL_W/SRL_W/SRA_W
  32-bit-word shifts (with sign-extension to 64).
- **Consumers:** all 6 K1-C BitVec lifts in
  `Airs/Binary/BinaryExtensionPackedCorrect.lean`
  (`binary_extension_{sll,srl,sra,sllw,srlw,sraw}_chunks_eq_bv_*`).
- **Provenance:** PIL2 plookup soundness on `bus_id = 124` plus the
  table-content correctness of `binary_extension_table.pil`'s
  generator switch. Trust class: same as BT-B.
- **Why axiomatic:** same reason as BT-B (openvm-fv pattern; closure
  out of per-opcode scope).
- **Architectural note:** unlike `Binary` (where the AIR exposes 7
  F-typed booleanity / linearity flag constraints), `BinaryExtension`
  exposes **zero** F-typed constraints — every constraint in the AIR
  is a permutation/lookup. The semantic content of every shift opcode
  flows entirely through this axiom.

## Memory-bus permutation soundness — register writes (finishing3 S4 — 2026-04-27)

### Entry MB-W: `ZiskFv.Airs.MemoryBus.LaneMatch.memory_bus_register_write_perm_sound`

- **File:** `ZiskFv/Airs/MemoryBus/LaneMatch.lean`.
- **Statement:** for every Main row `row` with `assumes_store_reg = 1`
  (column 37) and `store_pc = 0`, every consuming `MemoryBusEntry e`
  paired through the memory bus's permutation argument satisfies
  `memory_entry_lo e = m.c_0 row ∧ memory_entry_hi e = m.c_1 row`,
  given a Mem AIR consumer row at the matching `(addr=store_offset,
  wr=0, addr_changes=0)` whose value lanes byte-decompose to e's
  packed lo/hi halves.
- **Consumers:** `register_write_lanes_match_of_bus_emission` (the
  K2 writes-side closure at the LaneMatch layer). Ultimately
  consumed downstream by load/store metaplan theorems via
  `register_write_lanes_match`.
- **Provenance:** `zisk/state-machines/main/pil/main.pil:316-328`
  (the `reg_pre_store` + `mem_op` for store-reg) +
  `zisk/state-machines/mem/pil/mem.pil:436` (the Mem AIR's
  `permutation_proves` half on `bus_id = MEMORY_ID = 10`).
- **Trust class:** memory-bus permutation soundness. This is the
  writes-side analogue of the operation-bus axiom
  `OperationBus.matches_entry`, in the same trust class as the
  project's "proving-system correctness" scope (`CLAUDE.md` trust
  ledger). The PLONK / logUp permutation argument over `bus_id = 10`
  delivers multiset equality of emit/consume sites; this axiom
  bundles the soundness conclusion under the writing-emission gating
  + consuming-Mem-row hypotheses.
- **Why it cannot currently be derived in tree:**
  1. The writing-side bus emission for stores is not extracted as
     a separate `bus_emission_Main_mem_*` (the F-typed `proves`
     halves shipped in `Extraction/MemoryBuses.lean` are the rs1 /
     rs2 / store-reg-prev *reads*, not the stores). A future
     extractor extension could emit the writing-side `assumes` half
     on bus_id=10.
  2. The cross-row "value persists across same-addr no-write reads"
     chain in the Mem AIR (PIL constraints 27/28 — `read_same_addr
     * (value - prev_value) = 0`) is in the F/ExtF stub bucket of
     `Airs/Mem.lean`: `read_same_addr` is F-typed but `previous_value`
     references either an airvalue (stage-2) on the first row or
     `'value` (rotation = -1) on subsequent rows, mixing F with
     ExtF challenge randomness on the bus-protocol path.
- **Closure path if promoted to theorem:** extend the bus-emission
  extractor (`tools/pil-extract --bus-emissions`) to emit the
  writing-side `permutation_assumes` halves, write the Mem AIR
  cross-row continuity bridge against the airvalue-typed previous
  row state, and combine to derive the soundness statement from
  in-tree pieces. Estimated several hundred lines split across the
  Rust extractor, `Extraction/MemoryBuses.lean`, and a new
  `Airs/MemoryBus/MemBridge.lean` (which agent K is concurrently
  authoring as part of finishing3 S3). Once that bridge ships, this
  axiom retires in favor of a derivation from the Mem AIR's
  `Valid_Mem` consistency + PLONK-protocol primitives.
- **Audit scope:** any change to ZisK's memory-bus PIL macros
  (`mem_op`, `reg_pre_store`, `permutation_proves` on `bus_id =
  MEMORY_ID`) requires re-signing this axiom. The selector column
  (37, `assumes_store_reg`) and the store-offset column (24,
  `store_offset`) are pinned to PIL columns; if the PIL layout
  changes those, this axiom's column references must update too.

### Entry MB-W-PC: `ZiskFv.Airs.MemoryBus.LaneMatch.memory_bus_register_write_perm_sound_store_pc` (finishing5 S4 — 2026-04-27)

- **File:** `ZiskFv/Airs/MemoryBus/LaneMatch.lean`.
- **Statement:** companion to MB-W for the `store_pc = 1` case (JAL,
  JALR, AUIPC). When Main row `row` has `assumes_store_reg = 1`
  (column 37) and `store_pc = 1`, the PIL pins `store_value =
  (pc + jmp_offset2, 0)` (`main.pil:311-312` evaluated at
  `store_pc = 1`). Every consuming `MemoryBusEntry e` paired through
  the memory-bus permutation argument satisfies
  `memory_entry_lo e = m.pc row + m.jmp_offset2 row` and
  `memory_entry_hi e = 0`, given a Mem AIR consumer row at the
  matching `(addr=store_offset, wr=0, addr_changes=0)` whose value
  lanes byte-decompose to e's packed lo/hi halves.
- **Consumers:** `store_pc_lanes_match_lo_of_bus_emission` and
  `store_pc_lanes_match_hi_of_bus_emission` (the case-split soundness
  theorems for `store_pc_lanes_match_lo` / `_hi`). Ultimately
  consumed by JAL / JALR / AUIPC `h_rd_val` discharges in
  `Equivalence/RdValDerivation/JumpUType.lean`.
- **Provenance:** `zisk/state-machines/main/pil/main.pil:311-312`
  (the `store_value[0]` and `store_value[1]` formulas) +
  `zisk/state-machines/main/pil/main.pil:316-328` (the
  `reg_pre_store` + `mem_op` for store-reg) +
  `zisk/state-machines/mem/pil/mem.pil:436` (the Mem AIR's
  `permutation_proves` half on `bus_id = MEMORY_ID = 10`).
- **Trust class:** identical to MB-W — memory-bus permutation
  soundness on `bus_id = 10` for register writes. Differs from MB-W
  only in the conclusion's PIL-formula evaluation (at `store_pc = 1`
  vs `store_pc = 0`); the underlying multi-row Mem AIR chain is the
  same.
- **Why it cannot currently be derived in tree:** identical reasoning
  as MB-W. The writing-side bus emission for stores is not extracted
  as a separate `bus_emission_Main_mem_*`; the cross-row "value
  persists across same-addr no-write reads" chain is in the F/ExtF
  stub bucket of `Airs/Mem.lean`.
- **Closure path if promoted to theorem:** identical to MB-W.
  Extending the bus-emission extractor to surface the writing-side
  `permutation_assumes` half plus the Mem AIR cross-row continuity
  bridge would let both MB-W and MB-W-PC retire together.
- **Audit scope:** any change to the PIL `store_value` formulas at
  `main.pil:311-312` or to the bus-protocol macros named in MB-W's
  audit scope requires re-signing this axiom. The PIL formula
  `store_pc * (pc + jmp_offset2 - c[0]) + c[0]` and
  `(1 - store_pc) * c[1]` are pinned to specific Main columns
  (7 = pc, 27 = jmp_offset2, 4 = c_0, 5 = c_1, 22 = store_pc); if
  the PIL layout changes those, this axiom's column references in
  `Valid_Main`'s `_def` lemmas must update too.

## Memory-model bridge — load / store paths (finishing3 S3 — 2026-04-27)

The S3 closure in `ZiskFv/Spec/MemModel.lean` and
`ZiskFv/Airs/MemoryBus/MemBridge.lean` introduces **four** new axioms
to package the memory-bus / Sail-state correspondence. Together they
replace the per-opcode M-family `h_bus_execute_matches_sail` parameter
on load / store metaplan theorems with a single chain whose only trust
inputs are these axioms (plus the always-trusted bus-effect /
chip_bus_hyps machinery already in tree).

### Entry MB-L: `ZiskFv.Airs.MemoryBus.MemBridge.lookup_consumer_matches_provider_load`

- **File:** `ZiskFv/Airs/MemoryBus/MemBridge.lean`.
- **Statement:** for every Main row `r_main` whose memory-bus emission
  is a load (`b_0 = lo(e), b_1 = hi(e), as = 2, multiplicity = -1`),
  there exists a Mem AIR row `r_mem` whose
  `(addr, step, value_0, value_1, wr)` projection matches the entry
  `(ptr, timestamp, lo, hi, 0)`.
- **Consumers:** `memory_load_lanes_match_of_mem_row` and
  `Spec.MemModel.mem_load_correct`.
- **Provenance:** `zisk/state-machines/mem/pil/mem.pil:526` —
  the memory bus's `permutation_assumes` half pulls from the Mem AIR's
  per-row state. Trust class: PLONK / logUp / permutation-argument
  soundness, project-trusted (`CLAUDE.md` "Trust scoping").
- **Why axiomatic:** PLONK-style multiset equality for `bus_id = 10`
  is project-trusted; this axiom bundles the soundness conclusion
  in a structurally usable form.
- **Mirrors:** the operation-bus pattern at `bus_id = 5000`
  (`OperationBus.matches_entry`).

### Entry MB-S: `ZiskFv.Airs.MemoryBus.MemBridge.lookup_consumer_matches_provider_store`

- **File:** `ZiskFv/Airs/MemoryBus/MemBridge.lean`.
- **Statement:** dual of MB-L for stores: for every Main row whose
  emission is a store (`c_0 = lo(e), c_1 = hi(e), as = 2,
  multiplicity = 1`), there exists a Mem AIR row matching the entry
  with `wr = 1`.
- **Consumers:** `memory_store_lanes_match_of_mem_row` and
  `Spec.MemModel.mem_store_correct`.
- **Provenance:** same memory-bus permutation soundness as MB-L,
  store-side; `zisk/state-machines/mem/pil/mem.pil:527`.
- **Note vs MB-W:** MB-W (declared by agent L in `LaneMatch.lean`) is
  scoped to the *register-write* path on the memory bus — i.e. the
  `as = 3` register-side write that is consistency-checked via the
  Mem AIR's `prev_value` chain. MB-S is the *memory-write* path
  (`as = 2`) used by SD/SW/SH/SB. The two address-space sides differ
  in the value-carrying convention (register: 32-bit lanes; memory:
  byte decomposition); we keep them as separate axioms because the
  PIL macros they correspond to are also separate.

### Entry MS-L: `ZiskFv.Spec.MemModel.row_models_sail_state_load`

- **File:** `ZiskFv/Spec/MemModel.lean`.
- **Statement:** given a Mem AIR row `r_mem` matching a load-side bus
  entry `e` with `wr = 0` and `sel = 1`, the Sail state's memory at
  `e.ptr.toNat + i` agrees with `e.x_i` for each of the eight byte
  lanes.
- **Consumers:** `Spec.MemModel.mem_load_correct` (the M*-axiom
  replacement at the metaplan layer).
- **Provenance:** the Sail RV64IM memory model (`LeanRV64D`'s
  `state.mem`) and the ZisK Mem AIR's read protocol
  (`mem.pil:524-527`). Trust class: implementation-models-spec
  faithfulness — the Mem state-machine's view of memory must agree
  with Sail's at this point in execution.
- **Why axiomatic:** this is the irreducible correspondence between
  ZisK's memory state-machine model (a multiset of address-step-value
  rows enforced by permutation soundness) and Sail's memory model
  (a `Std.HashMap Nat (BitVec 8)`). Closing it would require a
  whole-trace argument that ZisK's Mem AIR is a correct refinement
  of Sail's `state.mem`. Out of per-opcode scope.

### Entry MS-S: `ZiskFv.Spec.MemModel.row_models_sail_state_store`

- **File:** `ZiskFv/Spec/MemModel.lean`.
- **Statement:** given a Mem AIR row in write mode (`wr = 1, sel = 1`)
  matching a store bus entry, the post-store Sail state's `state.mem`
  agrees byte-by-byte with the entry's lanes (in the same eight
  `mem.insert` chain shape `bus_effect`'s store branch produces).
- **Consumers:** `Spec.MemModel.mem_store_correct`.
- **Provenance:** dual to MS-L, store-side. Same trust class.
- **Why axiomatic:** same reason as MS-L: irreducible
  implementation-models-spec correspondence between ZisK's Mem AIR
  and Sail's memory model on the write side.

## Phase 6 finishing5 S1 — store_pc=1 PC bridges (2026-04-27)

The three axioms below pin the **runtime PC value** at the Main-AIR
`pc` column for the three `store_pc = 1` opcodes (JAL, JALR, AUIPC).
They extend the trusted transpile contract beyond operand / selector
witnesses to the program-counter witness column itself, which is
needed because the rd-write formula `store_value[0] = store_pc * (pc +
jmp_offset2 - c[0]) + c[0]` (`main.pil:311`) collapses to `pc +
jmp_offset2` for these opcodes — and downstream Spec / Equivalence
proofs need to bridge the FGL-side `m.pc r_main` to the Sail-side
`PC : BitVec 64`.

These axioms are consumed by finishing5 S3 (Spec hi-half lemmas) and
S5 (JumpUType `h_rd_val` Tier-1 upgrade) — together with finishing5
S2's wide-PC no-wrap toolkit they retire the
`h_pc_fgl_lo_nat` / `h_pci_lo_val` OUTPUT-EQ residuals on the existing
`RdValDerivation/JumpUType.lean` discharge lemmas.

### Entry TP-JAL: `ZiskFv.Trusted.transpile_PC_for_JAL`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Statement:** given a `Valid_Main` instance, a row index `r_main`,
  a Sail-side `PC : BitVec 64`, and the JAL mode-witness pair
  (`is_external_op = 0`, `op = OP_FLAG`), concludes
  `(m.pc r_main).val = PC.toNat`.
- **Consumers:** `transpile_PC_consumer_JAL` (V13 witness in
  `Fundamentals/TranspileConsumers.lean`); finishing5 S3 / S5 will
  plumb this through `Spec.Jal.jal_store_value_hi_bv` and
  `RdValDerivation.JumpUType.h_rd_val_jut_jal` to retire the
  `h_pc_fgl_lo_nat` parameter.
- **Provenance:** the Sail-PC ↔ ZisK Main-pc-column contract at
  `zisk/core/src/riscv2zisk_context.rs:201,1098` (`fn jal`):
  the Rust transpiler emits a Main row whose `pc` column carries the
  ROM-assigned representative of the Sail-state PC at this
  instruction. The full chain that ties `m.pc r_main` to `state.pc`
  combines (a) ZisK's ROM (which assigns `pc` per row), (b) the
  cross-row continuation handshake from `main.pil:410` (constraint
  20 — `(1 - SEGMENT_L1) * (pc - expected_current_pc) === 0`), and
  (c) the segment boundary `airval segment_initial_pc` /
  `segment_next_pc` chain.
- **Trust class.** Sail-PC ↔ ZisK Main-pc-column contract — the
  transpiler-emits-row faithfulness for the PC witness column.
  Same class as the existing `transpile_<OP>` operand axioms which
  pin `a_0 = lane_lo (state.xreg rs1)` etc. for source registers.
- **Why axiomatic:** the existing extractor does not surface ZisK's
  ROM nor the cross-segment handshake column rotations needed to
  derive this equality from in-tree pieces. PIL constraint 20 ties
  `pc` to the previous row's `expected_current_pc`, but the
  rotation-by-(-1) machinery + segment-boundary `airval` chain are
  in the F/ExtF stub bucket of the extractor today.
- **Closure path if promoted to theorem:** model ZisK's ROM as a
  per-row `pc → expected_pc` map; bridge it through the cross-segment
  continuation handshake to derive `(m.pc r_main).val =
  PC.toNat` from a Sail-side execution trace. Estimated several
  hundred lines split across a new `Fundamentals/Rom.lean` and
  extensions to `Airs/Main.lean` covering the segment-handshake
  airvalues. Trust reduction is welcome but out of finishing5 scope.
- **Audit scope:** changes to `riscv2zisk_context.rs::fn jal`, to
  ZisK's ROM-emission code, or to `main.pil:410`'s PC-handshake
  constraint require re-signing this axiom.

### Entry TP-JALR: `ZiskFv.Trusted.transpile_PC_for_JALR`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Statement:** given a `Valid_Main` instance, row index, Sail-side
  `PC : BitVec 64`, and the JALR mode-witness pair
  (`is_external_op = 0`, `op = OP_COPYB`), concludes
  `(m.pc r_main).val = PC.toNat`.
- **Consumers:** `transpile_PC_consumer_JALR`; finishing5 S5 will
  plumb this through the JumpUType JALR discharge.
- **Provenance:** Sail-PC ↔ ZisK Main-pc-column contract at
  `zisk/core/src/riscv2zisk_context.rs:200,1025` (`fn jalr`).
  Recall that JALR is modeled by ZisK's archetype validation as a
  simplified internal-copyb shape (with `set_pc = 1`); the same PC
  bridge applies — it asserts where the row sits in the program
  counter sequence, not how the next-PC is computed.
- **Trust class:** same as TP-JAL.
- **Why axiomatic:** same as TP-JAL.
- **Closure path:** same as TP-JAL.
- **Audit scope:** changes to `riscv2zisk_context.rs::fn jalr` or to
  the PC-handshake PIL require re-signing.

### Entry TP-AUIPC: `ZiskFv.Trusted.transpile_PC_for_AUIPC`

- **File:** `ZiskFv/Fundamentals/Transpiler.lean`.
- **Statement:** given a `Valid_Main` instance, row index, Sail-side
  `PC : BitVec 64`, and the AUIPC mode-witness pair
  (`is_external_op = 0`, `op = OP_FLAG`), concludes
  `(m.pc r_main).val = PC.toNat`.
- **Consumers:** `transpile_PC_consumer_AUIPC`; finishing5 S3 / S5
  will plumb this through `Spec.AddUpperImmediatePC` and the
  JumpUType AUIPC discharge to retire the `h_pci_lo_val` parameter.
- **Provenance:** Sail-PC ↔ ZisK Main-pc-column contract at
  `zisk/core/src/riscv2zisk_context.rs:907` (`fn auipc`).
- **Trust class:** same as TP-JAL.
- **Why axiomatic:** same as TP-JAL.
- **Closure path:** same as TP-JAL — closing TP-JAL closes all three.
- **Audit scope:** changes to `riscv2zisk_context.rs::fn auipc` or to
  the PC-handshake PIL require re-signing.
- **Selector overlap with TP-JAL:** AUIPC and JAL share the
  `(is_external_op = 0, op = OP_FLAG)` selector pair on the Main
  row; the discriminator at the proof level is the surrounding
  `transpile_<OP>` axiom invocation, which pins `jmp_offset1` /
  `jmp_offset2` differently for the two opcodes. Both PC bridges are
  declared as separate axioms because the *Sail-context* differs —
  same convention as the existing `transpile_JAL` / `transpile_AUIPC`
  operand axioms.

### M-family retirement scoping

The four axioms above (MB-L, MB-S, MS-L, MS-S) are designed to
**replace** per-opcode `h_bus_execute_matches_sail` hypotheses on the
load / store metaplan theorems. Per-opcode rewiring (S5 of
`finishing3.md`) is left to follow-up commits — the bridge lemmas
shipped here unblock that work without performing it.

### S5b: per-opcode metaplan retirement (2026-04-27)

The 11 load / store metaplan theorems (`equiv_{LD,LW,LWU,LH,LHU,LB,
LBU,SD,SW,SH,SB}_metaplan`) have been rewired to drop their
`h_bus_execute_matches_sail` parameter (and the LD-specific
`h_rd_val :` parameter). Each theorem now closes via the structural
bus-emission lemma family in `Airs/BusEmission.lean`
(`bus_effect_matches_sail_load_<n>byte_rrrw`,
`..._loadu_<n>byte_rrrw`, `..._store{,_<n>byte}_rrrw`) plus the
memory-model bridges in `Spec/MemModel.lean`
(`mem_load_correct{,_<n>byte}`, `mem_store_correct{,_<n>byte}`).

**New metaplan parameter classes (S5b).** Each metaplan theorem now
takes:
* `Valid_Main`, `Valid_Mem` AIR witnesses + a `r_main : ℕ` row index
  (CIRCUIT-CONSTRAINT class).
* `h_main_emit_b` / `h_main_emit_c` — the load / store memory-bus
  emission shape (`b_0 = lo(e), b_1 = hi(e)`, `as = 2`,
  `multiplicity = ±1`) — feeds `mem_load_correct` /
  `mem_store_correct`.
* `h_ptr_match` — bridges Sail's `r1_val + signExtend imm` (or
  `r1_val + signExtend imm` for stores) to the bus entry's
  `e.ptr.toNat` (TRANSPILE-PIN class).
* For loads: `h_e1_e2_bytes` (8-byte LD) or `h_high_bytes_<sign|zero>ext`
  (narrow-width loads) — bridges the bus's mem-read-entry bytes to
  the rd-write-entry's lanes via the appropriate Sail-level
  extension shape.
* For stores: `h_byte_<i>` per-byte equalities to
  `BitVec.extractLsb (8(i+1)-1) (8i) r2_val` for SD; for narrow
  stores, a single bridging premise `h_mem_eq` ties the bus's
  8-insert chain on `state.mem` to Sail's narrow `modify_memory_<n>`
  data fields.

**M-family axiom load-bearing status.** M1-M4, M7, M9-M11 (the
`*_pure_equiv_axiom` per-opcode axioms) were already promoted to
theorems in Phase 3.5 (2026-04-22) and were never load-bearing on
the metaplan-parameter retirement; their entries above remain valid
historical audit records. The load-bearing metaplan-side trust is
now MB-L / MB-S / MS-L / MS-S (the four memory-bus / state-bridge
axioms documented immediately above) plus the per-opcode pure-spec
equivalence theorems (no axiom).

**Trust-base impact.** No new axioms beyond MB-L/MB-S/MS-L/MS-S/MB-W
(already on the trust ledger). The S5b rewiring is a strict trust
reduction relative to the parameterized
`h_bus_execute_matches_sail` form — the closure shifts caller
obligations from one monolithic Sail-state-equality predicate to
several smaller circuit-level facts (bus shape + ptr-match + lane
match), each in CIRCUIT-CONSTRAINT, LANE-MATCH, or TRANSPILE-PIN
classes that the broader project plan is auditing separately.

## Inventory update — 2026-04-27 (post finishing1/2/3)

### Current axiom count

`grep -rh "^\s*axiom " ZiskFv/ --include="*.lean" | awk '{print $2}' | sort -u | wc -l`
returns **82** as of HEAD `cde0d6f` on `main`.

Net delta from the 2026-04-25 snapshot (76):
- **+7 new axioms** added in finishing2 + finishing3:
  - `bin_table_consumer_wf` (BT-B, finishing2 S0)
  - `bin_ext_table_consumer_wf` (BT-X, finishing2 S0)
  - `memory_bus_register_write_perm_sound` (MB-W, finishing3 S4)
  - `lookup_consumer_matches_provider_load` (MB-L, finishing3 S3)
  - `lookup_consumer_matches_provider_store` (MB-S, finishing3 S3)
  - `row_models_sail_state_load` (MS-L, finishing3 S3)
  - `row_models_sail_state_store` (MS-S, finishing3 S3)
- **−1 axiom net** elsewhere from Phase 6 retirements between
  2026-04-25 and 2026-04-27 (FENCE on Track R; un-retired/re-counted
  drift on intermediate Phase 6 commits — not separately tracked
  here).

### Updated category breakdown

| # | Category | Count | Confidence-blocking? | Retirement path |
|---|---|---|---|---|
| 1 | Transpile axioms | ~63 | **Yes — most** | Independent audit of `riscv2zisk_context.rs` (or Rust-side proof framework) |
| 2 | Arith lookup axioms | 4 | **Yes — moderate** | Formalize plookup / grand-product soundness in Lean |
| 3 | Platform axioms | 4 | Mild (scope-honest) | Only retire if ZisK's deployment changes |
| 4 | Sail-equivalence axioms | 4 | **No — pure tech debt** | Unfold the corresponding Sail bodies; FENCE retired in Phase 6 Track R |
| 5 | **Bus-protocol soundness axioms** (new) | 7 | **No — project-trusted by design** | All seven (BT-B, BT-X, MB-W, MB-L, MB-S, MS-L, MS-S) live in `Airs/{BinaryTable, BinaryExtensionTable, MemoryBus/{LaneMatch, MemBridge}}` and `Spec/MemModel`. Per `CLAUDE.md`, plookup / logUp / permutation soundness is project-trusted. Closing them would mean formalizing the proving system itself — out of per-opcode scope. |

### M-family load-bearing status (2026-04-27)

The per-opcode `*_pure_equiv_axiom` entries (M1-M4, M7, M9-M11) were
already promoted to theorems in Phase 3.5 (2026-04-22). With the
finishing3 S5b rewires (commit `144fb1b`), these entries are now
**doubly retired**: they were already non-axiomatic at the Sail-side,
and they're no longer load-bearing on the metaplan-parameter side
either (the 11 load/store metaplan theorems take MB-L/MB-S/MS-L/MS-S
as the trust-input now, not the per-opcode M-axiom). The entries
remain in this document as an audit trail of the Phase 3.5 promotion
work; they are no longer part of the active load-bearing trust
surface.

### Per-opcode coverage (2026-04-28)

- **finishing1 (3 ops):** ADD, LUI, ADDI — `equiv_<OP>_metaplan_tier1`
  derives `h_rd_val` from BT-B + circuit primitives. Original
  `equiv_<OP>_metaplan` retained for callers.
- **finishing2 (26 ops):** Logic (6) + Shifts (12) + Compares (4)
  + SUB + ALU-W (3) — `equiv_<OP>_metaplan_tier1` companions on top
  of BT-B / BT-X via 14 `SailBridge` lemmas.
- **finishing3 (11 ops):** LD/LW/LWU/LH/LHU/LB/LBU + SD/SW/SH/SB —
  `h_bus_execute_matches_sail` (and LD-specific `h_rd_val :`) dropped
  in-place from the existing metaplan; replaced by MB-L/MB-S/MS-L/MS-S
  composed through narrow-width `mem_{load,store}_correct_<n>byte`
  bridges. Final grep gate over the 11 files: 0 hits.
- **finishing4 (13 ops):** MUL/MULHU/DIVU/REMU/MULW (5 unsigned) +
  MULH/MULHSU/DIV/DIVW/DIVUW/REM/REMW/REMUW (8 signed) —
  `equiv_<OP>_metaplan_tier1` companions derive `h_rd_val` via two
  new toolkit files (`Fundamentals/PackedBitVec/MulNoWrap.lean` —
  14 theorems for chunk-level MUL/DIV no-wrap; `SignedNoWrap.lean` —
  22 theorems for four-quadrant sign-witness BitVec.toInt extension)
  composed with the existing `Spec/{MulField,MulFieldSigned,
  DivFieldSigned}` field identities and Track P arith_table layer.
  **No new trust axioms** — purely Lean-internal proof work.
- **finishing5 (3 ops):** JAL, JALR, AUIPC — `equiv_<OP>_metaplan_tier1`
  companions derive `h_rd_val` for the `store_pc=1` bus-emission path.
  Required 3 new transpile-PC trust axioms (TP-JAL/TP-JALR/TP-AUIPC)
  bridging Sail PC to Main's `pc` column, plus 1 new memory-bus
  permutation soundness axiom (MB-W-PC, parallel to MB-W but for
  `store_pc=1`). Wide-PC no-wrap toolkit
  (`Fundamentals/PackedBitVec/WidePCNoWrap.lean`) handles FGL values
  up to `2^64−1`. Per-opcode Spec hi/lo theorems in
  `Spec/{Jal,Jalr,AddUpperImmediatePC}.lean`. Hi-half formula
  `store_value[1] = (1 - store_pc) * c[1]` (verbatim from
  `zisk/state-machines/main/pil/main.pil:312`) makes hi-half
  identically zero when store_pc=1.

**56 of 56 RV64IM ops have metaplan parameter retirements landed.**
The complete metaplan-target trust-reduction goal is achieved.

### Trust classification (2026-04-27)

The 7 new bus-protocol axioms cleanly partition the trust surface:

- **2 lookup-table content axioms** (BT-B, BT-X) — assert the
  byte-level switch semantics of two virtual fixed tables in the
  ZisK PIL2 spec. Plookup soundness + table-content correctness
  bundled.
- **3 bus-protocol soundness axioms** (MB-W, MB-L, MB-S) — assert
  permutation soundness on `bus_id = 10`. PLONK-class.
- **2 Sail-state correspondence axioms** (MS-L, MS-S) — assert the
  Mem AIR's view of memory agrees with Sail's `state.mem` on aligned
  reads/writes. Implementation-models-spec faithfulness.

Together these seven, combined with the pre-existing
`OperationBus.matches_entry` (`bus_id = 5000`) and the Transpiler
contract, form the 9-item trusted surface the metaplan revision
notes in `ai_plans/zisk-fv-metaplan.md` (2026-04-27) summarize.
