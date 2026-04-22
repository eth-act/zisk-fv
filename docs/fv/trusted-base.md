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

## Phase 3A Track S memory-model axioms (2026-04-22)

The SH (store halfword) and SB (store byte) sibling fan-out ships
two additional trusted memory-model axioms — narrow companions of
M2 (SD) / M4 (SW). Structurally identical to M2/M4 modulo the
`width` parameter and the `modify_memory_{1,2}` primitive; jointly
closable with M1-M4 under the same PMP/CLINT extension to
`RISC_V_assumptions` (see "Why M1-M4 exist" above).

### Entry M10: `PureSpec.execute_STOREH_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/sh.lean`
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

### Entry M11: `PureSpec.execute_STOREB_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/sb.lean`
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

## Phase 3A Branch control-flow axioms (2026-04-22)

The BLT / BGE / BLTU / BGEU sibling fan-out ships four trusted
axioms — one per opcode — under a shared closure path. They parallel
the C1 (JALR) D4b-patch pattern: the Sail `execute_BTYPE` arm for
each of the four comparator opcodes reduces to a straightforward
`taken` predicate (signed/unsigned `<` / `≥` via Sail's `zopz0z*`
helpers), structurally matching the pure-spec `skip` field, but
direct closure via the BNE-style `simp`/`jump_to_equiv` route was
deferred in lockstep for axiom-discipline reasons (see "Why C2
exists" below).

### Entry C2a: `PureSpec.execute_BLT_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/blt.lean`
- **Statement (informal):** under the standard register-state
  hypotheses (imm/r1/r2 readable, PC readable, misa readable with
  `misa[C] = 0`), the Sail
  `execute_BTYPE (imm, r2, r1, bop.BLT)` threaded through the
  `writeReg nextPC (PC+4); execute …` prelude reduces to the
  `execute_BLT_pure` evaluation (signed `<` case on `.toInt`; taken
  → `jump_to PC+imm` with bit0/bit1 misalignment checks; not-taken →
  fall through to PC+4).
- **Consumers:** `PureSpec.execute_BLT_pure_equiv` (in the same
  file); consumed by
  `ZiskFv/Equivalence/BranchLessThan.lean::equiv_BLT_sail` and
  transitively by `equiv_BLT_metaplan`.
- **Provenance:** `LeanRV64D/InstsEnd.lean::execute_BTYPE` BLT arm
  (line 69720) + `LeanRV64D/Prelude.lean::zopz0zI_s` (line 382)
  + the existing `jump_to_equiv` chain used by BEQ/BNE.

### Entry C2b: `PureSpec.execute_BGE_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/bge.lean`
- **Statement (informal):** BGE analogue of C2a — signed `≥` on
  `.toInt` via `zopz0zKzJ_s`. Same structural shape as BLT's
  reduction.
- **Consumers:** `PureSpec.execute_BGE_pure_equiv`;
  `equiv_BGE_sail` and transitively `equiv_BGE_metaplan`.
- **Provenance:** `execute_BTYPE` BGE arm (line 69721)
  + `Prelude.zopz0zKzJ_s` (line 394).

### Entry C2c: `PureSpec.execute_BLTU_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/bltu.lean`
- **Statement (informal):** BLTU analogue — unsigned `<` via
  `zopz0zI_u = .toNatInt <b .toNatInt`, matching the pure spec's
  `.toNat <b .toNat` up to an `Int.ofNat` coercion.
- **Consumers:** `PureSpec.execute_BLTU_pure_equiv`;
  `equiv_BLTU_sail`; `equiv_BLTU_metaplan`.
- **Provenance:** `execute_BTYPE` BLTU arm (line 69722)
  + `Prelude.zopz0zI_u` (line 398)
  + `Sail/Sail.lean::toNatInt = Int.ofNat ∘ BitVec.toNat`.

### Entry C2d: `PureSpec.execute_BGEU_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/bgeu.lean`
- **Statement (informal):** BGEU analogue — unsigned `≥` via
  `zopz0zKzJ_u`. Same structural shape as BLTU.
- **Consumers:** `PureSpec.execute_BGEU_pure_equiv`;
  `equiv_BGEU_sail`; `equiv_BGEU_metaplan`.
- **Provenance:** `execute_BTYPE` BGEU arm (line 69723)
  + `Prelude.zopz0zKzJ_u` (line 410)
  + the `toNatInt` bridge used by C2c.

### Why C2a-C2d exist

Unlike C1 (JALR), which is blocked on a genuine platform-config gap
(`currentlyEnabled Ext_Zicfilp` → `mseccfg.MLPE` probe that
`RISC_V_assumptions` does not witness), C2a-C2d's Sail reduction is
structurally closable via the BNE-style proof skeleton:

```
simp [readReg_succ, execute, writeReg_state_success, execute_BTYPE]
rewrite [rX_read_xreg_equiv …] ; rewrite [read_xreg_write_other_reg_state …] ; simp
by_cases h_cmp : <signed or unsigned comparison>
-- taken branch: jump_to_equiv + misa[C] = 0
-- not-taken: falls through to the pure-spec's PC+4 path
```

The case-split predicate varies per opcode (BLT: `r1.toInt < r2.toInt`;
BGE: `r1.toInt ≥ r2.toInt`; BLTU: `r1.toNat < r2.toNat`; BGEU:
`r1.toNat ≥ r2.toNat`). Each requires a small bridge to align the
`BitVec.toInt`/`.toNatInt` form Sail emits with the `.toInt`/`.toNat`
form the pure spec uses — mechanical but in the aggregate a ≈200-400
line per-opcode closure exercise.

Phase 3A axiomatized the four in lockstep to keep Track B tractable
alongside the five other parallel archetype tracks. Each axiom is
narrow (single-opcode-scoped; no generalization across the branch
family), explicitly audit-flagged, and structurally identical to the
BNE proof except for the comparator. A future consolidated closure
(estimated 1 day total — port BNE's skeleton to four new case-split
predicates + a single Int-coercion bridge lemma) would retire C2a-C2d
together.

**Closure path.** No `RISC_V_assumptions` extension is required —
the same `misa[C] = 0` witness BEQ/BNE consume suffices. Author a
helper lemma `BitVec.toInt_lt_iff : (x.toInt <b y.toInt) = x.slt y`
(or use Lean's existing bridges) and replicate the BNE proof four
times. The Int-coercion bridge for the unsigned opcodes is just
`Int.ofNat_lt` + `decide`-able reassociation.

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

### Entry M7: `PureSpec.execute_LOADHU_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/lhu.lean`
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

### Entry M9: `PureSpec.execute_LOADBU_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/lbu.lean`
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

### Entry C3a: `PureSpec.execute_SHIFTIWOP_slliw_pure_equiv_axiom`

- **File:** `ZiskFv/ZiskFv/RV64D/slliw.lean`
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
