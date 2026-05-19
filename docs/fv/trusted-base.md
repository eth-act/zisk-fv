# zisk-fv — trusted base

## The claim

The verification claim of zisk-fv is the global compliance theorem

```
ZiskFv.Compliance.zisk_riscv_compliant_program_bus
```

(in `ZiskFv/Compliance.lean`). Its
`#print axioms` closure — captured as a flat list in
[`trust/baseline-zisk-riscv-compliant.txt`](../../trust/baseline-zisk-riscv-compliant.txt)
and as a hashed source-line ledger in
[`trust/baseline-axioms.txt`](../../trust/baseline-axioms.txt) —
**is** the trusted computing base for zisk-fv. The closure currently
contains **104 axioms**, organised into the rationale classes
summarised below.

**As of the `clean-integration` + `clean-full` work** (commits up to
`5e255bb`, tag `phase-5-complete-clean-full`), the floor is 104 — down
from 116 prior. The 12-axiom reduction is the result of the
`range_bus_sound` + `signed_range_bus_sound` consolidations
(class #5b/#6/#6b range axioms collapsed into 2 shared axioms; see
`ZiskFv/Channels/RangeBusSoundness.lean`).

The global theorem dispatches the 63 RV64IM opcodes through a 35-arm
`OpEnvelope` sum type to per-opcode `equiv_<OP>` wrappers
under `ZiskFv/Compliance/Wrappers/<Op>.lean`; each wrapper discharges the canonical `equiv_<OP>`
theorem's promise hypotheses from the trust ledger. The principal
"promise hypothesis" soundness gap surveyed in
[`docs/fv/known-gaps.md`](known-gaps.md) is therefore closed at the
global theorem; the V3 trust gates (`check-closure-vs-baseline` +
the wrapper caller-burden ledger) mechanically prevent regression.

Together with Lean 4's kernel and the LeanRV64D Sail-translated
specification (the LHS of every per-opcode equivalence), the 116
axioms below **are** the trusted computing base. Adding, removing,
renaming, or weakening any axiom is a trust-surface change — see
"Changing the trust surface" at the bottom.

## How to verify the claim

Three independent checks, all run from the repo root:

```bash
trust/scripts/check-all.sh                                      # full V1 gate (CI runs this)
trust/scripts/check-all-semantic.sh                             # full V2 gate (post lake build)
awk '$3=="axiom" {print $4}' trust/baseline-axioms.txt | wc -l  # total: 116
```

The V2 gate's `check-closure-vs-baseline` subcommand enforces that
the live transitive `#print axioms` closure of
`zisk_riscv_compliant_program_bus` matches the unqualified names in
`trust/baseline-axioms.txt` exactly; any silent drift — addition OR
removal — fails the gate.

Per-class spot check (116 axioms total):

```bash
awk '$3=="axiom" {n=split($2,a,":"); print a[1]}' trust/baseline-axioms.txt \
  | sort | uniq -c
#  35 ZiskFv/Airs/Arith/Ranges.lean                arith range / table / Euclidean-bound pins (class #6b)
#   1 ZiskFv/Airs/Binary/BinaryAddRanges.lean       binary-add column range (class #5b)
#   3 ZiskFv/Airs/Binary/BinaryExtensionRanges.lean BinaryExtension shift-pin + row→byte witness (class #6)
#   7 ZiskFv/Airs/Binary/BinaryRanges.lean          Binary range / per-byte / carry / b_op_or_sext consolidated / W-mode pins (class #6)
#   1 ZiskFv/Airs/Tables/BinaryExtensionTable.lean         BinaryExtension lookup soundness (class #6)
#   1 ZiskFv/Airs/Tables/BinaryTable.lean                  Binary lookup soundness (class #6)
#   1 ZiskFv/Airs/Main/Ranges.lean                  Main range-check soundness (class #5b)
#   1 ZiskFv/Airs/MemoryBus/EntryRanges.lean        memory-bus entry byte ranges (class #5b)
#   2 ZiskFv/Airs/MemoryBus/MemAlignBridge.lean     MemAlign permutation + ROM lookup (class #4)
#   7 ZiskFv/Airs/MemoryBus/MemBridge.lean          memory-bus lookup soundness + emission bundles, sub-doubleword consolidated (class #4)
#   1 ZiskFv/Airs/OperationBus/Consolidated.lean   op-bus permutation soundness, consolidated (class #4)
#   1 ZiskFv/ZiskCircuit/MemModel.lean                  memory-state bridge — load (class #2)
#  51 ZiskFv/Trusted/Transpiler.lean           transpile contracts (class #1)
#   4 ZiskFv/SailSpec/Auxiliaries.lean                  platform-feature scope (classes #7–#10)
```

`trust/scripts/check-locality.sh` enforces that no other file under
`ZiskFv/` may declare an axiom (`opaque`, `constant`, `unsafe def`,
`partial def`, `@[extern]`, `@[implemented_by]` are also caught).
The allowlist of files is `trust/allowed-axiom-files.txt`, which is
CODEOWNER-protected. The gate is described in detail in
[`trust/README.md`](../../trust/README.md).

## The flat index

For a flat per-axiom table — one row per axiom with its class, file:line,
and the docstring's first-sentence summary — see
[`axiom-index.md`](axiom-index.md). That file is auto-generated from
`trust/baseline-axioms.txt` + each axiom's source-file docstring by
`tools/trust-ledger-index.py` (refreshed by `trust/scripts/regenerate.sh`).
The narrative per-class rationale below stays here.

## The classes

| #  | Class                               | Count | File                                  | What is asserted                                                                                                                                  | Why we trust it                                                                                                                                              |
| -- | ----------------------------------- | ----: | ------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| 1  | Transpile contracts                 |    51 | `Trusted/Transpiler.lean`             | For each RV64IM instruction kind, ZisK's Rust transpilation lowers a Sail-decoded `ast` into a Main-row column shape that matches the pure spec. | Direct reading of ZisK's `transpile_*` Rust functions in the `zisk/` submodule; each axiom's docstring cites the exact upstream source line.                 |
| 2  | Memory state bridge — load          |     1 | `ZiskCircuit/MemModel.lean`           | A Mem-AIR row tagged `wr=0` matching a memory-bus entry implies Sail's `state.mem` agrees with the entry's eight bytes.                           | Bridges Mem AIR's column language to Sail's byte-addressable `Std.HashMap` once class #4 has placed the entry on the bus.                                    |
| 4  | Bus / lookup soundness              |    10 | `Airs/OperationBus/Consolidated.lean` (1), `Airs/MemoryBus/{MemBridge,MemAlignBridge}.lean` (7 + 2) | Permutation-argument and lookup soundness on the operation-bus, memory-bus, and MemAlign providers: (i) `op_bus_perm_sound_{BinaryAdd,Binary,BinaryExtension}` — a Main-row consumer pairs with a row in the provider AIR (operation_bus); (ii) `lookup_consumer_matches_provider_load` — load consumer ↔ Mem AIR row; (iii) `memalign_load_perm_sound` — sub-doubleword load consumer ↔ MemAlign* row; (iv) `mem_align_rom_subdoubleword_load_value_1_zero` — MemAlignRom lookup pins `value_1 = 0`; (v) `main_load_emission_bundle` / `main_sext_load_emission_bundle` — load and signed-load lane / ptr / rd-routing bundle on Main; (vi) `main_store_pc_emission_bundle` — lane match for `store_pc ∈ {0,1}` register writes; (vii) `main_external_arith_emission_bundle` — rd-write byte-pack lanes for the MUL/DIV family; (viii) `main_store_emission_bundle_{sd,sb,sh,sw}` — byte-extract + ptr-match + RMW high-byte preservation for the four store widths. | PLONK / logUp permutation-argument soundness for `bus_id = 10` (op-bus + mem-bus) and ROM-lookup soundness for the MemAlignRom table. Each axiom's docstring cites the PIL line and Rust transpile function it mirrors. |
| 5b | Range-bus / byte-range soundness    |     3 | `Airs/MemoryBus/EntryRanges.lean`, `Airs/Binary/BinaryAddRanges.lean`, `Airs/Main/Ranges.lean` | Each participating AIR's `bits(8)` / `bits(N)`-annotated columns satisfy the byte-range bus: `memory_bus_entry_byte_range_perm_sound`, `binary_add_columns_in_range`, `main_columns_in_range`. | Lookup-argument soundness on the standard byte-range bus, restricted to participants annotated `bits(N)` in the PIL — see citations in each axiom's docstring. |
| 6  | Binary / BinaryExtension lookup soundness | 12 | `Airs/{Binary,BinaryExtension}Table.lean` (1 + 1), `Airs/Binary/{Binary,BinaryExtension}Ranges.lean` (7 + 3) | Lookup-argument soundness on the Binary and BinaryExtension AIRs: (i) `bin_table_consumer_wf` / `bin_ext_table_consumer_wf` — table-lookup soundness on each; (ii) `binary_columns_in_range` / `binary_extension_columns_in_range` — column range pins; (iii) `binary_per_byte_lookup_witness` — per-byte witness extraction; (iv) `binary_carry_bits_in_range` — `bits(1)` carry-column range; (v) `binary_extension_op_is_shift_pin` — shift/SEXT op classification; (vi) `binary_extension_row_byte_lookups` — row → per-byte lookup witness; (vii) `binary_b_op_or_sext_eq_OP_{OR,AND,XOR}` — Binary `b_op_or_sext` column pins for the three logic ops; (viii) `binary_consumer_byte_match_chain_pin` — full 6-field byte-match chain for SUB/SLT-family; (ix) `binary_w_sext_choice_pin` / `binary_w_mode_carry_7_zero` — W-mode SEXT byte case-split + carry_7=0 corollary for SUBW/ADDW. | Lookup-argument soundness on the Binary and BinaryExtension AIRs (same trust kind as class #4), scoped to lookups against `binary_table.rs::ARITH_TABLE`'s row enumeration. |
| 6b | Arith range / table / Euclidean pins |    35 | `Airs/Arith/Ranges.lean`              | Range-checker bus lookups + arith_table-row sign / mode / operand / sign-witness pins + Euclidean-remainder bound, for the full MUL / DIV / REM family across signed/unsigned × 64/32 (W) modes + MULH-family high-half. Full list: `arith_{mul,div}_columns_in_range`, `arith_{mul,div}_carry_columns_in_range_{unsigned,signed,w}`, `arith_table_op_div_rem_signed_{d_sign,w_d_sign}_pin`, `arith_table_op_{mulw,divw}_operand_pin`, `arith_table_op_div_rem_{signed,unsigned}_mode_pin`, `arith_table_op_div_rem_{signed,unsigned}_w_mode_pin`, `arith_table_op_div_rem_main_selector_pin`, `arith_table_op_div_rem_{signed,unsigned}_main_selector_pin`, `arith_table_op_div_rem_{unsigned,signed}_w_mode_pin`, `arith_div_{np_eq_msb_of_dividend,nb_eq_msb_of_divisor}`, `arith_div_remainder_bound{,_unsigned,_unsigned_w,_signed_w}`, `arith_table_op_{mul,mulhu,mulh,mulhsu}_{mode_pin,main_selector_pin}`, `arith_mul_{na_eq_msb_of_a,nb_eq_msb_of_b}`, `arith_table_op_mulw_mode_pin`. | Range-checker bus lookup soundness on the Arith AIR's `bits(16)`-annotated chunk columns and on the `ARITH_RANGE_CARRY` entry of the arith_range_table; arith_table lookup soundness for the per-row sign/mode/operand/sign-witness/selector pins; binary-bus lookup soundness on the Arith `assumes_operation(|d|<|b|)` consumer for the Euclidean magnitude/sign bound. All sub-classes have the same lookup-soundness trust kind as #4 / #6. |
| 7  | Platform — PMP inert                |     1 | `SailSpec/Auxiliaries.lean`               | `LeanRV64D.Functions.pmpCheck _ _ _ _ = pure none`.                                                                                               | ZisK's RV64IM target excludes PMP. Axiomatising as inert is strictly stronger than threading state-level disjointness through every load/store proof.        |
| 8  | Platform — CLINT disjoint           |     1 | `SailSpec/Auxiliaries.lean`               | `LeanRV64D.Functions.within_clint _ _ = pure false`.                                                                                              | ZisK programs do not access the CLINT MMIO region. Same scope-honest framing as #7.                                                                          |
| 9  | Platform — PMA inert                |     1 | `SailSpec/Auxiliaries.lean`               | `LeanRV64D.Functions.pmaCheck _ _ _ _ = pure none`.                                                                                               | Alignment-fault arm short-circuited under the `RISC_V_assumptions` fields already recorded by LeanRV64D.                                                     |
| 10 | Platform — Zicfilp disabled         |     1 | `SailSpec/Auxiliaries.lean`               | `LeanRV64D.Functions.update_elp_state _ = pure ()`.                                                                                               | Zicfilp landing-pad extension is disabled in ZisK's target; helper reduces to no-op under `currentlyEnabled Ext_Zicfilp = false`.                            |

Total: 51 + 1 + 10 + 3 + 12 + 35 + 4 = **116 axioms**.

### Recent consolidations (clean-integration branch)

Three structural-symmetry consolidations replaced groups of
per-AIR / per-opcode axioms with bus-level / op-parameterized
axioms while preserving the per-target results as derived
theorems. Net: −6 axioms over the prior 122-axiom baseline.

* `op_bus_perm_sound_{BinaryAdd, Binary, BinaryExtension}` (3) →
  `op_bus_permutation_sound` (1) — parameterized over an
  `OpBusProvider` sum type. `ZiskFv/Airs/OperationBus/Consolidated.lean`.
* `main_store_emission_bundle_{sb, sh, sw}` (3) →
  `main_store_emission_bundle_subword` (1) — parameterized over
  store width `n ∈ {1, 2, 4}`. `ZiskFv/Airs/MemoryBus/MemBridge.lean`.
* `binary_b_op_or_sext_eq_OP_{AND, OR, XOR}` (3) →
  `binary_b_op_or_sext_eq_op_general` (1) — parameterized over
  opcode literal. `ZiskFv/Airs/Binary/BinaryRanges.lean`.

The per-target results are preserved as theorems with original
names and signatures, so downstream consumers (per-AIR discharge
bridges, Compliance wrappers) require no changes.

Remaining axiom classes (#1 transpile, #2 mem state bridge, #6b
Arith range/table/Euclidean, #7–10 platform) are honestly at the
right granularity — per-axiom specialization reflects genuinely
distinct trust content (different Rust source lines, different
state-bridge claims, different sign/mode/width specializations).
Further consolidation would require typeclass abstractions or
disjunctive conclusion shapes that compromise per-axiom
auditability.

### Out-of-scope assumptions (NOT in the 116)

For completeness, two trusts the proofs rely on that are not counted
here:

- **Lean 4's kernel and Mathlib.** Standard for any Lean 4 development.
- **The LeanRV64D Sail translation.** The LHS of every
  `equiv_<OP>` is `LeanRV64D.Functions.execute_*`; we trust
  that this module faithfully reflects upstream `riscv/sail-riscv`
  semantics. The Sail compiler + sail-riscv source pin live in
  `flake.lock` (`sail-src`, `sail-riscv-src`); the build is
  reproduced by `nix build .#sail-lean-tree`.

These are scope decisions, not omissions. The 116 axioms above are the
project-internal assumptions on top of those external trusts.

### Load-equivalence trust path

The 7 RV64IM load opcodes (LB, LH, LW, LBU, LHU, LWU, LD) used to
accept unproven OUTPUT-EQ-class hypotheses tying the rd-write bus
entry's bytes to the Sail spec's loaded-data field. They were
rewritten to derive these equations from circuit witnesses:

* **Family A — copyb byte passthrough** (LD, LBU, LHU, LWU):
  `ZiskFv/ZiskCircuit/LoadDerivation.lean::load_copyb_e1_e2_bytes_eq`
  derives per-byte equality between the read entry `e1` and the
  rd-write entry `e2` from Main constraints 9/16 (`(1 -
  is_external_op) * op * (b - c) = 0`) plus byte-range hypotheses on
  both entries. Pure Lean, no new axioms.

* **Family B — sign-extension** (LB, LH, LW): the
  `Circuit/SextLoadBridge.lean::load_{byte,half,word}_c_packed`
  theorems derive the c-packed identity from
  `bin_ext_table_consumer_wf` (class #6), the per-byte
  packed-correctness theorems
  `binary_extension_sext_{b,h,w}_chunks_eq_signextend_nat`
  (proved in `Airs/Binary/BinaryExtensionPackedCorrect.lean`),
  and the operation-bus permutation handshake (caller-supplied
  matching hypotheses on the BinaryExtension AIR's input/output
  byte lanes). No closure axiom — the chain is fully proved.

* **Family C — MemAlign zero-padding** (LBU, LHU, LWU): the
  high-bytes-zero claim for sub-doubleword loads
  (`ind_width ∈ {1, 2, 4}`) is a *theorem* —
  `memalign_subdoubleword_load_high_bytes_zero` in
  `Airs/MemoryBus/MemAlignBridge.lean`. It is derived from two
  narrow class-#4 axioms: (i) `memalign_load_perm_sound`, the
  bus-`bus_id=10` permutation-soundness handshake between Main
  consumers and the MemAlign* providers (MemAlignByte /
  MemAlignReadByte / MemAlign); (ii)
  `mem_align_rom_subdoubleword_load_value_1_zero`, ROM-lookup
  soundness pinning `value_1 = 0` on MemAlign provider rows of
  sub-doubleword width. No standalone closure axiom for the
  zero-pad — the byte-range arithmetic that closes
  `e.x4..x7 = 0 ∧ ...` is in pure Lean, atop the two axioms.

After this rewrite all 63 canonical `equiv_<OP>` theorems pass the
`check-no-output-eq.sh` gate uniformly with no `EXEMPT_STEMS`
carve-out. See `ZiskFv/ZiskCircuit/LoadDerivation.lean` for the proven
derivation lemmas and the equivalence files
(`ZiskFv/Equivalence/{Lb,Lh,Lw,Lbu,Lhu,Lwu,Ld}.lean`)
for the rewritten canonical theorems.

## Inspecting per-theorem trust

`trust/baseline-equiv-axiom-deps.txt` records the transitive
non-kernel axiom closure of each canonical `equiv_<OP>` theorem,
computed via `Lean.collectAxioms` from the V2 trust-gate Lake exe
(`bin/TrustGate/`). One sorted line per theorem:

```
ZiskFv.Equivalence.Add.equiv_ADD: <axiom>, <axiom>, ...
```

Use this when you want to know which axioms a single equivalence
theorem actually depends on — the global `baseline-axioms.txt` says
"these axioms exist", whereas this file says "this theorem consumes
exactly these axioms". The CI gate fails any unack'd line-level
diff, so silent dep growth (or shrinkage) is visible in review even
when the global axiom count is unchanged.

To regenerate:

```bash
lake build
lake exe trust-gate regenerate-deps > trust/baseline-equiv-axiom-deps.txt
git diff trust/baseline-equiv-axiom-deps.txt
```

## Changing the trust surface

Adding, removing, renaming, or weakening any axiom is a
trust-surface change. The protocol:

1. Edit the axiom in one of the files listed in
   `trust/allowed-axiom-files.txt`.
2. Run `trust/scripts/regenerate.sh` to refresh
   `trust/baseline-axioms.txt`,
   `trust/baseline-zisk-riscv-compliant.txt`, and the per-theorem
   axiom-dep baseline.
3. Add or update the corresponding row in the table above with the
   new one-line statement and rationale.
4. Commit axiom + baselines + this doc in the same PR.
5. CODEOWNER review of the `trust/baseline-axioms.txt` diff is the
   audit step (see `.github/CODEOWNERS`).

Adding a new file to `trust/allowed-axiom-files.txt` is itself a
CODEOWNER-protected change.

## History of the trust ledger

The trust ledger grew incrementally as the per-opcode `equiv_<OP>`
proofs were closed; the rounds below preserve the audit trail of
which axiom landed when and why. The current state — 116 axioms,
verified equal to the project-axiom closure of
`zisk_riscv_compliant_program_bus` — is the result of the rounds
chronologically listed below, with the Step-4 dead-code cleanup
trimming the ledger from 147 to 122.

### Step 4 dead-code cleanup (147 → 122)

Removed 25 axioms that previously sat in the ledger but were
unreached by any proof: 15 superseded `transpile_<OP>` contracts, 4
op-bus + 4 memory-bus + 2 ArithTable W-mode selector pins. See
`docs/fv/dead-code-audit.md` for the full audit and the per-axiom
disposition. The cleanup landed before the global theorem was
proved; afterwards the V2 trust gate's `check-closure-vs-baseline`
subcommand enforces that no further dead axioms can survive in the
ledger.

### Step 4.2 round 4 — SUBW/ADDW SEXT byte case-split (+2 in class #6)

`binary_w_sext_choice_pin` (W-mode sign-extension byte choice for
`free_in_c_4..7` based on the low-32-bit result MSB, per
`binary.pil:111` + `binary.pil:120-124` +
`binary_table.rs::ARITH_TABLE`) and `binary_w_mode_carry_7_zero`
(W-mode `carry_7 = 0` bundled corollary) close the SEXT-byte
case-split for SUBW/ADDW that Round 3.II's chain-pin axiom did not
expose for bytes 4..7. Wrappers landed: `equiv_SUBW`
(`Compliance/Wrappers/Subw.lean`), `equiv_ADDW`
(`Compliance/Wrappers/Addw.lean`).

### Step 4.2 round 3 — Four parallel branches landing 13 wrappers (+7 axioms)

Zero new axioms from the ITYPE constructibility-bundle branch (4
wrappers: ADDI/ANDI/ORI/XORI; uses pre-existing AND/OR/XOR mode pins
via the new pure-Lean `itype_imm_subset_holds_main` bundle +
`itype_imm_subset_binary_row_of_main` bridge); one class-#6 axiom
(`binary_consumer_byte_match_chain_pin`) from the Binary 6-field
chain branch (3 wrappers: SUB/SLTU/SLT; SLTI/SLTIU/ADDIW/SUBW/ADDW
deferred pending integration); three class-#6b axioms from the
MULH-family branch (`arith_mul_na_eq_msb_of_a`,
`arith_mul_nb_eq_msb_of_b`, `arith_table_op_mulw_mode_pin`) for
MULH/MULHSU/MULW wrappers; three class-#4 axioms from the Mem-stores
RMW branch (`main_store_emission_bundle_{sb,sh,sw}` — narrow-width
RMW emission bundles for SB/SH/SW).

### Step 4.2 round 2 — W-variant Arith + high-half MUL (+13 axioms)

Six W-variant Arith class-#6b axioms
(`arith_table_op_div_rem_{unsigned,signed}_w_mode_pin`,
`_{unsigned,signed}_w_main_selector_pin`,
`arith_div_remainder_bound_{unsigned,signed}_w`) for the
DIVUW/REMUW/DIVW/REMW wrappers; one class-#4 op-bus axiom
(`op_bus_perm_sound_ArithMulSecondary`) opening the secondary lane
for the high-half MUL family; and six class-#6b high-half MUL
mode/selector pins (`arith_table_op_mulh{,u,su}_mode_pin` +
`_main_selector_pin`) consumed by `equiv_MULHU`. Round 2
left 20 wrappers behind 4 deeper prerequisites (subsequently
addressed in round 3).

### Step 4.2 round 1 — within-shape mass authoring (+5 axioms, 28 wrappers)

Three class-#6b axioms from the Arith batch
(`arith_table_op_div_rem_unsigned_mode_pin`,
`arith_table_op_div_rem_unsigned_main_selector_pin`,
`arith_div_remainder_bound_unsigned` for DIVU/REMU/REM wrappers);
two class-#6 axioms from the Binary batch
(`binary_b_op_or_sext_eq_OP_AND`, `binary_b_op_or_sext_eq_OP_XOR` for
AND/XOR wrappers); the Mem+ControlFlow batch added zero new axioms
(12 wrappers landed via existing trust closure).

### Step 4.1.8 — ArithMul shape exemplar MUL (+2 axioms)

`arith_table_op_mul_mode_pin` and
`arith_table_op_mul_main_selector_pin` — the MUL-side mirrors of the
DIV-pilot mode-pin + main-selector-pin pair, consumed by the
`Compliance/Wrappers/Mul.lean` wrapper to derive seven mode pins and
the `main_mul = 1, main_div = 0` selector pin needed for the hi-lane
discharge of `h_byte_hi` via `mul_bus_res1_eq_c_hi`.

### Step 4.1.6 / 4.1.7 — Mem-load and ControlFlow-branch exemplars (+0 axioms)

LD wrapper: zero new axioms (load-side discharge fully covered by
`main_load_emission_bundle`, `memory_bus_entry_byte_range_perm_sound`,
`lookup_consumer_matches_provider_load`, and `transpile_LD`
consumed transitively via `equiv_LD`'s existing chains). BEQ
wrapper: zero new axioms (`equiv_BEQ` pivots on the Sail pure-spec
equivalence; the wrapper consumes only the existing closure plus a
pure-Lean alignment lemma).

### Step 4.1.4 — Binary shape exemplar OR (+1 axiom)

`binary_b_op_or_sext_eq_OP_OR` (Binary AIR table-pin sub-class)
consumed by `equiv_OR` (`Compliance/Wrappers/Or.lean`).

### Step 4.1.3 — Mem-stores shape exemplar SD (+1 axiom)

`main_store_emission_bundle_sd` (class-#4) delivers byte-extracted
store entry contents and ptr-match for the `equiv_SD`
wrapper in `Compliance/Wrappers/Sd.lean`.

### Step 4 DIV pilot — GAP-B sign-witness MSB pins (+2 axioms)

`arith_div_np_eq_msb_of_dividend` and `arith_div_nb_eq_msb_of_divisor`
(class-#6b sign-witness MSB pins on signed DIV/REM rows that link
`np` to MSB(C) and `nb` to MSB(B)) — consumed by the
`Compliance/Wrappers/Div.lean` wrapper via the new generic
`signed_packed_toInt_eq_of_read_xreg` Sail-state bridge to
discharge the `h_op1` / `h_op2` operand TRANSPILE-BRIDGE binders
of `equiv_DIV` end-to-end.

### Step 4 DIV pilot — GAP-M / GAP-C / GAP-A (+3 axioms)

`arith_table_op_div_rem_signed_mode_pin` (GAP-M, signed non-W
mode-pin), `arith_div_remainder_bound` (GAP-C, Euclidean-remainder
magnitude/sign bound on `arith.pil:274`), and
`arith_table_op_div_rem_main_selector_pin` (GAP-A hi-lane, the
`main_div`/`main_mul` selector pin on signed DIV/REM rows).

### Step 4 DIVW — W-mode signed sign-of-D pin (+1 axiom)

`arith_table_op_div_rem_signed_w_d_sign_pin` (class-#6b).

### Step 4 alpha — W-mode + signed disjunctive ranges (+6 axioms)

Step 4.alpha.B.1 added four W-mode axioms in class #6b: two W-mode
carry-column-range disjunctive axioms and two arith-table operand-pin
axioms for the MULW/DIVW/DIVUW/REMW/REMUW W-variants. Step 4.alpha.A.3
added the two signed-mode disjunctive carry-range axioms.

### Prior Round-3 ControlFlow lift (+1 axiom)

`main_store_pc_emission_bundle` extended class #4's memory-bus
emission footprint by 1 axiom.

### Prior Round-3 Binary lift (+1 axiom)

`binary_carry_bits_in_range` for the `bits(1) carry[BYTES]` range
fact, extending class #6's range-bus footprint by 1 axiom.
