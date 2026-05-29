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
**is** the trusted computing base for zisk-fv. The source trust ledger
currently records **53 axioms** and the global compliance closure contains
**50 names**, organised into the rationale classes summarised below.

**As of the current `clean-air-integration` head**, the floor is
53 source trust-ledger axioms. The larger historical reductions include
the range-bus consolidations, T4's Clean memory-channel route, T5's
Arith-family retirement of class-#6b source trust, and later Clean trim
passes that removed obsolete scaffolding without adding new trust.

The global theorem dispatches the 63 RV64IM opcodes through a 63-arm
`OpEnvelope` sum type to per-opcode `equiv_<OP>` wrappers
under `ZiskFv/Compliance/Wrappers/<Op>.lean`; each wrapper discharges the canonical `equiv_<OP>`
theorem's promise hypotheses from the trust ledger. The principal
"promise hypothesis" soundness gap surveyed in
[`docs/fv/known-gaps.md`](known-gaps.md) is therefore closed at the
global theorem; the V3 trust gates (`check-closure-vs-baseline` +
the wrapper caller-burden ledger) mechanically prevent regression.

Together with Lean 4's kernel and the LeanRV64D Sail-translated
specification (the LHS of every per-opcode equivalence), the 53
source trust-ledger axioms below **are** the project-internal trusted
computing base. Adding, removing,
renaming, or weakening any axiom is a trust-surface change — see
"Changing the trust surface" at the bottom.

## How to verify the claim

Three independent checks, all run from the repo root:

```bash
trust/scripts/check-all.sh                                      # full V1 gate (CI runs this)
trust/scripts/check-all-semantic.sh                             # full V2 gate (post lake build)
awk '$3=="axiom" {print $4}' trust/baseline-axioms.txt | wc -l  # total: 53
```

The V2 gate's `check-closure-vs-baseline` subcommand enforces that
the live transitive `#print axioms` closure of
`zisk_riscv_compliant_program_bus` matches the unqualified names in
`trust/baseline-axioms.txt` exactly; any silent drift — addition OR
removal — fails the gate.

### Current correction: ArithTable trust shape

The C3/C4 Clean-integration audit found that several class-#6b
`arith_table_op_*` axioms are the wrong trust shape, and some are false as
statements about the real 74-row ArithTable. They bundle three different
claims:

1. the trace row emits an `arith_table_assumes` lookup tuple;
2. the lookup/permutation argument implies that tuple is in the translated
   table;
3. opcode-specific row facts follow from finite table contents.

Only (2) is an appropriate trust boundary while the PLONK/logUp argument
remains out of scope. Item (3) must be proved from the translated table.
Item (1) must be represented by the AIR/Clean row model, not silently
folded into per-op axioms.

C3/C4-b is landed: the old opcode-shaped mode/selector axioms are now
theorems from shared ArithTable lookup membership plus finite-table
projection lemmas under `ZiskFv/AirsClean/ArithTableProjections.lean`.
The per-axiom classification lives in
[`arith-table-axiom-audit.md`](arith-table-axiom-audit.md).
C3.2-P is closed: the ordinary zero-sorry trust gate is restored, and the
known-bad arithmetic-table assumptions have been removed from the active
ArithMul/ArithDiv closures. The live global theorem is now explicitly
defect-aware via `h_known_bugs : Defects.NoKnownDefect env`; signed-MUL
claim weakening lives in the defect ledger, not in hidden proof holes. New
opcode-specific ArithTable axioms are not permitted.

Known defects that weaken or block the public compliance claim are tracked
separately from the trust ledger in [`defects.md`](defects.md). A defect
entry is not a trusted fact and must not be used to justify a new axiom.

Per-class spot check (53 axioms total):

```bash
awk '$3=="axiom" {n=split($2,a,":"); print a[1]}' trust/baseline-axioms.txt \
  | sort | uniq -c
#   6 ZiskFv/AirsClean/Completeness.lean         Clean completeness placeholders (class #C)
#   4 ZiskFv/SailSpec/Auxiliaries.lean           platform-feature scope (classes #7-#10)
#  42 ZiskFv/Trusted/Transpiler.lean             transpile contracts (class #1)
#   1 ZiskFv/ZiskCircuit/MemModel.lean           memory-state bridge -- load (class #2)
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
| 1  | Transpile contracts                 |    42 | `Trusted/Transpiler.lean`             | For each non-defect-gated RV64IM instruction kind, ZisK's Rust transpilation lowers a Sail-decoded `ast` into a Main-row column shape that matches the pure spec. | Direct reading of ZisK's `transpile_*` Rust functions in the `zisk/` submodule; each axiom's docstring cites the exact upstream source line.                 |
| 2  | Memory state bridge — load          |     1 | `ZiskCircuit/MemModel.lean`           | A Mem-AIR row tagged `wr=0` matching a memory-bus entry implies Sail's `state.mem` agrees with the entry's eight bytes.                           | Bridges Mem AIR's column language to Sail's byte-addressable `Std.HashMap` once class #4 has placed the entry on the bus.                                    |
| 4  | Bus / lookup soundness              |     0 | — | Retired from the live trust ledger. | The T4 Clean memory-channel route retired the load/provider, store, and MemAlign sub-doubleword entries from canonical/global trust. T5 retired `main_external_arith_emission_bundle`; T7 retired `main_store_pc_emission_bundle` by deriving store-PC/register-write lanes from selected Clean Main `cMemMessage` structural witnesses. |
| 5b | Range-bus / byte-range soundness    |     0 | — | Retired from the live trust ledger. | T7 removed `range_bus_sound` and `signed_range_bus_sound`; byte and signed-range facts now come from concrete Clean/static lookup witnesses or local row constraints. |
| 6  | Binary / BinaryExtension lookup soundness | 0 | — | Retired from the live trust ledger. `bin_table_consumer_wf`, `bin_ext_table_consumer_wf`, and the residual Binary W-mode facts have all been removed from source. | Binary-family table facts now come from Clean/static lookup witnesses and exact `BinaryTable` row proofs. |
| 6b | Arith range / Euclidean pins |     0 | —              | Retired in T5/T7. The shared `arith_{mul,div}_table_lookup_sound` axioms and the remaining dynamic `arith_table_op_*` / `arith_div_*` source axioms were removed. `MUL*`, `DIV*`, and `REM*` proofs now consume lookup-aware `ArithMulTableWitness` / `ArithDivTableWitness` binders for true static `ArithTableSpec` projections, while known dynamic witness gaps are explicit defects. | No live source axioms remain in this class. Future row/range/operation-bus facts must be proved from constraints and Clean/static lookup facts rather than reintroduced as trust. |
| 7  | Platform — PMP inert                |     1 | `SailSpec/Auxiliaries.lean`               | `LeanRV64D.Functions.pmpCheck _ _ _ _ = pure none`.                                                                                               | ZisK's RV64IM target excludes PMP. Axiomatising as inert is strictly stronger than threading state-level disjointness through every load/store proof.        |
| 8  | Platform — CLINT disjoint           |     1 | `SailSpec/Auxiliaries.lean`               | `LeanRV64D.Functions.within_clint _ _ = pure false`.                                                                                              | ZisK programs do not access the CLINT MMIO region. Same scope-honest framing as #7.                                                                          |
| 9  | Platform — PMA inert                |     1 | `SailSpec/Auxiliaries.lean`               | `LeanRV64D.Functions.pmaCheck _ _ _ _ = pure none`.                                                                                               | Alignment-fault arm short-circuited under the `RISC_V_assumptions` fields already recorded by LeanRV64D.                                                     |
| 10 | Platform — Zicfilp disabled         |     1 | `SailSpec/Auxiliaries.lean`               | `LeanRV64D.Functions.update_elp_state _ = pure ()`.                                                                                               | Zicfilp landing-pad extension is disabled in ZisK's target; helper reduces to no-op under `currentlyEnabled Ext_Zicfilp = false`.                            |
| C  | Clean-Component completeness — NON-SECURITY-CRITICAL | 6 | `AirsClean/Completeness.lean` | `binaryAdd_circuit_completeness`, `memAlignByte_circuit_completeness`, `memAlignReadByte_circuit_completeness`, `arithMul_circuit_completeness`, `arithDiv_circuit_completeness`, `mainWithRomAndMemBus_circuit_completeness` — fill mandatory `completeness` fields for Clean `GeneralFormalCircuit`s as integration proceeds. BinaryExtension's C5 component has trivial proved completeness and does not add an axiom. Binary's C6 component also adds no axiom: its prover-completeness side is explicitly conditional on the row `Spec`, while soundness remains proved from constraints. | zisk-fv is a **soundness-only** verification: it does not prove completeness (that an honest prover can satisfy the constraints — the pre-Clean code never established it either). These axioms are **completeness-direction** — a falsehood in any one CANNOT make a wrong execution verify; the verification's *soundness* does not depend on this class. Clean's `GeneralFormalCircuit` simply makes the field mandatory. (Plan decision D-COMPLETE.) |

Total live count: `trust/baseline-axioms.txt` currently records **53**
axioms, including the 6 non-security-critical Clean completeness axioms in
class C. Class C is separate in kind from the soundness-critical trust classes.

### Recent consolidations (clean-integration branch)

Structural-symmetry consolidations replaced groups of per-AIR /
per-opcode axioms with bus-level / op-parameterized axioms where the
trust content was genuinely shared. The T4 Clean memory route then
retired the subword-store emission axiom entirely from source. T5 then
removed the eight DIV/REM transpiler contracts from the trust ledger because
those opcodes are now explicitly gated by
`ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS` until the dynamic Arith
division/remainder witness route is proved.

* `op_bus_perm_sound_{BinaryAdd, Binary, BinaryExtension}` (3) →
  `op_bus_permutation_sound` (1) — parameterized over an
  `OpBusProvider` sum type. `ZiskFv/Airs/OperationBus/Consolidated.lean`.
* The old Binary table-pin family was retired by the Clean/static Binary
  route; no Binary table-pin axiom remains in the source ledger.

The binary per-target results are preserved as theorems with original
names and signatures, so downstream consumers require no changes.
The retired subword-store memory results are replaced on canonical
SB/SH/SW paths by Clean structural witnesses plus proved adapters.

Remaining soundness-critical axiom classes (#1 transpile, #2 memory
state bridge, and #7-10 platform) are honestly at the right granularity
— per-axiom specialization reflects genuinely distinct trust content
(different Rust source lines, different state-bridge claims, and
different platform-scope reductions). Class #C is separate and
completeness-direction only. Further consolidation would require
typeclass abstractions or disjunctive conclusion shapes that compromise
per-axiom auditability.

### Out-of-scope assumptions (NOT in the 53)

For completeness, two trusts the proofs rely on that are not counted
here:

- **Lean 4's kernel and Mathlib.** Standard for any Lean 4 development.
- **The LeanRV64D Sail translation.** The LHS of every
  `equiv_<OP>` is `LeanRV64D.Functions.execute_*`; we trust
  that this module faithfully reflects upstream `riscv/sail-riscv`
  semantics. The Sail compiler + sail-riscv source pin live in
  `flake.lock` (`sail-src`, `sail-riscv-src`); the build is
  reproduced by `nix build .#sail-lean-tree`.

These are scope decisions, not omissions. The 53 axioms above are the
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
  `Airs/MemoryBus/MemAlignBridge.lean`. It is derived from an explicit
  `SubdoublewordLoadProviderWitness` that unpacks the selected
  MemAlign-family provider row and the ROM-derived row facts. No
  MemAlign permutation or MemAlignRom axiom remains in canonical/global
  closure; the byte-range arithmetic that closes `e.x4..x7 = 0 ∧ ...`
  is pure Lean over that structural witness.

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
which axiom landed when and why. The current state — 53 source
trust-ledger axioms and a 50-name global compliance closure — is the
result of the rounds chronologically listed below, with the Step-4
dead-code cleanup trimming the ledger from 147 to 122 and the later
Clean terminal phases retiring memory and Arith-family trust.

### Step 4 dead-code cleanup (147 → 122)

Removed 25 axioms that previously sat in the ledger but were
unreached by any proof: 15 superseded `transpile_<OP>` contracts, 4
op-bus + 4 memory-bus + 2 ArithTable W-mode selector pins. See
`docs/fv/dead-code-audit.md` for the full audit and the per-axiom
disposition. The cleanup landed before the global theorem was
proved; afterwards the V2 trust gate's `check-closure-vs-baseline`
subcommand enforces that no further dead axioms can survive in the
ledger.

### Binary W-mode lookup retirement

The former W-mode sign-extension and final-carry facts for
ADDW/SUBW/ADDIW are now derived from Clean Binary balance, PIL-shaped
BinaryTable lookup messages, exact static table membership, and the
row-level Binary constraints. No Binary/BinaryExtension class-#6 source
axioms remain in the live trust ledger.

### Step 4.2 round 3 — Four parallel branches landing 13 wrappers

Zero new axioms from the ITYPE constructibility-bundle branch (4
wrappers: ADDI/ANDI/ORI/XORI; uses pre-existing AND/OR/XOR mode pins
via the new pure-Lean `itype_imm_subset_holds_main` bundle +
`itype_imm_subset_binary_row_of_main` bridge); one class-#6 axiom
(`binary_consumer_byte_match_chain_pin`) from the Binary 6-field
chain branch (3 wrappers: SUB/SLTU/SLT; SLTI/SLTIU/ADDIW/SUBW/ADDW
deferred pending integration); the former class-#6b signed-MUL MSB facts
(`arith_mul_na_eq_msb_of_a`, `arith_mul_nb_eq_msb_of_b`) are retired after
T5 made MULH/MULHSU close through the explicit signed-MUL defect
exclusion; three class-#4
axioms from the Mem-stores
RMW branch (`main_store_emission_bundle_{sb,sh,sw}` — narrow-width
RMW emission bundles for SB/SH/SW).

### C3.2-P5 — MULW transpiler contract (+1 in class #1)

`transpile_MULW` fills the missing RV64M MULW Main-row contract in the
same class as `transpile_MUL`, `transpile_MULH`, and the other live
per-opcode transpiler pins. It cites
`riscv2zisk_context.rs:247`, where MULW is emitted through
`create_register_op(..., "mul_w", 4)`: opcode `OP_MUL_W`, external-op
dispatch, `m32 = 1`, no PC/store-PC side effect, `jmp_offset1 =
jmp_offset2 = 4`, and `a`/`b` lanes from `rs1`/`rs2`. The C3.2-P5
MULW repair consumes only the `m32 = 1` and operand-lane pieces to
derive W high-lane collapse; it replaces the false static ArithTable
claim formerly made by `arith_table_op_mulw_mode_pin`'s `sext = 0`
premise. That false axiom declaration has since been deleted.

### Step 4.2 round 2 — W-variant Arith + high-half MUL (+13 axioms)

W-variant Arith class-#6b facts were later retired in T5 by placing the
remaining DIV/REM dynamic witness gap under `h_known_bugs`; one class-#4 op-bus axiom
(`op_bus_perm_sound_ArithMulSecondary`) opening the secondary lane
for the high-half MUL family; and faithful high-half MUL
mode/selector projections consumed by `equiv_MULHU`. The false W-mode
and signed-high-half mode axiom declarations have since been deleted. Round 2
left 20 wrappers behind 4 deeper prerequisites (subsequently
addressed in round 3).

### Step 4.2 round 1 — within-shape mass authoring (+5 axioms, 28 wrappers)

Three former class-#6b Arith facts from the Arith batch were later retired
in T5: true static mode/main-selector pins became finite-table projections,
and the unsigned remainder bound moved under the explicit DIV/REM dynamic
defect;
two class-#6 axioms from the Binary batch
(`binary_b_op_or_sext_eq_OP_AND`, `binary_b_op_or_sext_eq_OP_XOR` for
AND/XOR wrappers); the Mem+ControlFlow batch added zero new axioms
(12 wrappers landed via existing trust closure).

### Step 4.1.8 — ArithMul shape exemplar MUL

The old `arith_table_op_mul_mode_pin` has been deleted because its
all-zero sign-witness claim was false as a static table fact. The wrapper
now uses faithful Clean finite-table projections for basic mode and selector
facts; the remaining exceptional branch is tracked under
`arithMulSignedWitnessSoundness`.

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

### Step 4.1.3 — Mem-stores shape exemplar SD (retired in T4)

`main_store_emission_bundle_sd` was retired in T4. The `equiv_SD`
wrapper now consumes a structural Clean `SdCleanWitness`, and the
ptr/byte facts are derived by the Clean Main c/store adapter instead
of a class-#4 trust-ledger axiom.

### Step 4 DIV pilot — GAP-B sign-witness MSB pins (retired in T5)

`arith_div_np_eq_msb_of_dividend` and `arith_div_nb_eq_msb_of_divisor`
(former class-#6b sign-witness MSB pins on signed DIV/REM rows) were
removed from the trust ledger in T5. The unproved dynamic witness relation is
now represented by `ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS`.

### Step 4 DIV pilot — GAP-M / GAP-C / GAP-A (retired in T5)

The true static signed mode and selector pins are finite-table projections
from `ArithDivTableWitness`. The dynamic Euclidean-remainder bound was
removed from the trust ledger in T5 and is now covered by the explicit
DIV/REM dynamic defect.

### Step 4 DIVW — W-mode signed sign-of-D pin (retired in T5)

`arith_table_op_div_rem_signed_w_d_sign_pin` was removed from the trust
ledger in T5 and is now covered by the explicit DIV/REM dynamic defect.

### Step 4 alpha — W-mode + signed disjunctive ranges (+6 axioms)

Step 4.alpha.B.1 added four W-mode axioms in class #6b: two W-mode
carry-column-range disjunctive axioms and two arith-table operand-pin
axioms for the MULW/DIVW/DIVUW/REMW/REMUW W-variants. Step 4.alpha.A.3
added the two signed-mode disjunctive carry-range axioms.

### Prior Round-3 ControlFlow lift (+1 axiom, retired in T7)

`main_store_pc_emission_bundle` temporarily extended class #4's memory-bus
emission footprint by 1 axiom. T7 retired it from source and from the
global closure by routing LUI/AUIPC/JAL/JALR through explicit Clean Main
`cMemMessage` structural witnesses.

### Prior Round-3 Binary lift (+1 axiom)

`binary_carry_bits_in_range` for the `bits(1) carry[BYTES]` range
fact, extending class #6's range-bus footprint by 1 axiom.
