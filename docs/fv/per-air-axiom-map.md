# Per-AIR axiom inventory and predicted-gap map

> **Planning surface for Step 4 of `plan-to-completely-resolve-wild-lynx.md`.**
> Companion to [`docs/fv/discharge-recipe.md`](discharge-recipe.md) (the
> 5-category framework) and [`docs/fv/trusted-base.md`](trusted-base.md)
> (the trust ledger source of truth). For each of the 7 *provider AIRs*
> exposed by the per-opcode equivalence proofs, this doc enumerates the
> trust-ledger axioms that already cover the AIR and predicts the
> additional axiom surface the AIR's *discharge pilot* is expected to
> need, by walking DIV's 5-category template against the AIR's
> shape.

## Scope and reading guide

The 7 provider AIRs covered here are the AIRs whose discharge
bridges live under `ZiskFv/Equivalence/Bridge/`. They are the
provider side of the cross-AIR matching identities that every
canonical `equiv_<OP>` theorem either consumes (Tier-3 shapes) or
will consume after promise discharge (Tier-1 / Tier-2 shapes). See
[`docs/fv/known-gaps.md`](known-gaps.md) for the tiering.

**Snapshot.** This inventory is taken at commit `83532d7` — the
state immediately after the DIV pilot closed (Step 4 of
`plan-to-completely-resolve-wild-lynx.md`'s pilot phase). Trust
ledger size at this commit: **116 axioms** across ~11 classes.

**Categories from `discharge-recipe.md`.** Each "Predicted gaps"
section walks five categories the DIV pilot established:

1. **Lane-match** — the cross-AIR equation linking Main's emission
   slots to the provider AIR's witness columns (op-bus
   `matches_entry`, c-lane chain, etc.).
2. **Mode pins** — table-lookup-pinned mode columns on the provider
   AIR (`m32`, `sext`, `div`, etc.) that select the row's
   constraint specialization.
3. **Sign-witness pins** — table-lookup-pinned sign columns (`np`,
   `nb`, `nr`, `na`) tying sign witnesses to MSBs of signed inputs.
   Only relevant when the AIR has signed paths.
4. **Range/bound** — range-checker bus soundness on chunk / carry /
   byte columns (the `bits(K)` annotations in PIL) plus magnitude
   bounds (e.g. DIV's Euclidean-remainder bound).
5. **Operand bridges** — cross-shape equalities between the
   provider AIR's input chunks and the operands the Sail spec
   reads from registers (the `signed_packed_toInt_eq_of_read_xreg`
   / `unsigned_packed_toNat_eq_of_read_xreg` bridges).

For each AIR, the "Predicted gaps" section flags each category as:

* **Discharged** — axiom already on the trust ledger.
* **Bridge-only** — closed by a pure-Lean derivation under an
  existing axiom (no new axiom needed).
* **Predicted** — likely to need a new axiom; class and PIL
  citation suggested.
* **TBD** — to be determined by the AIR's pilot.

## Trust-ledger snapshot by AIR

| AIR | Provider axioms (this AIR's specific axioms) | Cross-AIR axioms consumed | Total fingerprint |
|---|---|---|---|
| **BinaryAdd** | 1 | 1 (op-bus) | 2 |
| **Binary** | 3 + 1 (table) | 1 (op-bus) | 5 |
| **BinaryExtension** | 3 + 1 (table) | 1 (op-bus) | 5 |
| **ArithMul** | (see Arith Ranges, shared with ArithDiv) | 1 (op-bus) | shares 17 with ArithDiv |
| **ArithDiv** | 17 in Arith Ranges (shared with ArithMul) | 2 (op-bus primary + secondary) | shares 17 with ArithMul |
| **Mem** | 8 in MemBridge/MemAlignBridge + 2 (LaneMatch) + 1 (EntryRanges) + 2 (MemModel) | — | 13 |
| **ControlFlow** | (none specific) | — | 0 (relies on Main range + transpile + memory-bus axioms when JAL/JALR/AUIPC store_pc fires) |

Cross-cutting axioms NOT counted in any AIR's column (because they
apply globally):

* 66 transpile contracts in `Fundamentals/Transpiler.lean` — one
  per RV64IM instruction kind, consumed by every per-opcode proof.
* 4 platform-feature axioms in `SailSpec/Auxiliaries.lean` (PMP / CLINT
  / PMA / Zicfilp).
* 1 main-range axiom (`main_columns_in_range`) in
  `Airs/Main/Ranges.lean`.

Total: 13 + 0 + 5 + 5 + 17 (Arith shared) + 1 (BinaryAdd) + 66
(transpile) + 4 (platform) + 1 (main range) + 2 (op-bus
ArithMul/ArithDivSecondary not separately counted above) +
remainder = 116. The "fingerprint" column above counts only the
AIR-specific axioms most likely to dominate the AIR's discharge
pilot, not the cross-cutting infrastructure.

---

## BinaryAdd (covers 2 opcodes: ADD, ADDI)

**Validator:** `ZiskFv/Airs/Binary/BinaryAdd.lean::Valid_BinaryAdd`
**Discharge bridge:** `ZiskFv/Equivalence/Bridge/BinaryAdd.lean`
**Provider-bus axiom:** `op_bus_perm_sound_BinaryAdd` in
`ZiskFv/Airs/OperationBus/Bridge.lean:54`

### Trust-ledger axioms already in place

| Axiom | Class | Source | Discharges |
|---|---|---|---|
| `op_bus_perm_sound_BinaryAdd` | #4 (op-bus perm) | `Airs/OperationBus/Bridge.lean:54` | cross-AIR matches_entry between Main's op-bus consumer and BinaryAdd's provider |
| `binary_add_columns_in_range` | #5b (range-bus) | `Airs/Binary/BinaryAddRanges.lean:59` | chunk-range bounds on BinaryAdd's `bits(N)`-annotated columns |

### Predicted gaps for the AIR's discharge pilot

* **Lane-match:** Discharged. The op-bus axiom plus the lane-match
  packaging in `Bridge/BinaryAdd.lean` already supplies the
  Main↔BinaryAdd row-match identity. The remaining downstream work
  (`WriteValueProofs.Arith.h_rd_val_arith_add`) is pure Lean atop
  these axioms.
* **Mode pins:** N/A. BinaryAdd has no mode-selector columns —
  ADD and ADDI share the same row shape.
* **Sign-witness pins:** N/A. ADD/ADDI are unsigned add; there is
  no MSB-tied sign witness column.
* **Range/bound:** Discharged via `binary_add_columns_in_range`.
* **Operand bridges:** Discharged via `Bridge/SailStateBridge.lean`'s
  `add_input_bridges_of_read_xreg` (pure Lean; no axiom).

### Pilot scope

When ArithDiv's pilot ran (DIV), it added 6 axioms across classes 4
and 6b. Expected for BinaryAdd: **0–1 new axioms**. The shape is
the simplest of the seven — single bus, no mode/sign columns. Any
new axiom would most likely sit in the lane-match category if the
existing op-bus axiom's hypotheses prove insufficient for ADD's
specific `Valid_Main`↔`Valid_BinaryAdd` row-shape bridge.

### Pilot status (Step 4.1.2 — ADD exemplar)

**Actual: 0 new axioms** for the ADD exemplar
(`ZiskFv/Compliance/Wrappers/Add.lean`,
`equiv_ADD`). Matches the prediction's lower bound (0–1).

Composition: `transpile_ADD` (class #1) + `op_bus_perm_sound_BinaryAdd`
(class #4) + `memory_bus_entry_byte_range_perm_sound` (class #5b) +
`equiv_ADD`'s existing transitive closure
(`binary_add_columns_in_range` class #5b). No category 1–5 work
surfaced a new axiom:

* **Lane-match (category 1)** is internalized by `equiv_ADD` via
  `add_discharge` — no wrapper-level work.
* **Mode pins (category 2)** N/A on the provider side; the Main-side
  pins `m32 = 0` (from `transpile_ADD`) and `flag = 0` (from
  `op_bus_perm_sound_BinaryAdd` → `matches_entry` flag-slot
  projection) are derivations of existing axioms.
* **Sign-witness pins (category 3)** N/A — ADD is unsigned.
* **Range/bound (category 4)** internal chunk ranges discharged by
  `equiv_ADD` via `binary_add_columns_in_range`; the 8 memory-bus
  entry byte ranges (`h_e2_0..h_e2_7`) discharged uniformly via
  `memory_bus_entry_byte_range_perm_sound`.
* **Operand bridges (category 5)** internalized by `equiv_ADD` via
  `add_input_bridges_of_read_xreg` — no wrapper-level work.

Caller-burden (per discharge-recipe.md): 34 binders / 20 hypotheses
on `equiv_ADD` vs. 41 / 27 on `equiv_ADD`. **Net −7
binders / −7 hypotheses**. Composition: drops `h_main_mode` (1) and
`h_e2_0..h_e2_7` (8); adds `h_main_active`, `h_main_op_add` (2) —
the activation/opcode pins from Compliance.lean's program-counter
handshake.

Cross-shape lessons:
* **No new bridge added** to `Equivalence/Bridge/SailStateBridge.lean`
  or `Equivalence/Bridge/BinaryAdd.lean`. The existing `add_discharge`
  bridge already handles every category-1/4/5 promise internally;
  the wrapper only repackages the structural Main-mode bundle
  (`main_row_in_add_mode`) and the byte-range bulk.
* **`flag = 0` projection from `matches_entry`** is a one-liner
  reusable for BinaryAdd shape only (ADDI). Other provider AIRs
  carry an output in the `flag` slot (Binary's `cout`, Arith's
  comparison verdicts), so the projection stays in the BinaryAdd
  exemplar file rather than being lifted to a generic bridge.
* The discharge generalizes mechanically to ADDI in Step 4.2:
  swap `transpile_ADD` for `transpile_ADDI` (and pin `m.op = OP_ADD`
  per `Transpiler.lean:1898` — ADDI piggybacks on OP_ADD); the
  matches_entry flag projection and byte-range discharge work
  unchanged. **Predicted: still 0 new axioms for ADDI.**

The trust-ledger size stays at 116 axioms across the BinaryAdd
shape — confirming that BinaryAdd is the cleanest provider-AIR
shape and that the per-AIR axiom map's 0–1 prediction was correct.

---

## Binary (covers 14 opcodes: AND, ANDI, OR, ORI, XOR, XORI, SLT, SLTI, SLTU, SLTIU, SUB, SUBW, ADDIW, ADDW)

**Validator:** `ZiskFv/Airs/Binary/Binary.lean::Valid_Binary`
**Discharge bridge:** `ZiskFv/Equivalence/Bridge/Binary.lean`
**Provider-bus axiom:** `op_bus_perm_sound_Binary` in
`ZiskFv/Airs/OperationBus/Bridge.lean:77`

### Trust-ledger axioms already in place

| Axiom | Class | Source | Discharges |
|---|---|---|---|
| `op_bus_perm_sound_Binary` | #4 (op-bus perm) | `Airs/OperationBus/Bridge.lean:77` | cross-AIR matches_entry for Binary-shape opcodes |
| `binary_columns_in_range` | #6 (range-bus) | `Airs/Binary/BinaryRanges.lean:56` | chunk-range bounds on Binary's `bits(8)` byte columns |
| `binary_per_byte_lookup_witness` | #6 (range-bus) | `Airs/Binary/BinaryRanges.lean:149` | per-byte BinaryTable lookup witness — links each row byte slot to a `consumer_byte_match_chain` instance |
| `binary_carry_bits_in_range` | #6 (range-bus) | `Airs/Binary/BinaryRanges.lean:198` | `(v.carry_i r).val < 2` for the 8 `bits(1) carry[BYTES]` columns (`binary.pil:67`) — needed for AND/OR/XOR `c_7 = 0` derivation |
| `binary_b_op_or_sext_eq_OP_OR` | #6 (table-pin) | `Airs/Binary/BinaryRanges.lean:263` | for any Binary row whose op-bus emission `b_op + 16 * mode32 = 15` (OP_OR), `b_op_or_sext = OP_OR` (`binary.pil:104` + `binary.pil:131-148`). Added by Step 4.1.4 (OR exemplar). |
| `binary_b_op_or_sext_eq_OP_AND` | #6 (table-pin) | `Airs/Binary/BinaryRanges.lean` | parallel pin for `b_op + 16 * mode32 = 14` (OP_AND). Added by Step 4.2.B (AND wrapper). |
| `binary_b_op_or_sext_eq_OP_XOR` | #6 (table-pin) | `Airs/Binary/BinaryRanges.lean` | parallel pin for `b_op + 16 * mode32 = 16` (OP_XOR). Added by Step 4.2.B (XOR wrapper). |
| `binary_consumer_byte_match_chain_pin` | #6 (chain-pin) | `Airs/Binary/BinaryRanges.lean:398` | 6-field per-byte chain witness exposing `cin`/`pos_ind` for SUB/SLT-family + W-mode (`op_emit ∈ {0x06, 0x07, 0x0B, 0x1A, 0x1B}`). Added by Step 4.2 round 3.II (SUB wrapper). |
| `binary_w_sext_choice_pin` | #6 (W-mode SEXT) | `Airs/Binary/BinaryRanges.lean:542` | W-mode (`op_emit ∈ {0x1A, 0x1B}`) sign-extension byte choice — for `free_in_c_4..7`, either all `0x00` and low-32 result MSB = 0, or all `0xFF` and MSB = 1. Added by Step 4.2 round 4.B (SUBW/ADDW wrappers). |
| `binary_w_mode_carry_7_zero` | #6 (W-mode chain-end) | `Airs/Binary/BinaryRanges.lean:568` | W-mode (`op_emit ∈ {0x1A, 0x1B}`) `v.carry_7 r = 0` bundled corollary. Added by Step 4.2 round 4.B (SUBW/ADDW wrappers). |
| `bin_table_consumer_wf` | #6 (lookup-bus) | `Airs/BinaryTable.lean:281` | BinaryTable consumer rows (`multiplicity = 1`) satisfy `wf_properties` |

### Predicted gaps for the AIR's discharge pilot

* **Lane-match:** Discharged. Op-bus axiom plus the per-byte lookup
  witness give the byte-level chain that downstream `equiv_<OP>`
  theorems substitute into `h_match_clo` / `h_match_chi`.
* **Mode pins:** **Predicted.** Binary covers 14 ops across several
  sub-shapes (AND/OR/XOR byte-local logic; SUB/SUBW/SLT*/ADDIW/ADDW
  with carry-chain). The PIL row at `binary.pil` discriminates
  these via `op` literal and `m32` (W-mode). At least one mode-pin
  axiom is likely needed to pin `m32 ∈ {0, 1}` from the op literal
  (analogous to DIV's `arith_table_op_div_rem_signed_mode_pin`).
  Class #6 (table-lookup soundness on the binary AIR's row-type
  selector lookup).
* **Sign-witness pins:** **Predicted.** SLT / SLTI involve signed
  comparison; ADDIW / ADDW / SUBW involve 32-bit sign extension.
  At minimum a sign-of-result / sign-of-operand pin will be needed
  for SLT-family — likely class #6, analog to
  `arith_div_np_eq_msb_of_dividend`. PIL cite: TBD — by inspection
  of `binary.pil`'s signed-op rows.
* **Range/bound:** Mostly discharged via `binary_columns_in_range`
  + `binary_carry_bits_in_range`. **Bridge-only** for the
  `carry_7 = 0` derivation for AND/OR/XOR (already done via
  `Bridge.Binary.carry_7_zero_{AND,OR,XOR}_pure`).
* **Operand bridges:** Discharged via `Bridge/SailStateBridge.lean`
  per opcode shape. ADDIW / SUBW / ADDW will use a packed-nat lift
  on 32-bit operands plus the `transpile_*W` axioms — pure Lean
  atop existing axioms.

### Pilot scope

When ArithDiv's pilot ran, it added 6 axioms across classes 4 and
6b. Expected for Binary: **~2–4 new axioms** spread across mode
pins (1–2 axioms for `m32` and op-literal pinning) and sign-witness
pins (1–2 axioms for SLT-family signed comparison). The byte-chain
infrastructure is already in place; the gap is on mode/sign for the
14-opcode coverage. Larger surface than BinaryAdd because of the
op-class diversity.

### Pilot landed (Step 4.1.4 — OR exemplar)

**Added: 1 axiom** at the low end of the 2–4 prediction.

| New axiom | Class | Source | Discharges (in `equiv_OR`) |
|---|---|---|---|
| `binary_b_op_or_sext_eq_OP_OR` | #6 (table-pin) | `Airs/Binary/BinaryRanges.lean:263` | `h_bop_or_sext : (v.b_op_or_sext r_binary).val = OP_OR` |

Composition: `op_bus_perm_sound_Binary` (class #4) provides the
existential row witness `r_binary` + the `matches_entry` predicate.
Projecting matches_entry's `.op`-slot equality through
`h_main_op_or : m.op r_main = OP_OR` gives
`v.b_op r_binary + 16 * v.mode32 r_binary = 15`, which feeds the
new pin axiom to deliver `(v.b_op_or_sext r_binary).val = OP_OR`.

Caller-burden drop on `equiv_OR` vs `equiv_OR`: **−3
binders / −3 hypotheses** (`r_binary`, `h_match`, `h_bop_or_sext`).
At the global Compliance.lean level the reduction extends further
because `(m, v, ∀ r, core_every_row v r)` collapse into shared
parameters across all 14 Binary-shape opcodes.

### Within-shape mass-author predictions

For each of the 13 remaining Binary-shape opcodes (AND, ANDI, OR
already piloted, ORI, XOR, XORI, SLT, SLTI, SLTU, SLTIU, SUB, SUBW,
ADDIW, ADDW), the wrapper authoring will follow the OR exemplar's
shape. New axiom budget:

* **AND / ANDI** (2 wrappers): `binary_b_op_or_sext_eq_OP_AND` —
  the OP_AND parallel of (e). +1 axiom, shared across the 2
  wrappers.
* **XOR / XORI** (2 wrappers): `binary_b_op_or_sext_eq_OP_XOR` —
  the OP_XOR parallel. +1 axiom, shared.
* **ORI** (1 wrapper): reuses `binary_b_op_or_sext_eq_OP_OR`. 0
  new axioms.
* **SLT family** (4 wrappers — SLT, SLTI, SLTU, SLTIU): sign-witness
  pins are needed for the signed forms (SLT, SLTI); the unsigned
  forms (SLTU, SLTIU) reuse the unsigned-comparison output column.
  Predicted: +1–2 axioms (a `binary_use_first_byte_pin_SLT_family`
  and/or `binary_c_is_signed_pin_for_signed_compare`).
* **SUB / SUBW / ADDIW / ADDW** (4 wrappers): need cin-chain
  6-field consumer match instead of the byte-local 3-field form;
  also need an m32 pin for the W variants (SUBW, ADDIW, ADDW).
  Predicted: +1–2 axioms (`binary_consumer_byte_match_chain_pin`
  and/or `binary_mode32_pin_for_W_ops`).

**Running budget after the within-shape phase:** 1 (this pilot) + 2
(AND/XOR pins) + 1–2 (SLT signed) + 1–2 (SUB chain + W-mode) = **5–7
total class-#6 additions** for the entire Binary shape. The OR pilot
landed cleanly on the low end of the 2–4 prediction because the
byte-local logic sub-shape (AND/OR/XOR) is the simplest of the four
sub-shapes inside the Binary AIR's 14-opcode coverage.

---

## BinaryExtension (covers 15 opcodes: SLL, SLLI, SRL, SRLI, SRA, SRAI, SLLW, SRLW, SRAW, SLLIW, SRLIW, SRAIW, plus internal SEXT_B/SEXT_H/SEXT_W consumed by LB/LH/LW)

**Validator:** `ZiskFv/Airs/Binary/BinaryExtension.lean::Valid_BinaryExtension`
**Discharge bridge:** `ZiskFv/Equivalence/Bridge/BinaryExtension.lean`
**Provider-bus axiom:** `op_bus_perm_sound_BinaryExtension` in
`ZiskFv/Airs/OperationBus/Bridge.lean:101`

### Trust-ledger axioms already in place

| Axiom | Class | Source | Discharges |
|---|---|---|---|
| `op_bus_perm_sound_BinaryExtension` | #4 (op-bus perm) | `Airs/OperationBus/Bridge.lean:101` | cross-AIR matches_entry for BinaryExtension-shape opcodes |
| `binary_extension_columns_in_range` | #6 (range-bus) | `Airs/Binary/BinaryExtensionRanges.lean:53` | chunk-range bounds on BinaryExtension's `bits(8)` byte columns |
| `binary_extension_row_byte_lookups` | #6 (range-bus) | `Airs/Binary/BinaryExtensionRanges.lean:136` | per-byte BinaryExtensionTable lookup witness for each row's byte slots |
| `binary_extension_op_is_shift_pin` | #6 (table-pin) | `Airs/Binary/BinaryExtensionRanges.lean:106` | pins `v.op_is_shift r = 1` for shift literals / 0 for SEXT literals (per `binary_extension.pil:88,92`) |
| `bin_ext_table_consumer_wf` | #6 (lookup-bus) | `Airs/BinaryExtensionTable.lean:262` | BinaryExtensionTable consumer rows satisfy `wf_properties` (covers SEXT_B/H/W) |

### Predicted gaps for the AIR's discharge pilot

* **Lane-match:** Discharged. Op-bus + per-byte lookup witness give
  the cross-AIR equations downstream shifts and SEXT loads
  substitute into `h_match_clo` / `h_match_chi`.
* **Mode pins:** Discharged for the shift/SEXT split via
  `binary_extension_op_is_shift_pin`. Additional W-vs-non-W mode
  pin **predicted** for the `*IW` family (SLLIW, SRLIW, SRAIW) —
  the W variants restrict the shift count to `[0, 32)` vs `[0, 64)`
  for the 64-bit shifts; a row-side pin on `m32` (or equivalent)
  may be needed. PIL cite: `binary_extension.pil` W-rows; class #6.
* **Sign-witness pins:** **Predicted.** SRA / SRAI / SRAW / SRAIW
  perform arithmetic right shift — the sign-extension byte
  inserted into the MSB must be pinned to MSB(input) on the
  provider AIR side. Likely one new class-#6 axiom analog to
  `arith_div_np_eq_msb_of_dividend`. PIL cite: `binary_extension.pil`
  SRA/SRAI row signature.
* **Range/bound:** Discharged via `binary_extension_columns_in_range`
  + `binary_extension_row_byte_lookups`.
* **Operand bridges:** Discharged via `Bridge/SailStateBridge.lean`
  + `transpile_S{LL,RL,RA}*` axioms (already on the books for all
  12 shift opcodes + 3 SEXT variants).

### Pilot scope

Expected for BinaryExtension: **~1–2 new axioms** — primarily the
SRA-family sign-extension pin, possibly a W-mode mode-pin. Smaller
surface than Binary's pilot because the AIR's row structure is more
uniform (it's a pure shift / sign-extension AIR with no carry
chain to discharge). The SEXT load path is already known to work
(LB / LH / LW are closed via `Circuit/SextLoadBridge.lean` consuming
`bin_ext_table_consumer_wf`); the pilot's job is to lift the same
discharge to the 12 shift opcodes' `h_match_clo` / `h_match_chi`.

---

## ArithMul (covers 5 opcodes: MUL, MULH, MULHU, MULHSU, MULW)

**Validator:** `ZiskFv/Airs/Arith/Mul.lean::Valid_ArithMul`
**Discharge bridge:** `ZiskFv/Equivalence/Bridge/Arith.lean` —
entry point `arith_mul_discharge_conservative`
**Provider-bus axiom:** `op_bus_perm_sound_ArithMul` in
`ZiskFv/Airs/OperationBus/Bridge.lean:120`

ArithMul and ArithDiv share the Arith AIR's chunk / carry columns
and the arith_table lookup. All "Arith Ranges" axioms listed here
appear once in `ZiskFv/Airs/Arith/Ranges.lean` but cover both AIRs
via separate signatures (`arith_mul_*` vs `arith_div_*`).

### Trust-ledger axioms already in place (MUL-side)

> Current correction: this subsection is historical. The false
> opcode-shaped ArithTable axioms named below for `MUL`, `MULH`,
> `MULHSU`, and `MULW` have been deleted from the Lean trust ledger.
> The current generated ledger is `docs/fv/axiom-index.md`; the signed
> multiply leftovers are tracked as
> `ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS`, not as active
> ArithTable trust-shape axioms.

| Axiom | Class | Source | Discharges |
|---|---|---|---|
| `op_bus_perm_sound_ArithMul` | #4 (op-bus perm) | `Airs/OperationBus/Bridge.lean:120` | cross-AIR matches_entry for MUL-family opcodes |
| `arith_mul_columns_in_range` | #6b (range-bus) | `Airs/Arith/Ranges.lean:43` | `bits(16)` chunk-range on a/b/c/d columns (PIL `arith.pil:17-20`) |
| `arith_mul_carry_columns_in_range_unsigned` | #6b (range-bus) | `Airs/Arith/Ranges.lean:109` | 7-carry-witness range under unsigned mode (na=nb=np=nr=0) |
| `arith_mul_carry_columns_in_range_signed` | #6b (range-bus) | `Airs/Arith/Ranges.lean:177` | signed-mode disjunctive carry-range (`arith.pil:280` + `arith_range_table.pil:69`) |
| `arith_mul_carry_columns_in_range_w` | #6b (range-bus) | `Airs/Arith/Ranges.lean:296` | W-variant (m32=1) carry-range |
| `arith_table_op_mul_mode_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean` (new) | MUL-pilot mode pin: `op = 180` ⇒ `na = nb = np = nr = sext = m32 = div = 0` |
| `arith_table_op_mul_main_selector_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean` (new) | MUL-pilot selector pin: `op = 180` ⇒ `main_mul = 1, main_div = 0` |
| `arith_table_op_mulhu_mode_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:927` | MULHU mode pin: `op = 177` ⇒ all 7 mode/sign witnesses = 0 |
| `arith_table_op_mulhu_main_selector_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:946` | MULHU selector pin: `op = 177` ⇒ `main_mul = 0, main_div = 0` |
| `arith_table_op_mulh_mode_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:977` | MULH mode pin: `op = 181` ⇒ `nr=sext=m32=div=0`, na/nb boolean, np XOR |
| `arith_table_op_mulh_main_selector_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:993` | MULH selector pin: `op = 181` ⇒ `main_mul = 0, main_div = 0` |
| `arith_table_op_mulhsu_mode_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:1003` | MULHSU mode pin: `op = 179` ⇒ `nb=nr=sext=m32=div=0`, na boolean, np XOR |
| `arith_table_op_mulhsu_main_selector_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:1018` | MULHSU selector pin: `op = 179` ⇒ `main_mul = 0, main_div = 0` |
| `arith_mul_na_eq_msb_of_a` | #6b (table-pin) | `Airs/Arith/Ranges.lean` (Step 4.2 r3.III) | r3.III: `op ∈ {179, 181}` ⇒ `na.val = MSB(packed4 a[0..3])` |
| `arith_mul_nb_eq_msb_of_b` | #6b (table-pin) | `Airs/Arith/Ranges.lean` (Step 4.2 r3.III) | r3.III: `op = 181` ⇒ `nb.val = MSB(packed4 b[0..3])` |
| `arith_table_op_mulw_mode_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean` (Step 4.2 r3.III) | r3.III MULW mode pin: `op = 182` ⇒ `nr=sext=div=0, m32=1`, na/nb boolean, np XOR |
| `ExternalArithMemoryWitness` | structural witness | `Compliance/SharedBundles.lean` | T5 replacement for the retired `main_external_arith_emission_bundle`: rd-write entry byte-pack lanes are derived from the selected Clean Main `cMemMessage` row, `store_pc = 0`, and the memory-entry match. |

### Pilot status — landed at Step 4.1.8

The ArithMul shape exemplar `equiv_MUL`
(`ZiskFv/Compliance/Wrappers/Mul.lean`) closes all five
discharge categories for the low-half MUL opcode (OP_MUL = 180) end-to-end
using **2 new class-#6b axioms** (the two pins listed above) — well
within the 3-5 prediction.

* **Lane-match:** Discharged via `ExternalArithMemoryWitness`
  (the c_0/c_1 byte lanes) composed with the op-bus `matches_entry`
  projection on `opBus_row_Arith` plus, for the hi side, the existing
  `mul_bus_res1_eq_c_hi` bridge (`Airs/Arith/Bridge1.lean:56`) under
  the MUL-primary mode pins (`main_mul = 1`, `main_div = 0`) derived
  from the new `arith_table_op_mul_main_selector_pin`.
* **Mode pins:** Discharged by the new `arith_table_op_mul_mode_pin`
  bundling all seven (na/nb/np/nr/sext/m32/div = 0). The low-half MUL
  row in `arith_table_data.rs` uses the unsigned carry chain (the low
  64 bits of `a * b` are sign-agnostic).
* **Sign-witness pins:** Not needed for MUL — `equiv_MUL` consumes
  `r1.toNat` / `r2.toNat` (unsigned packed4), not the signed form.
  MULH / MULHU / MULHSU will need parallel mode-pin / selector-pin
  axioms and, for MULH and MULHSU, sign-witness MSB pins on `na` /
  `nb` (mirroring DIV's `arith_div_np_eq_msb_of_dividend` /
  `arith_div_nb_eq_msb_of_divisor`).
* **Range/bound:** None needed for MUL (no remainder bound).
* **Operand bridges:** Discharged via the generic
  `packed_lane_eq_of_read_xreg` (unsigned form) composed with
  `transpile_MUL` and the matches_entry projection of Main's `a`/`b`
  lanes to ArithMul's `a[]`/`b[]` packings. No new bridge needed.

### Within-shape mass authoring template (MULH / MULHU / MULHSU / MULW)

Each of the 4 remaining MUL-family opcodes will follow the
`equiv_MUL` skeleton with the following per-opcode
adjustments:

* **MULHU (op = 0xb1 = 177):** unsigned × unsigned, high 64 bits.
  Needs `arith_table_op_mulhu_mode_pin` (op = 177, sext = 0, m32 = 0,
  div = 0, all sign witnesses 0) + `arith_table_op_mulhu_main_selector_pin`
  (op = 177 ⇒ `main_mul = 0, main_div = 0` — secondary lane, since
  the high-half is emitted via `bus_res1` from the `d[]` chunks). Hi
  lane uses `rem_bus_res1_eq_d_hi` (mirroring DIV's REM secondary).
* **MULH (op = 0xb5 = 181):** signed × signed, high 64 bits. Needs
  mode pin (op = 181 ⇒ sext = 0, m32 = 0, div = 0, na = nb_unspecified,
  np = unspecified), selector pin (secondary lane), AND `na = MSB(A)`
  / `nb = MSB(B)` / `np = ?` MSB pins. Consumed via the signed
  `signed_packed_toInt_eq_of_read_xreg` for r1/r2.
* **MULHSU (op = 0xb3 = 179):** signed × unsigned, high 64 bits.
  Mixed signedness — `na = MSB(A)`, `nb = 0`. May need a bridge-only
  helper combining `signed_packed_toInt_eq_of_read_xreg` (for r1)
  with `packed_lane_eq_of_read_xreg` (for r2).
* **MULW (op = 0xb6 = 182):** 32-bit truncated MUL. `m32 = 1`. Needs
  mode pin + selector pin AND can reuse existing
  operation-bus W high-lane collapse for the upper-chunk zeroing.

Each within-shape wrapper adds 1-3 axioms (mode pin always; selector
pin always; sign-witness MSB pins for the two signed-input variants).
Total predicted MUL family delta: **~6-10 axioms** across all 5
wrappers, all sitting in class #6b alongside the MUL-pilot pair.

### Status — landed at Step 4.2 r3.III (ArithMul-signed family)

All 4 within-shape wrappers landed:

* `equiv_MULHU` (`Compliance/Wrappers/MulHU.lean`) — Step 4.2 r2 Family A.
* `equiv_MULH` (`Compliance/Wrappers/MulH.lean`) — Step 4.2 r3.III.
* `equiv_MULHSU` (`Compliance/Wrappers/MulHSU.lean`) — Step 4.2 r3.III.
* `equiv_MULW` (`Compliance/Wrappers/MulW.lean`) — Step 4.2 r3.III.

Total ArithMul axiom delta across the whole Step 4.2 effort (r2 + r3.III):
* `arith_table_op_mul_mode_pin` + `arith_table_op_mul_main_selector_pin` (r1.8)
* `arith_table_op_mulhu_mode_pin` + `arith_table_op_mulhu_main_selector_pin` (r2)
* `arith_table_op_mulh_mode_pin` + `arith_table_op_mulh_main_selector_pin` (r2)
* `arith_table_op_mulhsu_mode_pin` + `arith_table_op_mulhsu_main_selector_pin` (r2)
* `arith_mul_na_eq_msb_of_a` + `arith_mul_nb_eq_msb_of_b` (r3.III)
* `arith_table_op_mulw_mode_pin` (r3.III)

11 class-#6b axioms across all 5 MUL-family opcodes — slightly above
the predicted upper bound (10) because MULW kept the W-mode mode pin
separate from the existing operand-truncation pin
by operation-bus W high-lane collapse rather than combining them. MULW
exemplar still passes through `h_sext_choice`, `h_op1`, `h_op2` as
W-form caller obligations (mirroring DIVW's exemplar shape); a future
within-shape pass can derive these from the existing W operand pin
plus a signed-low-32 form of `signed_packed_toInt_eq_of_read_xreg`.

---

## ArithDiv (covers 8 opcodes: DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW)

**Validator:** `ZiskFv/Airs/Arith/Div.lean::Valid_ArithDiv`
**Discharge bridges:** `ZiskFv/Equivalence/Bridge/Arith.lean`
(entry points `arith_div_discharge_conservative` and
`arith_div_secondary_discharge_conservative`), plus the
pilot wrapper `ZiskFv/Compliance/Wrappers/Div.lean`.
**Provider-bus axioms:**
* `op_bus_perm_sound_ArithDiv` — `Airs/OperationBus/Bridge.lean:143`
  (primary bus tuple, quotient lane)
* `op_bus_perm_sound_ArithDivSecondary` — `Airs/OperationBus/Bridge.lean:159`
  (companion remainder lane)

### Trust-ledger axioms already in place (DIV-side)

| Axiom | Class | Source | Discharges |
|---|---|---|---|
| `op_bus_perm_sound_ArithDiv` | #4 (op-bus perm) | `Airs/OperationBus/Bridge.lean:143` | DIV-primary cross-AIR matches_entry |
| `op_bus_perm_sound_ArithDivSecondary` | #4 (op-bus perm) | `Airs/OperationBus/Bridge.lean:159` | DIV-secondary cross-AIR matches_entry |
| `arith_div_columns_in_range` | #6b (range-bus) | `Airs/Arith/Ranges.lean:55` | `bits(16)` chunk-range on a/b/c/d (`arith.pil:17-20`) |
| `arith_div_carry_columns_in_range_unsigned` | #6b (range-bus) | `Airs/Arith/Ranges.lean:126` | 7-carry-witness range under unsigned mode |
| `arith_div_carry_columns_in_range_signed` | #6b (range-bus) | `Airs/Arith/Ranges.lean:193` | signed-mode disjunctive carry-range |
| `arith_div_carry_columns_in_range_w` | #6b (range-bus) | `Airs/Arith/Ranges.lean:311` | W-variant carry-range |
| `arith_table_op_div_rem_signed_d_sign_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:237` | for signed DIV/REM rows: `nr = np ∨ d[] = 0` |
| `arith_table_op_div_rem_signed_w_d_sign_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:261` | W-mode analog of the above |
| `arith_table_op_divw_operand_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:352` | W-mode operand-chunk pin for DIVW/REMW/DIVUW/REMUW |
| `arith_table_op_div_rem_signed_mode_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:386` | DIV-pilot GAP-M: `sext=0, m32=0, div=1` for `op ∈ {186, 187}` |
| `arith_table_op_div_rem_main_selector_pin` | #6b (table-pin) | `Airs/Arith/Ranges.lean:427` | DIV-pilot GAP-A hi-lane: `main_div`/`main_mul` selector pin |
| `arith_div_np_eq_msb_of_dividend` | #6b (table-pin) | `Airs/Arith/Ranges.lean:502` | DIV-pilot GAP-B: `np = MSB(C)` |
| `arith_div_nb_eq_msb_of_divisor` | #6b (table-pin) | `Airs/Arith/Ranges.lean:530` | DIV-pilot GAP-B: `nb = MSB(B)` |
| `arith_div_remainder_bound` | #6b (range-bus) | `Airs/Arith/Ranges.lean:602` | DIV-pilot GAP-C: Euclidean remainder magnitude/sign bound (`arith.pil:274`) |
| `ExternalArithMemoryWitness` | structural witness | `Compliance/SharedBundles.lean` | shared with ArithMul — rd-write byte-pack lanes derived from Clean Main `cMemMessage` rather than a trust-ledger axiom |

### Predicted gaps for the AIR's discharge pilot

ArithDiv **is the piloted AIR** as of commit `83532d7`. The DIV
pilot (`Compliance/Wrappers/Div.lean`) closed all five categories for
`equiv_DIV` end-to-end. Remaining items to lift the DIV pilot to
the full 8-opcode DIV/REM family:

* **Lane-match:** Discharged for DIV via `ExternalArithMemoryWitness`
  + `arith_table_op_div_rem_main_selector_pin` + `div_bus_res1_eq_a_hi`.
  Extension to REM (`op = 187`) reuses the same axioms (the selector
  pin covers both `op = 186` and `op = 187`); REM-secondary uses
  the secondary op-bus axiom. **Bridge-only** for DIVU/REMU
  (unsigned analog using `arith_div_carry_columns_in_range_unsigned`).
* **Mode pins:** Discharged for signed 64-bit (`op ∈ {186, 187}`)
  via `arith_table_op_div_rem_signed_mode_pin`. Unsigned-mode and
  W-mode mode pins are **partially predicted**: unsigned-mode pin
  for `op ∈ {184, 185}` (DIVU/REMU) and W-mode pin for `op ∈ {0xba,
  0xbb, 0xbc, 0xbd}` (DIVW/DIVUW/REMW/REMUW). Some of this is
  already covered by `arith_table_op_divw_operand_pin` but a clean
  mode-pin axiom for `(sext, m32, div) = (?, 1, 1)` may be needed.
  Estimate: 1–2 new axioms, class #6b.
* **Sign-witness pins:** Discharged for signed 64-bit DIV/REM via
  the np/nb MSB pins. **Predicted gap** for signed W variants —
  `arith_div_np_eq_msb_of_dividend_w` / analog needed if the W-mode
  signed paths follow the same operand bridge. Estimate: 1–2
  axioms, class #6b.
* **Range/bound:** Discharged for signed 64-bit via
  `arith_div_remainder_bound`. **Predicted gap** for the W-mode
  Euclidean bound (32-bit magnitude). Estimate: 1 new axiom, class
  #6b.
* **Operand bridges:** Discharged for signed 64-bit via
  `signed_packed_toInt_eq_of_read_xreg`. **Bridge-only** for
  unsigned (analogous `unsigned_packed_toNat_eq_of_read_xreg`,
  already in `SailStateBridge.lean`).

### Pilot scope

DIV pilot added 6 axioms across classes 4 and 6b (GAP-A, GAP-B,
GAP-C, GAP-M, GAP-O — 4 class-#6b table/range pins + 2 class-#4
op-bus literal corrections that were existing axioms with
corrected statements, so net new = +6 since branch base).
Extension to the remaining 7 DIV/REM opcodes (DIVU/DIVW/DIVUW/REMU/REMW/REMUW
+ REM via the secondary): expected **~2–4 additional axioms** for
the W-mode and unsigned-mode mode/sign/range parallels. ArithDiv
is the most axiom-heavy of the seven AIRs and will likely remain
so post-discharge.

---

## Mem (covers 8 opcodes: LD, LBU, LHU, LWU, SB, SH, SW, SD — plus LB/LH/LW via the SEXT chain)

The Mem provider is a **three-sub-provider** shape, all reachable
through `Bridge/Mem.lean`:

* **Mem core** (`Valid_Mem`) — aligned width-8 loads / stores.
* **MemAlign** (`Valid_MemAlign`) — sub-doubleword (width 1/2/4)
  read-aligned access for LBU / LHU / LWU.
* **MemAlignByte / MemAlignReadByte** — narrower lookup paths used
  by the MemAlign permutation closure.

**Validator(s):** `ZiskFv/Airs/Mem.lean::Valid_Mem` plus the
MemAlign* validators (not yet extracted as named-column wrappers at
this commit — the AIR-inventory has them in Category B; the
bridge axioms below absorb them).
**Discharge bridge:** `ZiskFv/Equivalence/Bridge/Mem.lean`

### Trust-ledger axioms already in place

#### Mem core (aligned width-8)

| Axiom | Class | Source | Discharges |
|---|---|---|---|
| `lookup_consumer_matches_provider_store` | #4 (memory-bus) | `Airs/MemoryBus/MemBridge.lean:178` | Main-row store consumer (`c_*`) is matched by a Mem-AIR row |
| `main_store_pc_emission_bundle` | #4 (memory-bus) | `Airs/MemoryBus/MemBridge.lean:495` | rd-write entry lanes match `store_pc_lanes_match_{lo,hi}` for `is_external_op = 0`, `op ∈ {OP_FLAG, OP_COPYB}` — consumed by JAL/JALR/AUIPC/LUI |
| `memory_bus_register_write_perm_sound` | #5 (memory-bus perm) | `Airs/MemoryBus/LaneMatch.lean:138` | Main rd-write entry pairs with a "next read" Mem row at same address |
| `memory_bus_register_write_perm_sound_store_pc` | #5 (memory-bus perm) | `Airs/MemoryBus/LaneMatch.lean:329` | `store_pc = 1` variant of the above |
| `memory_bus_entry_byte_range_perm_sound` | #5b (range-bus) | `Airs/MemoryBus/EntryRanges.lean:52` | every memory-bus entry's 8 `x0..x7` byte cells in `[0, 256)` |
| `row_models_sail_state_load` | #2 (mem-state bridge) | `Circuit/MemModel.lean:127` | `wr=0` Mem row → Sail's `state.mem` agrees with the entry's bytes |
| `row_models_sail_state_store` | #3 (mem-state bridge) | `Circuit/MemModel.lean:152` | `wr=1` Mem row → Sail's `state.mem` after store equals chained `insert` form |

#### MemAlign / MemAlignByte / MemAlignReadByte (sub-doubleword loads)

No live trust-ledger axioms remain for the canonical LBU/LHU/LWU
zero-padding route. `MemAlignBridge.SubdoublewordLoadProviderWitness`
structurally unpacks the selected provider row and the ROM-derived
row facts; `memalign_subdoubleword_load_high_bytes_zero` then derives
the high-byte-zero predicate in Lean.

### Predicted gaps for the AIR's discharge pilot

* **Lane-match (Mem core):** Canonical LD/LB/LH/LW/LBU/LHU/LWU and
  SB/SH/SW/SD now use Clean structural witnesses on the PIL-shaped
  memory channel instead of the legacy load/store emission bundle
  axioms. The remaining `main_*_emission_bundle` declarations are
  legacy compatibility surface for non-canonical paths: `store_pc`
  belongs to T6/T7, and `external_arith` belongs to T5.
* **Lane-match (MemAlign sub-doubleword):** Discharged for LBU /
  LHU / LWU via the structural provider witness plus the derived
  theorem `memalign_subdoubleword_load_high_bytes_zero` (in
  `MemAlignBridge.lean`, pure Lean derivation).
* **Mode pins:** N/A for Mem core in the usual sense (no
  multi-mode rows). MemAlign's sub-doubleword width/value pins now
  live in the structural provider witness instead of the trust ledger.
* **Sign-witness pins:** N/A for Mem. Signed-load sign-extension
  is handled by BinaryExtension (via the SEXT chain in
  `Circuit/SextLoadBridge.lean`), not by Mem itself.
* **Range/bound:** Discharged via `memory_bus_entry_byte_range_perm_sound`.
* **Operand bridges:** Loads' read-address bridge and stores'
  store-value bridge are discharged via pure-Lean derivations atop
  the emission bundles + transpile axioms.

### Constructibility note (Mem is special)

Mem's discharge pilot — once the MemAlign* named-column wrappers
are stood up — will likely **not need new trust-ledger axioms**.
The axiom surface is the heaviest of any AIR (13 axioms) but the
infrastructure is already in place. The next step for Mem is a
**constructibility audit** (see CLAUDE.md's anti-laundering
principle item 4): confirming each Mem / MemAlign* axiom's
hypotheses are derivable from a real ZisK trace, NOT silently
overstrong. This is a separate concern from "more axioms needed."

### Pilot scope

Expected for Mem (full pilot): **0–2 new axioms**, primarily for
MemAlign* mode-pin closure if the named-column wrappers reveal
gaps. Smallest projected delta of the seven AIRs — Mem was the
first AIR to receive comprehensive axiom coverage (the
load-output-eq-closure work in `docs/fv/plans/`) and its pilot is
largely a packaging exercise atop existing axioms.

### Actual delta (Step 4.1.3 — SD exemplar, retired in T4)

`main_store_emission_bundle_sd` was removed from the trust ledger
during T4. The canonical `equiv_SD` wrapper now carries a structural
Clean `SdCleanWitness` tying the selected Main row to the PIL-shaped
c-side memory interaction, and the proved Clean adapter derives the
ptr-match plus 8 byte equalities. This is recorded as structural
unpacking for SD rather than an active class-#4 trust-ledger axiom.

### Actual delta (Step 4.2.r3.IV — SB/SH/SW narrow-store wrappers)

**3 new axioms** added: `main_store_emission_bundle_{sb,sh,sw}`
(class #4, `MemBridge.lean:768/804/832`). The narrow stores follow
the same architectural pattern as SD: Main emits the same memory-bus
entry shape (`as = 2`, `mult = 1`, 8 byte cells) but only the low
`N ∈ {1, 2, 4}` byte lanes carry the store-value bytes; the high
`8 - N` lanes are restored from the **pre-existing memory contents**
by the MemAlign* RMW protocol (`mem_align.pil:28-37` and `:50-61`).

Each axiom produces:
1. **Ptr-match.** `e_st.ptr.toNat = (r1_val + signExt(imm)).toNat`.
2. **Low-byte extracts.** `(e_st.x_i : BitVec 8) = BitVec.extractLsb _ _ r2_val`
   for `i ∈ [0, N)`.
3. **High-byte RMW preservations.** `state.mem[e_st.ptr.toNat + i]?
   = some (e_st.x_i : BitVec 8)` for `i ∈ [N, 8)`.

The canonical `equiv_SB / SH / SW` theorems carry a single bundled
`h_mem_eq` hypothesis equating the bus side's 8-insert chain on
`state.mem` with the Sail spec's `N`-insert chain (via
`modify_memory_{1,2,4}`). The `Bridge.Mem.{sb,sh,sw}_discharge_full`
helpers derive `h_mem_eq` from the new axiom + `transpile_{SB,SH,SW}` +
a pure-Lean `Std.ExtHashMap.ext_getElem?` closure: each trailing
insert at `ptr + i` (`i ≥ N`) is a no-op because (3) says memory
already contains the inserted value at that key.

**Design choice rationale.** The user-specified options were:
* (a) New class-#4 axioms encoding the RMW protocol directly. ✅ CHOSEN.
* (b) Pure-Lean composition with an existing memory-bus
  permutation-soundness fact + at most one new class-#5 axiom.

Option (b) is not feasible without 3 new axioms anyway: SD's
full-width Clean path proves byte-extract equalities for **all 8
bytes** under `ind_width = 8`; for SB/SH/SW only the low `N` byte
extracts are valid, and the high `8 - N` lanes follow a different
(RMW) protocol that must be represented separately. The cleanest
factoring is one narrow-width axiom per width, mirroring the
full-width store shape on the low side and adding the RMW clause on
the high side. All three axioms fit class #4 with the same PIL
citation surface plus the MemAlign write-protocol citations.

Matches the upper half of the original Mem-shape 0-2 prediction
(prediction was for the full pilot; this wraps up the
narrow-stores sub-shape of the Mem family).

### Actual delta (Step 4.1.6 — LD exemplar, Mem-loads shape)

**Zero new axioms.** The Mem-loads load-side discharge was already
fully covered before this pilot:

* `main_load_emission_bundle` (class #4, `MemBridge.lean:374`)
  delivers the seven-tuple `(h_main_emit_b, h_main_emit_c,
  h_ptr_match, h_rd_zero_iff, h_rd_idx, h_copy0, h_copy1)` from
  `Bridge.Mem.ld_discharge_full` (and its `lbu_/lhu_/lwu_`
  synonyms) — already consumed inside `equiv_LD`'s proof body.
* `memory_bus_entry_byte_range_perm_sound` (class #5b) and
  `lookup_consumer_matches_provider_load` (class #4) are likewise
  consumed transitively via `equiv_LD`'s
  `ZiskFv.ZiskCircuit.LoadDerivation.load_copyb_e1_e2_bytes_eq_bv` and
  `Circuit.MemModel.mem_load_correct` chains.
* `transpile_LD` (class #1) feeds the routing-pin derivations
  inside the canonical theorem.

The `equiv_LD` wrapper at
`ZiskFv/Compliance/Wrappers/Ld.lean` therefore consumes
no per-AIR trust-ledger axiom beyond `equiv_LD`'s existing closure.
The reduction in caller burden is small (−1 binder, 0 hypothesis
delta) and is principally **canonical-naming**: `h_op : main.op
r_main = (1 : FGL)` becomes `h_main_op_ld : main.op r_main =
OP_COPYB`, aligning with the Compliance-handshake convention used
by the SD / LUI / ADD / OR / SLL exemplars. The shape's narrower
zero-extended opcodes (LBU / LHU / LWU) generalize from LD
mechanically — the canonical-naming pattern carries over verbatim,
and the high-byte-zero pin is closed by the pre-existing pure-Lean
derivation `memalign_subdoubleword_load_high_bytes_zero`.

Matches the lower endpoint of the 0-2 prediction range (jointly
with LUI, ADD, and SLL among prior pilots that needed zero new
axioms).

---

## ControlFlow (covers 11 opcodes: AUIPC, BEQ, BGE, BGEU, BLT, BLTU, BNE, FENCE, JAL, JALR, LUI)

ControlFlow is **not a provider AIR** in the same sense as the
others — there is no `Valid_ControlFlow` (and no corresponding
PIL AIR). These opcodes are **Main-only** — they consume from the
Main AIR + the memory-bus (for rd-write on JAL/JALR/AUIPC/LUI),
but not from a separate arithmetic provider AIR. The
`Bridge/ControlFlow.lean` file packages these Main-only proofs.

### Sub-shapes

ControlFlow splits into three sub-shapes:

1. **Branches** (`BEQ`, `BNE`, `BLT`, `BLTU`, `BGE`, `BGEU`,
   `FENCE`) — no register write. Only the PC update matters.
2. **U-type** (`AUIPC`, `LUI`) — rd-write of a PC-relative or
   immediate constant.
3. **Jumps** (`JAL`, `JALR`) — rd-write of return-address (PC + 4),
   PC update to target.

### Trust-ledger axioms already in place

ControlFlow has **no AIR-specific axioms**. It consumes:

| Axiom | Class | Source | When |
|---|---|---|---|
| `transpile_AUIPC`, `transpile_BEQ`, `transpile_BNE`, `transpile_JAL`, `transpile_JALR`, `transpile_FENCE`, `transpile_BLT`, `transpile_BGE`, `transpile_BLTU`, `transpile_BGEU`, `transpile_LUI` | #1 (transpile) | `Fundamentals/Transpiler.lean` | every opcode in the shape — Main column ↔ Sail-decoded `ast` |
| `transpile_PC_for_JAL`, `transpile_PC_for_JALR`, `transpile_PC_for_AUIPC` | #1 (transpile) | `Fundamentals/Transpiler.lean:2719,2741,2770` | the PC-update half (separate axiom from the operand half) |
| `main_columns_in_range` | #5b (range-bus) | `Airs/Main/Ranges.lean:67` | `bits(N)`-annotated Main column ranges |
| `main_store_pc_emission_bundle` | #4 (memory-bus) | `Airs/MemoryBus/MemBridge.lean:495` | JAL/JALR/AUIPC/LUI rd-write entry lane equalities (`store_pc=0` or `store_pc=1` per op) |
| `memory_bus_register_write_perm_sound{,_store_pc}` | #5 (memory-bus perm) | `Airs/MemoryBus/LaneMatch.lean:138,329` | rd-write entry pairs with Mem row (consumed by JAL/JALR/AUIPC/LUI) |
| `memory_bus_entry_byte_range_perm_sound` | #5b (range-bus) | `Airs/MemoryBus/EntryRanges.lean:52` | register-write entry byte ranges (consumed by AUIPC, JAL) |

### Predicted gaps for the AIR's discharge pilot

* **Lane-match:**
  * Branches: **Bridge-only.** No cross-AIR match — branches are
    pure Main. The `r1_val` / `r2_val` packed-lane forms used by
    BLT / BLTU / BGE / BGEU come from `Bridge/SailStateBridge.lean`
    + transpile axioms; pure Lean.
  * U-type: Discharged via `main_store_pc_emission_bundle`
    (`store_pc = 0` specialization for LUI; `store_pc = 1` for
    AUIPC).
  * Jumps: Discharged via `main_store_pc_emission_bundle` +
    transpile PC axioms.
* **Mode pins:** N/A — these opcodes do not flow through a
  provider AIR with mode columns.
* **Sign-witness pins:** **Bridge-only.** BLT / BGE require signed
  comparison; the sign of `r1_val.toInt - r2_val.toInt` is
  computed in pure Lean from the packed-nat lift.
* **Range/bound:** Discharged via `main_columns_in_range` +
  `memory_bus_entry_byte_range_perm_sound`.
* **Operand bridges:** Discharged via `Bridge/SailStateBridge.lean`
  per opcode.

### Pilot scope

Expected for ControlFlow: **0 new axioms.** ControlFlow is the
**only AIR with no AIR-specific axioms today** — it relies entirely
on the transpile contracts (#1), main range (#5b), and memory-bus
infrastructure (#4, #5, #5b) for rd-write. The pilot is a
packaging exercise to demonstrate that the 11 ControlFlow opcodes'
existing `equiv_<OP>` theorems can be lifted to a single
`Compliance/ControlFlowPilot.lean` wrapper consuming only existing
axioms. If new axioms surface during the pilot, the most likely
candidates are constructibility-driven (a missing `transpile_*`
contract for an edge case) — class #1. **Smallest predicted axiom
delta of the seven AIRs.**

### Pilot status (Step 4.1.1 — non-branch LUI exemplar)

**Actual: 0 new axioms** for the LUI non-branch exemplar
(`ZiskFv/Compliance/Wrappers/Lui.lean`,
`equiv_LUI`). Matches the prediction above.

Composition: `transpile_LUI` (class #1) + `equiv_LUI`'s existing
transitive closure (`main_store_pc_emission_bundle` class #4,
`memory_bus_entry_byte_range_perm_sound` class #5b,
`main_columns_in_range` class #5b). No category 1–5 work surfaced
a new axiom: lane-match, range/bound, and the lone (Main-side)
mode pins (`m32 = 0`, `set_pc = 0`, `store_pc = 0`) are all already
internalized by `equiv_LUI`. The wrapper unpacks `h_circuit` into
`(h_main_active, h_main_op_lui, h_lui_subset)` — a
structural-unpacking pattern consuming only `transpile_LUI`.

Caller-burden (per discharge-recipe.md): 22 binders / 13 hypotheses
on `equiv_LUI` vs. 22 / 12 on `equiv_LUI`. Per-opcode
hypothesis count grows by 1 because `h_circuit` is a structural
bundle (`lui_subset_holds` + `main_row_in_lui_mode`, 12 sub-claims)
that unpacks into three Compliance-friendly ingredients. The
removed `h_nextPC_eq` / `nextPC_val` (made `rfl` by setting
`nextPC_val := lui_input.PC + 4#64`) offsets two added binders;
the third is the net growth. At the global `Compliance.lean` level
this nets to a reduction because `(m, ∀ r, lui_universal_row m r)`
collapses into shared parameters across all eleven ControlFlow
opcodes plus the Main-only opcodes.

Cross-shape lessons:
* **No new bridge added** to `Equivalence/Bridge/SailStateBridge.lean`.
  LUI has no `read_xreg` — operand-bridge category 5 is N/A.
* The discharge generalizes to AUIPC / JAL / JALR mechanically:
  swap `transpile_LUI` for `transpile_AUIPC` / `transpile_JAL` /
  `transpile_JALR`, swap `lui_subset_holds` for the corresponding
  AUIPC / JAL / JALR subset, swap `lui_archetype_circuit_holds`
  for the corresponding `*_archetype_circuit_holds`. Mass-author
  the four UTYPE/jump wrappers in Step 4.2.

Remaining ControlFlow work: the seven branch opcodes
(`BEQ`, `BNE`, `BLT`, `BLTU`, `BGE`, `BGEU`, `FENCE`) are a
**different shape** (no rd-write, only PC update) and need a
separate exemplar. Predicted: still 0 new axioms — the branch
shape is also Main-only and consumes transpile contracts (#1)
plus `main_columns_in_range` (#5b) only.

### Pilot status (Step 4.1.7 — branches BEQ exemplar)

**Actual: 0 new axioms** for the BEQ branch exemplar
(`ZiskFv/Compliance/Wrappers/Beq.lean`,
`equiv_BEQ`). Matches the prediction (0 new axioms).

Composition: `equiv_BEQ`'s existing transitive closure (which for
the branch sub-shape comprises `transpile_BEQ` (class #1), Sail
auxiliaries (`writeReg`/`readReg`/`jump_to_equiv`), and the
bus-emission shape lemma `bus_effect_matches_sail_beq`) plus a
pure-Lean misalignment derivation local to this file. No category
1–5 work surfaced a new axiom:

* **Lane-match (category 1)** N/A on the provider side. The
  Binary-AIR flag-correctness fact (`m.flag = 1 ↔ r1_val = r2_val`,
  consumed by a future `h_nextPC_matches` discharge) is NOT
  exercised by this exemplar — `h_nextPC_matches` passes through
  as a structural bus pin. The flag-correctness bridge belongs to
  a separate `Bridge/ControlFlow.lean` extension consuming
  `op_bus_perm_sound_Binary` (class #4) + `bin_table_consumer_wf`
  (class #6, `wf_EQ` clause) and is deferred.
* **Mode pins (category 2)** N/A on the provider side. Main-side
  mode pins are not directly consumed by `equiv_BEQ`'s Sail-pivot
  proof.
* **Sign-witness pins (category 3)** N/A — equality is sign-agnostic.
* **Range/bound (category 4)** N/A — BEQ writes no register and
  consumes no byte-level Mem entries.
* **Operand bridges (category 5)** N/A at the wrapper level —
  `equiv_BEQ` consumes raw Sail `read_xreg` facts directly; the
  comparison is `BitVec` equality not lane chunks.

The actual discharge target on BEQ is the pair of Sail-pure-spec
exception promises `h_not_throws` and `h_success`. Reading
`PureSpec.execute_BEQ_pure`, both depend on bits 0 and 1 of the
branch target `input.PC + signExt 64 input.imm`. The wrapper
introduces a **single SPEC-PRE alignment hypothesis**
`h_target_aligned : (input.PC + signExt 64 input.imm).toNat % 4 = 0`
(a ZisK assembler/transpiler invariant — RV64I requires branch
targets to be 4-byte-aligned per RISC-V ISA Manual §2.5) and
derives both promises via the pure-Lean lemma
`beq_pure_no_exception_of_aligned`.

Caller-burden (per discharge-recipe.md): 18 binders / 10 hypotheses
on `equiv_BEQ` vs. 19 / 11 on `equiv_BEQ`. **Net −1
binder / −1 hypothesis.** Cleaner than LUI's +1 structural-unpacking
growth — branches need no compensating bundle unpack because there
is no rd-write entry (no `e_rd` byte ranges, no `register_write_lanes_match`).

Cross-shape lessons:
* **No new bridge added** to `Equivalence/Bridge/ControlFlow.lean`
  or `Equivalence/Bridge/SailStateBridge.lean`. The misalignment
  derivation is a 12-line `BitVec.toNat` argument local to the
  exemplar file.
* The discharge generalizes mechanically to the other branches
  (BNE / BLT / BGE / BLTU / BGEU). Every branch's pure spec uses
  the same `throws := !skip && bit0`, `fails := throws || (!skip && bit1)`
  shape parameterized on the per-opcode comparison output; the
  alignment lemma is opcode-agnostic. The within-shape wrappers
  swap `execute_BEQ_pure` for the per-opcode pure spec and reuse
  the same single-hypothesis alignment discharge.
* **Signed branches BLT / BGE** additionally need sign-witness
  pins **only if** the within-shape exemplar discharges
  `h_nextPC_matches` (which BEQ does not). Following BEQ's
  alignment-only pattern, BLT / BGE / BLTU / BGEU also need only
  the alignment hypothesis.
* `FENCE` is structurally distinct (no branch target, no PC
  jump) — see its current `equiv_FENCE` for the trivial Main-only
  proof; no Compliance wrapper required.

The trust-ledger size stays unchanged after the BEQ exemplar —
confirming that ControlFlow branches is the cleanest sub-shape
within ControlFlow (and one of the cleanest across the seven
AIRs) and that the per-AIR axiom map's 0-new-axioms prediction
was correct.

---

## Summary: per-AIR axiom counts and predicted deltas

| AIR | Existing AIR-specific axioms | DIV-pilot template categories needing axioms | Predicted new axioms |
|---|---|---|---|
| BinaryAdd | 2 | none | 0–1 |
| Binary | 5 | mode pins (1–2), sign-witness pins (1–2) | 2–4 |
| BinaryExtension | 5 | sign-witness pins (1), possibly W mode pin (1) | 1–2 |
| ArithMul | 6 (shares 11 of 17 with ArithDiv) | mode pin (1), sign pins (1–2), selector pin (1) | 3–5 |
| ArithDiv (piloted) | 14 | W/unsigned extensions (mode + sign + range) | 2–4 (lift from DIV → 8 DIV/REM ops) |
| Mem | 13 | constructibility-driven only | 0–2 |
| ControlFlow | 0 (consumes #1, #4, #5, #5b) | none — Main-only shape | 0 |
| **Total predicted** | **45** (excluding cross-cutting) | | **~8–18 new axioms** across remaining 6 pilots |

Cross-cutting axioms NOT in the per-AIR tally above:

* 66 transpile contracts (class #1)
* 4 platform-feature axioms (classes #7–#10)
* 1 `main_columns_in_range` (class #5b)
* 6 op-bus permutation-soundness axioms (one per provider in
  class #4)

Grand total at this snapshot: **116 axioms** (matches
`trust/baseline-axioms.txt`).

### Where the surprise might come

* **ArithMul** is the largest predicted delta — its pilot has to
  re-do for MUL/MULH/MULHU/MULHSU/MULW most of what the DIV pilot
  did for DIV/REM. Worth scoping carefully: 3–5 axioms is the
  median estimate; the upper end (~5) lands if MULHSU's mixed-sign
  operand bridge needs its own table-lookup pin.
* **Binary** is wider in opcode coverage (14 ops) but most of the
  per-op work is bridge-only after the mode-pin axiom lands. The
  carry-7-zero AND/OR/XOR derivation is already in place
  (`Bridge.Binary.carry_7_zero_*_pure`), which is the trickiest
  part.
* **ControlFlow** at zero new axioms is the most striking — but
  validate with the pilot. If a JALR misaligned-target edge case
  surfaces, a class-#1 transpile addendum could be needed.
* **Mem** at 0–2 is contingent on the MemAlign* named-column
  wrappers being clean. If extraction reveals gaps in MemAlignByte
  / MemAlignReadByte, this could grow.

### Flagged for review

* **`ExternalArithMemoryWitness`** straddles ArithMul and ArithDiv.
  T5 retired the prior `main_external_arith_emission_bundle` source
  axiom; the PIL citation (`main.pil:311-312`) is now carried by the
  Clean Main structural witness and adapter proof.
* **The op-bus axioms** are listed under each AIR's "provider-bus
  axiom" header but counted only once in the totals
  (`Airs/OperationBus/Bridge.lean` has 6 axioms total, one per
  provider AIR). Total of 6 is consistent with the trust-ledger
  snapshot.
* **No axioms are currently uncategorizable** — every axiom in
  `trust/baseline-axioms.txt` fits cleanly into one AIR's section
  or one of the cross-cutting categories above.
