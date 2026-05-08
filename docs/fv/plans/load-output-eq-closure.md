# Plan — Close every unproven hypothesis in the 7 load equivalence proofs

## Context

The canonical claim of this project is, for each RV64IM opcode,

```
equiv_<OP> : Sail.execute … state = (bus_effect …).2
```

For 56 of 63 ops, this typechecks against circuit witnesses + the 82 trusted axioms with no unproven hypothesis carrying spec content. The 7 loads (LB, LH, LW, LBU, LHU, LWU, LD) currently accept hypotheses that *do* carry spec content:

- Cross-entry rd-value (the OUTPUT-EQ class): `h_high_bytes_signext` / `h_high_bytes_zeroext` / `h_e1_e2_bytes` — say the rd-write entry `e2`'s bytes are the appropriate (sign- / zero-) extension or passthrough of the read entry `e1`'s bytes.
- Single-entry zero-padding (LBU / LHU / LWU only): `memory_entry_high_bytes_zero_*` — say the unused high bytes of `e1` are zero.

These are insulated from the trust gate by two layers:
1. `EXEMPT_STEMS = {"Lb","Lh","LoadBU","LoadD","LoadHU","LoadWU","Lw"}` in `trust/scripts/check-no-output-eq.py:38`.
2. Their hypothesis names (`h_high_bytes_*ext`, `h_e1_e2_bytes`, `memory_entry_high_bytes_zero_*`) are absent from `trust/forbidden-param-shapes.txt` — even without the exemption, the regex would not catch them.

**Outcome wanted:** every load proof derives every property of `e1`/`e2` from circuit witnesses + existing or new axioms; both insulating layers are removed; the trust gate uniformly polices all 63 opcodes; CLAUDE.md's status line drops the "7 loads remain on a follow-up" carve-out.

## Design

Three independent derivation gaps, three corresponding lemma families. Strict TCB-additions cap: at most +2 axioms, both in existing classes.

### Gap A — copyb byte passthrough (LD, LBU, LHU, LWU)

ZisK lowers all four to `copyb` (`OP_COPYB = 1`, internal). Main constraints 8 and 14 (`build/extraction/Extraction/Main.lean:67-79`) are F-typed: `((1 - is_external_op) * op) * (b[i] - c[i]) = 0` for `i ∈ {0,1}`. Combined with the named-column emission predicates, this gives `lo e1 = lo e2 ∧ hi e1 = hi e2` directly.

To lift `(lo, hi)` equality to per-byte equality, use the byte ranges from the Mem AIR rows produced by `lookup_consumer_matches_provider_{load,store}` and the standard base-256 unique-decomposition argument.

**Net:** 0 new axioms. Pure Lean derivation.

### Gap B — sign-extension via BinaryExtension AIR (LB, LH, LW)

ZisK lowers these to `signextend_{b,h,w}` (`OpType::BinaryE`, `is_external_op = 1`); `c_0/c_1` are produced by the BinaryExtension AIR over the operation bus (`bus_id = 5000`). The BinaryExtension AIR holds 0 F-typed constraints; semantics live in the `bin_ext_table_consumer_wf` axiom's `wf_properties` — but `wf_properties` currently lacks `wf_SEXT_B/H/W` clauses (the upstream PIL `binary_extension_table.pil:149-189` defines them; the Lean port doesn't expose them).

**Net:** 0 new axioms — extend the existing `wf_properties` predicate. The axiom's source-text hash changes, surfaces in the `trust/baseline-axioms.txt` diff, and gets CODEOWNER-acked. +1 axiom only if a missing op-bus matches-provider axiom turns out not to exist (verify in step B-0); cap held at +1.

### Gap C — MemAlign zero-padding (LBU, LHU, LWU only)

For sub-doubleword unsigned loads, ZisK's MemAlign state machine produces a memory-bus entry `e1` whose high bytes (above the loaded width) are zero. This is enforced by MemAlign's PIL constraints + a permutation argument tying MemAlign's output to the memory bus.

The Lean side has named-column wrappers `ZiskFv/Airs/MemAlign*.lean` for the four MemAlign AIRs (verify scope in step C-0). What's missing is the bus-side closure: from "this `e1` came through MemAlign with width `n`" to "`e1.x_n .. e1.x_7` are zero".

**Net:** at most +1 axiom in trust class #4 (memory-bus lookup soundness, extended to the MemAlign sub-bus) if MemAlign uses a distinct bus from the main memory bus. Possibly 0 if existing axioms already cover it.

**Combined TCB delta cap: +2 axioms.** If the actual cost exceeds this, stop and re-confer with the user before proceeding.

## Step-by-step

### Step 0 — Confirm investigation findings before writing any code

Three quick Bash greps + reads to lock down whether the predicted axiom budget holds:

```
grep -rn "axiom.*op_bus\|matches_entry.*op_bus\|opBus.*matches_entry" \
  ZiskFv/Airs/ ZiskFv/Fundamentals/
grep -rn "axiom" ZiskFv/Airs/MemAlign*.lean
ls ZiskFv/Airs/ | grep -i memalign
```

Confirms whether step B's op-bus matches-provider and step C's MemAlign bus axiom already exist or need to be added.

### Step 1 — Gap A derivation (LD, LBU, LHU, LWU)

**New file:** `ZiskFv/Circuit/LoadDerivation.lean`. Imports: `ZiskFv.Airs.Main`, `ZiskFv.Airs.Mem`, `ZiskFv.Airs.MemoryBus`, `ZiskFv.Airs.MemoryBus.MemBridge`, `ZiskFv.Circuit.MemModel`.

Three lemmas:

- `entry_bytes_eq_of_lo_hi_eq` — pure base-256 algebra. From `lo e1 = lo e2`, `hi e1 = hi e2`, and per-byte ranges (`x_i.val < 256` for both entries), conclude per-byte equality. Mirrors the technique already implicit in `MemBridge.lean::entry_packs_mem_row_value`.
- `load_copyb_e1_e2_bytes_eq` — chains `lookup_consumer_matches_provider_load` (for `e1` byte ranges via the Mem AIR row), `lookup_consumer_matches_provider_store` (for `e2`), the named-column constraint-8/14 wrappers (`internal_op1_copies_b0` / `_b1`, already used by `ZiskFv/Circuit/LoadD.lean:121-124`), and the previous lemma. Output: 8 `e2.x_i = e1.x_i` equalities.
- `load_copyb_rd_value_eq_read` (LD-shape) and `load_copyb_rd_value_*_extended` (LBU/LHU/LWU-shapes, consume `memory_entry_high_bytes_zero_*` from step 3).

### Step 2 — Gap B derivation (LB, LH, LW)

**Step B-0:** Verify op-bus matches-provider availability (grep from step 0). If absent, add a single axiom in `ZiskFv/Airs/OperationBus/Bridge.lean` (new file; add to `trust/allowed-axiom-files.txt`) under trust class #4. Document in `docs/fv/trusted-base.md`.

**Step B-1: extend `bin_ext_table_consumer_wf`'s `wf_properties`** in `ZiskFv/Airs/BinaryExtensionTable.lean`. Add `wf_SEXT_B`, `wf_SEXT_H`, `wf_SEXT_W` clauses mirroring `binary_extension_table.pil:149-189`. The axiom's source text expands; baseline hash diff is the audit trail.

**Step B-2: packed-correctness theorems** in `ZiskFv/Airs/Binary/BinaryExtensionPackedCorrect.lean`. Three new theorems `binary_extension_sext_{b,h,w}_chunks_eq_bv_signExtend` mirroring the existing 6 shift-direction theorems. No new axioms.

**Step B-3: bus-side closure** in `ZiskFv/Tactics/SignExtendLoadArchetype.lean`. Three new theorems `sign_extend_load_archetype_c_packed_{b,h,w}` consuming the archetype hypothesis + B-2 to give `main_c_packed = signExtend 64 (low bytes)`.

**Step B-4: derivation lemma** `load_signextend_rd_value_signExtended` in `LoadDerivation.lean`. Combines B-3 with `h_main_emit_c` and Gap A's byte-decomp algebra to deliver the LB/LH/LW shape directly.

### Step 3 — Gap C derivation (LBU, LHU, LWU)

**Step C-0:** Inventory MemAlign Lean files (from step 0). Identify which AIR is responsible for sub-doubleword load width selection (likely `MemAlignReadByte`). Read its named-column wrapper.

**Step C-1:** Add a derivation theorem `memalign_high_bytes_zero_<width>` in `ZiskFv/Airs/MemAlign/HighBytesZero.lean` (new file). For each width `n ∈ {1,2,4}`: given the Main row's load-width selector + the bus emission shape, conclude `e1.x_n = 0 ∧ ... ∧ e1.x_7 = 0`. Proof consumes MemAlign constraint(s) + the memory-bus matches-provider axiom (or a new MemAlign-bus matches-provider axiom — verify in C-0). +1 axiom maximum.

**Step C-2:** Update `LoadDerivation.lean::load_copyb_rd_value_*_extended` to take `Valid_MemAlign*` + `r_memalign` parameters and call C-1 internally instead of accepting `memory_entry_high_bytes_zero_*` as a hypothesis.

### Step 4 — Per-equivalence file rewrite (all 7 files)

For each of `ZiskFv/Equivalence/{Lb,Lh,Lw,LoadBU,LoadHU,LoadWU,LoadD}.lean`:

- **Drop:** `h_high_bytes_signext` (LB/LH/LW), `h_high_bytes_zeroext` (LBU/LHU/LWU), `h_e1_e2_bytes` (LD), `memory_entry_high_bytes_zero_*` (LBU/LHU/LWU).
- **Add:** `h_main_emit_c` (`c_0/c_1` packing predicate, mirrors existing `h_main_emit_b`); for LB/LH/LW: a `Valid_BinaryExtension` row + `r_be` + op-bus match; for LBU/LHU/LWU: a `Valid_MemAlign*` row + `r_memalign` + width-selector emission.
- **Proof body:** replace the manual `h_rd_val_derived := by rw [h_high_bytes_*, ...]` block with a single call to the appropriate `LoadDerivation.lean` lemma. The downstream `bus_effect_matches_sail_load_*byte_rrrw` reduction, the `dif_pos`/`dif_neg` rd-zero split, and the `h_idx_eq` Subtype rewrite are unchanged.

### Step 5 — Trust gate hardening

- `trust/scripts/check-no-output-eq.py`: delete `EXEMPT_STEMS` block (lines 32–38) and the `if f.stem in EXEMPT_STEMS: continue` skip (~line 117).
- `trust/forbidden-param-shapes.txt`: append three patterns (defense-in-depth — these names are gone after step 4, but the gate now actively forbids reintroducing them):
  ```
  \(h_high_bytes_signext\s*:
  \(h_high_bytes_zeroext\s*:
  \(h_e1_e2_bytes\s*:
  ```
- `trust/scripts/check-floor.sh`: bump `MIN_CANONICAL` from 56 to 63.
- `CLAUDE.md`: status line — drop "56 of the 63 canonical … OUTPUT-EQ-free" → "all 63 canonical equiv_<OP> theorems are OUTPUT-EQ-free"; remove the "The 7 loads remain on a follow-up" sentence; bump axiom count if step B-0 / C-0 added one.
- `trust/README.md`: search/remove any "7 loads exempt" / "EXEMPT_STEMS" mention.
- `docs/fv/trusted-base.md`: update class #9 entry (BinaryExtension lookup) to note `wf_properties` now covers SEXT_B/H/W; add per-class entry if axiom was added in step B-0 or C-0; add a one-line ledger note that the load gap is closed.

### Step 6 — Verification

Order matters — earlier failures invalidate later ones.

```
nix develop --command bash trust/scripts/regenerate.sh    # if any axiom touched
git diff trust/baseline-axioms.txt                         # AUDIT — every line
nix develop --command lake build                           # the FV claim
nix develop --command bash trust/scripts/check-all.sh      # gate, seconds
nix run .#test                                             # full suite
```

Each must pass. Specifically:
- `lake build` succeeds (this *is* the FV claim).
- `check-no-output-eq.sh` passes with `EXEMPT_STEMS` removed and the new patterns active.
- `check-floor.sh` passes with `MIN_CANONICAL = 63`.
- `check-uniformity.sh` reports 63 opcodes.
- `check-baseline.sh` matches `baseline-axioms.txt` post-regenerate.
- `baseline-axioms.txt` diff shows only: `bin_ext_table_consumer_wf` hash updated; at most two new entries (steps B-0 and C-0 if needed).

## Critical files

- **New:** `ZiskFv/Circuit/LoadDerivation.lean` (Gaps A, B, C derivation lemmas).
- **New (conditional):** `ZiskFv/Airs/OperationBus/Bridge.lean` (B-0, only if axiom missing).
- **New (conditional):** `ZiskFv/Airs/MemAlign/HighBytesZero.lean` (C-1, +1 axiom max).
- **Modified — axioms:** `ZiskFv/Airs/BinaryExtensionTable.lean` (extend `wf_properties`).
- **Modified — Lean theorems:** `ZiskFv/Airs/Binary/BinaryExtensionPackedCorrect.lean`, `ZiskFv/Tactics/SignExtendLoadArchetype.lean`.
- **Modified — equivalence files (7):** `ZiskFv/Equivalence/{Lb,Lh,Lw,LoadBU,LoadHU,LoadWU,LoadD}.lean`.
- **Modified — trust gate:** `trust/scripts/check-no-output-eq.py`, `trust/forbidden-param-shapes.txt`, `trust/scripts/check-floor.sh`.
- **Modified — docs:** `CLAUDE.md`, `trust/README.md`, `docs/fv/trusted-base.md`.

## Reusable existing infrastructure

- `lookup_consumer_matches_provider_{load,store}` (`ZiskFv/Airs/MemoryBus/MemBridge.lean:134,150`) — Main bus emission ⇒ Mem AIR row + byte ranges.
- `mem_load_correct{,_1byte,_2byte,_4byte}` (`ZiskFv/Circuit/MemModel.lean:203,290,307,320`) — byte-level state agreement on the read side.
- `internal_op1_copies_b0` / `_b1` (already consumed by `ZiskFv/Circuit/LoadD.lean:121-124`) — F-typed constraint 8/14 wrappers.
- `Valid_Main`, `Valid_Mem`, `Valid_BinaryExtension`, `Valid_MemAlign*` — named-column wrappers for the relevant AIRs.
- `SignExtendLoadArchetype`, `LoadArchetype` (`ZiskFv/Tactics/`) — existing tactic infra for load Main-row archetypes.
- `BinaryExtensionPackedCorrect` — pattern for `chunks_eq_bv_<op>` packed-correctness proofs (mirror it for SEXT).

## Out of scope (explicitly)

- V2 type-based parameter check (Lake exe walking elaborated types). The user's intent is met without it once the OUTPUT-EQ-class names are gone from the canonical theorems and forbidden by name. V2 remains future work; mention in `trust/README.md`.
- Stores. They have analogous structural hypotheses but those *are* legitimate (caller-provided value-extraction facts pinning Sail operands to bus bytes), not OUTPUT-EQ class. Out of scope.
