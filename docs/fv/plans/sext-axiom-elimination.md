# Plan — eliminate `signextend_load_c_packed`

## Status

- **Step 1 (DONE, commit `77eeca8`):** `wf_properties` in
  `ZiskFv/Airs/Tables/BinaryExtensionTable.lean` extended with `wf_SEXT_B`,
  `wf_SEXT_H`, `wf_SEXT_W` mirroring
  `binary_extension_table.pil:149-189`. The `bin_ext_table_consumer_wf`
  axiom statement strengthens automatically.
- **Step 2 (DONE, commit `8734206`):** Three packed-correctness
  theorems proven in
  `ZiskFv/Airs/Binary/BinaryExtensionPackedCorrect.lean`:
  `binary_extension_sext_{b,h,w}_chunks_eq_signextend_nat`. Each
  composes 8 per-byte equations into a Nat identity for the packed
  c-output.
- **Step 3 (DONE):** `Circuit/SextLoadBridge.lean` provides
  `load_{byte,half,word}_c_packed`; LB/LH/LW refactored to consume
  them with the BinaryExtension AIR connection witnesses.
- **Step 4 (DONE):** `axiom signextend_load_c_packed` deleted from
  `Airs/BinaryExtensionTable.lean`; baseline shrinks 84→83;
  `MIN_AXIOMS` floor lowered; `docs/fv/trusted-base.md` ledger entry
  for class #9 updated (1 axiom → no closure axiom; only
  `bin_ext_table_consumer_wf` remains in that class).
- **Step 5 (DONE):** `lake build`, V1 + V2 gates, and `nix run .#test`
  all pass.

## Step 3 design

Add a bridge theorem in `ZiskFv/Airs/Tables/BinaryExtensionTable.lean`
(or a new dedicated file like `ZiskFv/Circuit/SextLoadBridge.lean`)
that takes the BinaryExtension AIR connection witnesses and derives
the existing `signextend_c_packed_for_op` conclusion shape:

```lean
theorem signextend_load_c_packed_proven
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_BinaryExtension C FGL FGL) (r_binary : ℕ)
    (e1 e2 : MemoryBusEntry FGL)
    -- Existing structural witnesses (already supplied by LB/LH/LW callers):
    (h_emit_b : m.b_0 r_main = memory_entry_lo e1
              ∧ m.b_1 r_main = memory_entry_hi e1
              ∧ e1.as = 2 ∧ e1.multiplicity = -1)
    (h_emit_c : m.c_0 r_main = memory_entry_lo e2
              ∧ m.c_1 r_main = memory_entry_hi e2)
    (h_ext : m.is_external_op r_main = 1)
    -- New BinaryExtension AIR connection (op-bus permutation handshake):
    (h_op_match : (v.op r_binary).val = (m.op r_main).val)
    -- Per-byte input matching — only the bytes the SEXT op consumes:
    (h_a0_match : (v.free_in_a_0 r_binary).val = e1.x0.val)
    (h_a1_match : (v.free_in_a_1 r_binary).val = e1.x1.val)
    (h_a2_match : (v.free_in_a_2 r_binary).val = e1.x2.val)
    (h_a3_match : (v.free_in_a_3 r_binary).val = e1.x3.val)
    -- Output matching: Main's c_0/c_1 = sums of v.free_in_c_*:
    (h_match_clo : (m.c_0 r_main).val = Σ_{i∈0..7} (v.free_in_c_i r_binary).val)
    (h_match_chi : (m.c_1 r_main).val = Σ_{i∈8..15} (v.free_in_c_i r_binary).val)
    -- Lookup-soundness: 8 byte entries with multiplicity 1:
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    -- Byte-range hypotheses on e1/e2 (e1.x0..3 < 256, e2.x0..7 < 256):
    (h_e1_byte_ranges : ...) (h_e2_byte_ranges : ...) :
    signextend_c_packed_for_op e1 e2 (m.op r_main) := by
  refine ⟨?_op_b, ?_op_h, ?_op_w⟩
  case op_b =>
    intro h_op
    -- Use binary_extension_sext_b_chunks_eq_signextend_nat
    -- Lift Nat identity to BitVec via signExtend 64 (BitVec.ofNat 8) lemma
    -- Pack memory_entry_lo/hi into U64.toBV [e2.x0..7] via byte-pack identity
    sorry
  case op_h => sorry
  case op_w => sorry
```

Each `case` is ~30-60 lines and shares structure:

1. Specialize the appropriate packed-correctness theorem
   (`binary_extension_sext_<X>_chunks_eq_signextend_nat`) at `v` and
   `r_binary`. Needs `(v.op r_binary).val = OP_SEXT_<X>` — derive from
   `h_op_match` and `m.op r_main = OP_SIGNEXTEND_<X>` (which equals
   `OP_SEXT_<X>` numerically).
2. Substitute `h_match_clo` and `h_match_chi` to bring Main's
   `c_0/c_1` into the equation.
3. Use `memory_entry_lo`/`memory_entry_hi` definitions to expand
   `m.c_0 = e2.x0 + e2.x1*256 + e2.x2*65536 + e2.x3*16777216` and
   similar for hi.
4. Use byte-pack identity (`memory_entry_toField_eq_toBV_toNat` or
   `u64_toBV_eq_ofNat_fgl_val` from `Fundamentals/PackedBitVec.lean`)
   to identify `U64.toBV [e2.x0..7] = BitVec.ofNat 64 (m.c_0.val + m.c_1.val * 2^32)`.
5. Use a NEW small helper lemma (which needs writing):
   `BitVec.ofNat 64 (if a ≥ 128 then a + (2^64 - 256) else a)`
   `= BitVec.signExtend 64 (BitVec.ofNat 8 a)`
   for `a < 256`. Similarly for SEXT_H (with 2^16) and SEXT_W (with 2^32).
6. Apply `h_a0_match` etc. to convert v.free_in_a_<i> back to e1.x<i>.

## Step 4 — convert axiom to theorem

After Step 3 lands, in `ZiskFv/Airs/Tables/BinaryExtensionTable.lean`:

1. Change `axiom signextend_load_c_packed` to `theorem
   signextend_load_c_packed`. Take all the new parameters introduced
   in Step 3.
2. Body: invoke `signextend_load_c_packed_proven` with the new params.
   (Or just merge — rename the proven version.)
3. Update LB/LH/LW (`ZiskFv/Equivalence/{Lb,Lh,Lw}.lean`) to supply
   the new parameters at the call site.
4. Run `trust/scripts/regenerate.sh` — `trust/baseline-axioms.txt`
   shrinks 84 → 83. Lower `MIN_AXIOMS` floor in
   `trust/scripts/check-floor.sh` (84 → 83).
5. Run `lake exe trust-gate regenerate-deps` — `trust/baseline-equiv-axiom-deps.txt`
   updates: LB/LH/LW lose `signextend_load_c_packed`, gain
   `bin_ext_table_consumer_wf` (already counted).
6. Update `docs/fv/trusted-base.md` ledger to retire class #9's
   second axiom (back to a single `bin_ext_table_consumer_wf`).

## Step 5 — verify

```
lake build
trust/scripts/check-all.sh                  # V1 syntactic
nix develop --command bash trust/scripts/check-all-semantic.sh  # V2 semantic
nix run .#test
```

## Estimated size

* Step 3 bridge theorem: ~250-400 lines (3 subcases × ~80-130 each).
* Step 3 LB/LH/LW signature additions: ~50-100 lines per file.
* Step 4 mechanical updates: small.
* Total remaining: ~600-900 LoC.
