# ArithTable Axiom Audit

This audits the ArithTable-facing facts currently or historically tracked in
`trust/baseline-arith-table-op-axioms.txt`, plus the adjacent sign/operand
facts in `ZiskFv/Airs/Arith/Ranges.lean` that play the same role in the
MUL/DIV/REM proofs.

Status key:

- `derived-via-lookup`: already a theorem from
  `arith_{mul,div}_table_lookup_sound` plus a finite Clean
  `ArithTableSpec` projection. The remaining trust is the shared lookup /
  permutation soundness axiom, not an opcode-shaped fact.
- `derivable-via-lookup`: should be a finite-table projection, but no theorem
  is currently wired.
- `false-as-static`: cannot be derived from the table because the statement is
  not true for all matching table rows.
- `dynamic-proof-needed`: the old static statement must be replaced by a proof
  using row constraints, range facts, bus matching, or a defect record.

## Shared Lookup Boundary

| Name | Status | Audit |
|---|---|---|
| `arith_mul_table_lookup_sound` | retired in T5 | The shared ArithMul lookup/permutation axiom was removed. Canonical and compatibility wrappers now consume explicit row-native `ArithTableSpec (ArithMul.rowAt v r)` witnesses. |
| `arith_div_table_lookup_sound` | retired in T5 | Same boundary for ArithDiv. Canonical and compatibility DIV/REM-family proofs now consume explicit row-native `ArithTableSpec (ArithDiv.rowAt v r)` witnesses instead of calling a lookup axiom inside the proof. |

## Baseline ArithTable Opcode Facts

| Name | Status | Audit |
|---|---|---|
| `arith_table_op_div_rem_signed_d_sign_pin` | not pure table / dynamic-or-range proof needed | C3.2-P3 corrected the earlier audit: `nr = np` is a table relation, but the alternate branch mentions concrete `d[]` chunk values. `ArithTableSpec (rowAt v r)` contains `range_cd`, not `d_0..d_3`, so the zero-remainder branch must use row/range constraints beyond the table lookup. |
| `arith_table_op_div_rem_signed_w_d_sign_pin` | not pure table / dynamic-or-range proof needed | W-mode analog of the previous row. It cannot be a pure Clean finite-table projection because the table lookup does not expose concrete `d[]` chunks. |
| `arith_table_op_mulw_operand_pin` | not pure table / W operand proof needed | C3.2-P3 corrected the earlier audit: the lookup tuple has mode/sign/range selectors, not concrete `a_2/a_3/b_2/b_3` chunks. The upper-operand zero fact must come from W-mode row constraints / bus shape, under an independently justified W-mode premise. |
| `arith_table_op_divw_operand_pin` | not pure table / W operand proof needed | Same for DIV/REM W-family operands and upper remainder chunks. The table lookup can supply `m32/div/range_*` selectors, but not concrete zero chunk values. |
| `arith_table_op_div_rem_signed_mode_pin` | derived-via-row-witness | Already theorem from `Div.div_rem_signed_mode_pin` plus explicit `ArithDiv.ArithTableSpec`. True static non-W signed DIV/REM mode fact. |
| `arith_table_op_div_rem_main_selector_pin` | derived-via-row-witness | Already theorem from `Div.div_rem_main_selector_pin` plus explicit `ArithDiv.ArithTableSpec`. True selector projection. |
| `arith_table_op_mul_mode_pin` | false-as-static / dynamic-proof-needed | Pins `na = nb = np = 0` for `MUL`. The replacement already in the tree shows the true static facts are only `mul_basic_mode_pin`, range pins, and `mul_np_xor_or_zero_product_shape`; exceptional sign rows exist. Correctness must use the dynamic carry/range proof or remain defect-gated. |
| `arith_table_op_mul_main_selector_pin` | derived-via-row-witness | Already theorem from `Mul.mul_main_selector_pin` plus explicit `ArithMul.ArithTableSpec`. True selector projection. |
| `arith_table_op_div_rem_unsigned_mode_pin` | derived-via-row-witness | Already theorem from `Div.div_rem_unsigned_mode_pin` plus explicit `ArithDiv.ArithTableSpec`. True static DIVU/REMU mode fact. |
| `arith_table_op_div_rem_unsigned_main_selector_pin` | derived-via-row-witness | Already theorem from `Div.div_rem_unsigned_main_selector_pin` plus explicit `ArithDiv.ArithTableSpec`. True selector projection. |
| `arith_table_op_div_rem_unsigned_w_mode_pin` | false-as-static | Pins `sext = 0` for all DIVUW/REMUW rows. Clean has `Counterexamples.divuw_sext_zero_not_static`, so this cannot be a table projection. The true static subset is `div_rem_unsigned_w_basic_mode_pin`. |
| `arith_table_op_div_rem_signed_w_mode_pin` | false-as-static | Pins `sext = 0` for all DIVW/REMW rows. Clean has `Counterexamples.divw_sext_zero_not_static`, so this cannot be a table projection. The true static subset is `div_rem_signed_w_basic_mode_pin`. |
| `arith_table_op_mulhu_mode_pin` | derived-via-row-witness | Already theorem from `Mul.mulhu_mode_pin` plus explicit `ArithMul.ArithTableSpec`. True static MULHU mode fact. |
| `arith_table_op_mulhu_main_selector_pin` | derived-via-row-witness | Already theorem from `Mul.mulhu_main_selector_pin` plus explicit `ArithMul.ArithTableSpec`. True selector projection. |
| `arith_table_op_mulh_mode_pin` | false-as-static / dynamic-proof-needed | Its basic mode/boolean subset is true and already derived, but the `np_xor` conclusion is false as a static table fact. Clean proves `Counterexamples.mulh_np_xor_not_static`. C3.2 needs a different signed high-half dynamic proof or a defect. |
| `arith_table_op_mulh_main_selector_pin` | derived-via-row-witness | Already theorem from `Mul.mulh_main_selector_pin` plus explicit `ArithMul.ArithTableSpec`. True selector projection. |
| `arith_table_op_mulhsu_mode_pin` | false-as-static / dynamic-proof-needed | Same problem as MULH: basic facts are true and already derived, but static `np_xor` is false. Clean proves `Counterexamples.mulhsu_np_xor_not_static`. |
| `arith_table_op_mulhsu_main_selector_pin` | derived-via-row-witness | Already theorem from `Mul.mulhsu_main_selector_pin` plus explicit `ArithMul.ArithTableSpec`. True selector projection. |
| `arith_table_op_mulw_mode_pin` | false-as-static | Pins `sext = 0` and `np_xor` for all MULW rows. Clean has `Counterexamples.mulw_sext_zero_not_static`; the true static subset is `mulw_basic_mode_pin`. Any remaining signed-product relation must be proved dynamically. |

## Adjacent Sign / Bound Facts

These are not in `baseline-arith-table-op-axioms.txt`, but they are the same
kind of risk because they are currently trusted facts about ArithTable-selected
arithmetic behavior.

| Name | Status | Audit |
|---|---|---|
| `arith_div_np_eq_msb_of_dividend` | not pure table / dynamic-or-range proof needed | Claims the signed dividend witness equals an MSB expression over chunks. This is a row-meaning fact, not just a finite opcode projection. It may be derivable from table row type plus range/packing facts, but it is not currently a Clean projection. |
| `arith_div_nb_eq_msb_of_divisor` | not pure table / dynamic-or-range proof needed | Same for divisor sign witness. |
| `arith_div_remainder_bound` | dynamic/protocol boundary | Remainder magnitude bound comes from `assumes_operation` / range-table behavior, not a static opcode table row. It should not be classified as an ArithTable projection. |
| `arith_div_remainder_bound_unsigned` | dynamic/protocol boundary | Same, unsigned non-W. |
| `arith_div_remainder_bound_unsigned_w` | dynamic/protocol boundary | Same, unsigned W. |
| `arith_div_remainder_bound_signed_w` | dynamic/protocol boundary | Same, signed W. |
| `arith_mul_na_eq_msb_of_a` | not pure table / dynamic-or-range proof needed | Sign witness equals operand MSB for MULH/MULHSU. This depends on how table row-type flags bind witness columns to packed operand chunks. It is not currently a Clean finite projection and may need range/packing support. |
| `arith_mul_nb_eq_msb_of_b` | not pure table / dynamic-or-range proof needed | Same for MULH second operand. |

## Bottom Line

The old opcode-shaped ArithTable axiom family splits into three groups:

1. True finite-table projections already derivable from Clean lookup membership
   plus shared lookup soundness.
2. Facts that looked table-shaped but mention concrete witness chunks or
   dynamic arithmetic behavior; these need row/range/bus proofs, not table
   projection lemmas.
3. False static claims, mostly `sext = 0` and `np_xor` claims over rows where
   the table deliberately contains multiple cases.

The third group cannot be retired by deriving the same statement. It must be
replaced by dynamic proofs from row constraints/range facts, or by explicit
defects if the full constraints admit a bad witness.

## T5 Canonical Lookup Split

T5 routes all 13 canonical `MUL*`, `DIV*`, and `REM*` equivalence theorems
through row-native `_of_table` wrappers. Each canonical theorem now exposes one
structural `h_arith_table` binder for the selected Arith provider row, and the
semantic closures no longer include `arith_mul_table_lookup_sound` or
`arith_div_table_lookup_sound`. This is recorded as a structural-unpacking
exception because the binder is the row membership witness formerly hidden
inside the wrapper closure, not an opcode-specific arithmetic promise.

The legacy wrappers with the old names remain as compatibility entry points,
but their signatures now also require the explicit row-native witness. That
preserves existing theorem names while retiring the lookup axioms from the
trust ledger and leaving the path ready for a future Compliance-level Arith
ensemble witness.

## C3.2-P2 Active-Closure Purge

The false opcode-shaped facts have been removed from the active wrapper
closures, and the false declarations themselves have been deleted from
`ZiskFv/Airs/Arith/Ranges.lean` (`MUL`, `MULH`, `MULHSU`, `MULW`,
unsigned-W DIV/REM, and signed-W DIV/REM). The temporary obligations that
replace the remaining signed-MUL cases are:

| Wrapper | Temporary obligation | Classification |
|---|---|---|
| `MULH` | `np = na XOR nb` in `toIntZ` form | dynamic signed high-half witness soundness |
| `MULHSU` | `np = na XOR nb` in `toIntZ` form | dynamic signed/unsigned high-half witness soundness |
| `MUL` | exceptional low-MUL product-shape branch is unreachable | dynamic zero-product / range-row proof |

The `MULH`/`MULHSU` high-half branches have concrete malicious-row shapes,
not merely missing Lean bridges: with `rs1 = -1`, `rs2 = 1`, rows using
`na = 1`, `nb = 0`, `np = 0`, `c = 1`, `d = 0` satisfy the signed carry-chain
equations with carries `[-1,-1,-1,-1,0,0,0]` and the relevant sign ranges,
but Sail returns `0xffffffffffffffff`, not `0`. The executable repro branch
`repro/mulh-mulhsu-malicious-witness-demo` at ZisK commit `0142ab5d7`
confirmed that stock ZisK accepts and verifies malicious proofs for
`MULH(-1,1)=0` and `MULHSU(-1,1)=0`. This is why `MULH`/`MULHSU` are now
tracked under `arithMulSignedWitnessSoundness` rather than as ArithTable
trust-shape work.

`MULW` has been repaired: the core no longer asks for `sext = 0`; the
wrapper keeps true static pins from `arith_table_op_mulw_basic_mode_pin`,
uses `h_sext_choice` for result sign-extension, and derives operand
high-chunk zeroes from the operation-bus W high-lane collapse.

`DIVUW` and `REMUW` have also been repaired: the core no longer asks for
`sext = 0`, and the wrappers are removed from the defect predicate. Their
closures still consume dynamic Div/Rem facts (`arith_table_op_divw_operand_pin`
and `arith_div_remainder_bound_unsigned_w`), which are C6-deferred
row/range/bus facts rather than false static ArithTable projections.

`DIVW` and `REMW` have the same W-contract repair: the core no longer asks
for `sext = 0`, and the wrappers are removed from the defect predicate. Their
closures still consume dynamic Div/Rem facts
(`arith_table_op_div_rem_signed_w_d_sign_pin`,
`arith_table_op_divw_operand_pin`, and
`arith_div_remainder_bound_signed_w`), which are C6-deferred row/range/bus
facts rather than false static ArithTable projections.

The remaining obligations are no longer proof holes. They are represented
as explicit known-defect exclusions in the affected wrappers/canonical
theorems and in the global `h_known_bugs : Defects.NoKnownDefect env`
hypothesis. This restores zero-sorry while preserving the fact that signed
multiply is not fully proved.

For the W-family rows, C3.2-P5 must not try to prove `sext = 0`. The
finite table contains matching rows with `sext = 1`; this is expected because
`sext` participates in the high 32 bits of the write value. The correct
repair is to change the W core contracts so they consume the existing
`h_sext_choice` / byte-extension evidence and separately justified W operand
chunk facts, rather than taking `sext = 0`.
