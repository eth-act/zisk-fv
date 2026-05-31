# DIV/REM Dynamic Witness Resolution Audit

Date: 2026-05-30

## Outcome

`DIVU`, `REMU`, `DIVUW`, and `REMUW` are no longer covered by the broad
`ArithDivDynamicWitnessShape` known-defect gate.

The proof now derives the unsigned dynamic facts from concrete
constructible evidence:

* ArithDiv chunk ranges from `ChunkRangeLookupWitness`.
* ArithDiv unsigned carry ranges from `UnsignedCarryRangeLookupWitness`.
* DIVU/REMU/DIVUW/REMUW mode and selector pins from Clean ArithTable
  projections.
* Operand packing from the transpiler contract, `matches_entry`, and Sail
  register reads.
* The Euclidean remainder bound `d < b` from ArithDiv's real
  remainder-bound operation-bus consumer matched to a Binary LTU provider row.
* W-mode high-chunk pins from the W high-lane operation-bus collapse, plus
  quotient high-zero facts from the unsigned Euclidean identity.

No axioms were added. The removed caller promises are:

* `h_op2_ne : <rs2>.toNat ≠ 0`
* `h_no_arith_div_dynamic_defect : False`

The replacement binders are structural witnesses (`arith_chunk_ranges`,
`arith_carry_ranges`, and `remainder_bound`). They are constructibility
evidence for existing Clean lookup / operation-bus paths, not output-equality
promises.

## Remaining Defect Scope

The known-defect gate still covers:

* `DIV`
* `DIVW`
* `REM`
* `REMW`

The remaining work is signed-specific:

* signed sign-witness relations for `np`, `nb`, and `nr`;
* signed Euclidean remainder bounds;
* explicit divide-by-zero behavior;
* signed overflow behavior, including `INT64_MIN / -1` and
  `INT32_MIN / -1`.

The first constructibility bridge for the signed route is now present:
`ZiskFv.EquivCore.Bridge.Arith.arith_div_signed_carry_ranges_at_holds`
derives `ArithDivSignedCarryRangesAt` from the Clean
`SignedCarryRangeLookupWitness`. That removes the need for a future
caller-supplied signed carry-range promise, but the signed opcode wrappers are
not retired from the defect gate until the sign pins, signed remainder bounds,
boundary cases, and top-level wrapper composition are proved end to end.

The non-W signed chain and write-value layers are also now present:

* `ZiskFv.EquivCore.Bridge.Arith.div_signed_chain_witnesses` lifts the
  ArithDiv signed carry-chain constraints to the signed Euclidean chunk
  identity consumed by the pure signed DIV/REM math.
* `ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_div_chunked`
  derives the 64-bit signed DIV quotient from that chain identity, byte-lane
  packing, sign witnesses, and explicit non-boundary preconditions.
* `ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned.h_rd_val_mdrs_rem_chunked`
  derives the 64-bit signed REM remainder under the same non-boundary
  preconditions.
* `ZiskFv.EquivCore.Bridge.Arith.arith_div_remainder_bound_op_of_signs`
  isolates the ArithDiv remainder-bound consumer's `nr`/`nb` selector:
  `(0,0) -> LTU`, `(1,0) -> LT_ABS_NP`, `(0,1) -> LT_ABS_PN`,
  `(1,1) -> GT`. The remaining signed remainder-bound proof is therefore
  localized to Binary semantics for `LT_ABS_NP`, `LT_ABS_PN`, and `GT`;
  the Arith-side op expression no longer has to be re-expanded at each
  call site.

These lemmas are intentionally not counted as defect retirement yet. The
legacy `EquivCore.Div` / `EquivCore.Rem` surfaces now compose the non-boundary
chunked write-value lemmas, but the Compliance wrappers and canonical
Equivalence theorems still
need structural witness plumbing plus sign-pin, signed-remainder-bound, and
boundary-case discharge before the known-bug exclusion can be retired.

## Signed Remainder-Bound Blocker

The signed proof attempt localized the remaining non-W DIV/REM obstacle to
Binary's `LT_ABS_NP` table semantics. The ArithDiv signed remainder-bound
consumer chooses:

* `(nr, nb) = (0, 0)` -> `LTU`
* `(nr, nb) = (1, 0)` -> `LT_ABS_NP`
* `(nr, nb) = (0, 1)` -> `LT_ABS_PN`
* `(nr, nb) = (1, 1)` -> `GT`

The `LTU` branch is already proved for unsigned DIV/REM. `GT` is a normal
signed comparison branch. `LT_ABS_NP`, however, has a concrete whole-word
vs byte-chain mismatch on strict equality when the negative operand's
absolute value is a multiple of 256.

Minimal executable model of the mismatch. The Lean version is checked as
`ZiskFv.Airs.Binary.ltAbsNpByteChain_falsePositive_eqAbs256` in
`ZiskFv/Airs/Binary/BinaryPackedCorrect.lean`.

```python
MASK = (1 << 64) - 1

def lt_abs_np_chain(a, b):
    cin = 0
    for i in range(8):
        ai = (a >> (8 * i)) & 255
        bi = (b >> (8 * i)) & 255
        sub = ((ai ^ 255) + 1 - bi) if i == 0 else ((ai ^ 255) - bi)
        cin = 1 if sub < 0 else cin if sub == 0 else 0
    return cin

a = 0xffffffffffffff00  # -256 as u64
b = 0x100               # +256
assert ((a ^ MASK) + 1) & MASK == 256
assert not (256 < b)
assert lt_abs_np_chain(a, b) == 1
```

This mirrors upstream:

* `zisk/state-machines/binary/src/binary_basic.rs` computes the whole-word
  helper with `let a_pos = (a ^ MASK_U64).wrapping_add(1); a_pos < b`.
* The per-byte table path computes byte 0 as `(a0 ^ 0xff) + 1 - b0`, but
  bytes 1..7 as `(ai ^ 0xff) - bi`, so the `+1` carry is not propagated.

Therefore the strict signed remainder bound `|r| < |rs2|` cannot currently
be proved from the real constraints for the `(nr, nb) = (1, 0)` branch.
Removing the signed DIV/REM defect gate would be unsound unless upstream
rejects this witness shape or the theorem explicitly excludes it.

The sampled equality cases for the opposite `(nr, nb) = (0, 1)` branch
(`LT_ABS_PN`) do not show the same failure: `+k` vs `-k` agrees with the
strict whole-word comparison for the tested boundary values. The current
known blocker is therefore the negative-remainder/positive-divisor
`LT_ABS_NP` branch.

## Ledger Effect

The canonical hypothesis-count ledger changed as follows:

* `ZiskFv.Equivalence.Divu.equiv_DIVU`: `hypothesis=4` to `hypothesis=2`.
* `ZiskFv.Equivalence.Remu.equiv_REMU`: `hypothesis=4` to `hypothesis=2`.
* `ZiskFv.Equivalence.Divuw.equiv_DIVUW`: removed `h_op2_ne` and
  `h_no_arith_div_dynamic_defect`; added constructible unsigned range and
  remainder-bound witnesses.
* `ZiskFv.Equivalence.Remuw.equiv_REMUW`: removed `h_op2_ne` and
  `h_no_arith_div_dynamic_defect`; added constructible unsigned range and
  remainder-bound witnesses.

The total binder count grows by one per opcode because this is structural
unpacking: two promise/defect binders were removed and three constructible
witness binders were exposed. The semantic closure now records the real proof
dependencies on:

* `ZiskFv.AirsClean.ArithDiv.arithDiv_circuit_completeness`
* `ZiskFv.Trusted.transpiler_contract_sound`

Follow-up trust-shape cleanup after the upstream bug repro confirmed the
signed `LT_ABS_NP` issue replaced the canonical signed `DIV`/`REM`/`DIVW`/`REMW`
`h_no_arith_div_dynamic_defect : False` promise with
`h_avoid_known_bugs : Defects.NoKnownDefect <signed-DIV/REM envelope>`. This is
not a proof of the signed arms; those envelopes are still blocked by
`Defects.ArithDivDynamicWitnessShape`. The change makes the caller-burden
ledger point at the existing known-bug registry instead of an unstructured
contradiction. The lower `ZiskFv.Compliance.Wrappers.*` compatibility theorem
surfaces still carry the legacy `False` binder because they sit below
`OpEnvelope` in the import graph.
