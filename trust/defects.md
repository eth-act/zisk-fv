# Defect ledger

This ledger tracks known defects that affect the formal verification claim.
The ledger is not the trust ledger: do not add axioms to cover these rows.
Each open defect must either block the unqualified theorem or appear as an
explicit exception predicate in the theorem statement.

Every known defect must be visible in three places:

1. a human-readable ledger entry in this file;
2. a Lean predicate under `ZiskFv/Compliance/Defects.lean` naming the exact
   excluded behavior or blocked witness shape;
3. a top-level theorem statement whose name and hypotheses make the
   exception explicit.

The theorem must exclude the smallest behavior justified by the evidence.
Excluding an entire opcode is allowed only when the defect covers the whole
opcode. Ordinary out-of-scope items, such as precompiles or non-RV64IM
extensions, belong in scope documentation rather than this ledger.

| Kind | Meaning | Theorem treatment |
|------|---------|-------------------|
| `implementation-semantic` | ZisK intentionally or accidentally implements less than the RV64IM Sail behavior for an in-scope opcode. | Prove compliance on the complement of a precise defect predicate. |
| `circuit-soundness` | A malicious witness can satisfy the constraints while disagreeing with the intended execution relation. | Do not advertise an unqualified compliance theorem for affected cases. Either prove a precise exclusion theorem or mark the claim blocked. |
| `trust-shape` | An axiom states an opcode-level conclusion that should instead be derived from a shared trust boundary plus finite proofs. | Replace with a shared boundary and derived projection theorems. The defect is closed only when the bad axiom disappears from the global theorem closure. |
| `modeling-gap` | The Lean model deliberately abstracts something required for the real implementation claim. | Either move it to the scope document if it is out of scope, or express it as an explicit theorem hypothesis. |

## Open / mitigated defects

### ZISK-DEFECT-ARITH-TABLE-TRUST-SHAPE

| Field | Value |
|-------|-------|
| `kind` | `trust-shape` |
| `status` | `retired-in-lean` |
| `affected` | None in `Defects.UsesOpcodeSpecificArithTableAxiom`. The false opcode-shaped declarations for `MUL`, `MULH`, `MULHSU`, `MULW`, unsigned-W DIV/REM, and signed-W DIV/REM have been deleted from `ZiskFv.Airs.Arith.Ranges`. |
| `condition` | Opcode-specific ArithTable conclusions are trusted directly instead of proved from shared table membership plus finite projections. |
| `evidence` | See [`trusted-base.md`](trusted-base.md). |
| `claim impact` | This trust-shape defect no longer blocks the defect-aware theorem. The ordinary zero-sorry invariant is restored for this cleanup; the remaining signed-MUL limitation is tracked separately as `ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS`. |
| `retirement condition` | Met for the defect predicate: every C3/C4 constructor is removed from `Defects.UsesOpcodeSpecificArithTableAxiom`; proof closures for repaired arms consume shared lookup/permutation membership plus proved finite-table projections, not false opcode-shaped ArithTable facts. |

### ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS

| Field | Value |
|-------|-------|
| `kind` | `circuit-soundness` |
| `status` | `open` |
| `affected` | Arith signed multiplication witness relation for `MUL`, `MULH`, and `MULHSU` under malicious witness construction. |
| `condition` | A malicious witness can select signed-multiply table rows where the product-sign witness is not `na XOR nb`; the carry-chain then describes an absolute/product-shape relation rather than the intended two's-complement signed result. |
| `evidence` | Clean finite-table counterexamples show `MULH` and `MULHSU` rows with `na = 1`, opposite unsigned/nonnegative operand sign, and `np = 0`. The range-table shape admits positive `d3` for that branch, so the signed high-half proof cannot recover Sail semantics from the old `np_xor` shortcut. Executable repro: a separate ZisK worktree at commit `0142ab5d7` was branched as `repro/mulh-mulhsu-malicious-witness-demo` and run on 2026-05-22 with Docker image `zisk-arith-mul-repro:mulh-demo`. Stock ZisK accepted and verified malicious proofs for all three shapes: `MUL(-1,1)=1`, `MULH(-1,1)=0`, and `MULHSU(-1,1)=0`. The bad row family uses `na = 1`, `nb = 0`, `np = 0`, `c = 1`, `d = 0`, carries `[-1,-1,-1,-1,0,0,0]`; for high-half cases this contradicts Sail, which returns `0xffffffffffffffff`, not `0`. |
| `claim impact` | This is not a normal opcode input exception. The global theorem now explicitly takes `h_known_bugs : Defects.NoKnownDefect env`, and the affected `MUL`, `MULH`, and `MULHSU` wrapper/canonical theorems carry a visible `h_no_signed_mul_witness_defect : False` binder. This is claim weakening, not promise discharge. |
| `retirement condition` | Upstream constraints reject the malicious witness, or Lean proves the affected witness shape impossible from the real constraints and shared table/lookup boundaries. The repro must fail in verifier/prover mode after the fix. |

### ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS

| Field | Value |
|-------|-------|
| `kind` | `circuit-soundness` |
| `status` | `open` |
| `affected` | Arith division/remainder witness relations for the signed `DIV`, `DIVW`, `REM`, and `REMW` arms. `DIVU`, `REMU`, `DIVUW`, and `REMUW` were retired from this defect on 2026-05-30. |
| `condition` | The retired `arith_table_op_*` and `arith_div_*` assumptions were not pure ArithTable projections. They connected row selectors to concrete operand chunks, sign witnesses, W-mode upper-chunk pins, and Euclidean remainder bounds. The signed remainder-bound consumer additionally relies on Binary's `LT_ABS_NP` / `LT_ABS_PN` / `GT` operations rather than plain `LTU`. |
| `evidence` | [`trusted-base.md`](trusted-base.md) summarizes the ArithTable and DIV/REM audit conclusions. T5 removed the nine source axioms from `ZiskFv.Airs.Arith.Ranges` instead of keeping them in the trust ledger. The 2026-05-30 unsigned pass rebuilt both non-W and W routes from Clean ArithDiv chunk/carry range lookups plus the real ArithDiv remainder-bound operation-bus consumer matched to Binary LTU. That removed `h_op2_ne` and `h_no_arith_div_dynamic_defect` from `DIVU`, `REMU`, `DIVUW`, and `REMUW`. The signed carry-range bridge now derives `ArithDivSignedCarryRangesAt` from `SignedCarryRangeLookupWitness`, `div_signed_chain_witnesses` proves the non-W signed Euclidean chain identity, and `h_rd_val_mdrs_{div,rem}_chunked` prove non-boundary signed DIV/REM outputs; the legacy `EquivCore.Div` / `EquivCore.Rem` surfaces compose those lemmas. The attempted signed remainder-bound proof exposed a concrete `LT_ABS_NP` mismatch, now checked by `ZiskFv.Airs.Binary.ltAbsNpByteChain_falsePositive_eqAbs256`: for `a = 0xffffffffffffff00` (`-256`) and `b = 0x100` (`256`), the Rust whole-word helper `lt_abs_np_execute` computes `((-a) mod 2^64) < b`, hence `256 < 256 = false`, but the per-byte table chain returns final carry `1`. The same false-positive equality shape occurs for `-512` vs `512`, `-65536` vs `65536`, and `-2^32` vs `2^32`. This is exactly the strict signed remainder-bound predicate needed by Sail DIV/REM, so the signed false gate cannot be removed by proof until this discrepancy is narrowed or fixed upstream. |
| `claim impact` | The global theorem excludes the remaining four signed DIV/REM arms through `Defects.ArithDivDynamicWitnessShape`. The canonical `ZiskFv.Equivalence.{Div,Rem,Divw,Remw}` surfaces now carry a visible `h_avoid_known_bugs : Defects.NoKnownDefect <signed-DIV/REM envelope>` binder instead of the old unstructured `h_no_arith_div_dynamic_defect : False` promise; because these envelopes are registered known-bug shapes, that premise is intentionally contradictory. The lower `ZiskFv.Compliance.Wrappers.*` compatibility surfaces still contain the legacy `False` binder because importing `Defects` there would create an `OpEnvelope`/wrapper module cycle; the global theorem and canonical audit surface no longer consume it. The unsigned `DIVU`, `REMU`, `DIVUW`, and `REMUW` arms no longer use the claim-weakening gate. |
| `retirement condition` | Upstream must either fix the `LT_ABS_NP` byte-chain semantics or prove/add constraints that exclude the false-positive equality shape from ArithDiv signed remainder rows. After that, prove constructible ArithDiv range lookup witnesses and operation-bus facts for the remaining signed obligations: sign-witness relations, signed remainder bounds, divide-by-zero, and signed-overflow behavior. If the upstream behavior is intentional, keep the defect gate narrowed to the exact signed remainder-bound false-positive witness shape rather than removing it. |

### ZISK-DEFECT-FENCE-INCOMPLETE

| Field | Value |
|-------|-------|
| `kind` | `implementation-semantic` |
| `status` | `open-needs-triage` |
| `affected` | RV64I `FENCE`; `ZiskFv/SailSpec/fence.lean`; `ZiskFv/EquivCore/Fence.lean`; `ZiskFv/Compliance/Wrappers/Fence.lean`. |
| `condition` | ZisK appears to implement FENCE as `nop()` / `PC += 4`; the exact unsupported behavior relative to the intended RV64IM platform model still needs to be pinned down. |
| `evidence` | `ZiskFv/SailSpec/fence.lean` cites the transpiler lowering and proves the no-op Sail subset under Machine mode and the Sail concurrency stub. User report: ZisK does not currently support FENCE completely. |
| `claim impact` | FENCE should stay in opcode coverage, but the theorem should be named or hypothesized as compliance for the `FenceNopEquivalent` subset until the full support boundary is explicit. |
| `retirement condition` | Either prove the current no-op model is the full in-scope RV64IM platform behavior, or update ZisK and the proof so FENCE compliance no longer needs a defect predicate. |

## Retired defects

* `ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS` for `DIVU`,
  `REMU`, `DIVUW`, and `REMUW`: retired on 2026-05-30 by deriving
  unsigned chunk/carry ranges, W high-chunk facts, nonzero-divisor
  facts, quotient high-zero facts, and the remainder-bound fact from
  concrete ArithDiv/Binary operation-bus evidence plus the unsigned
  Euclidean identity.
