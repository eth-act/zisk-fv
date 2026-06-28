# Issue #101 — Binary-EQ branch-flag aggregation — closeout record

`Closes #101` ("Prerequisite (P4 #61 child): Binary-EQ 8-byte aggregation
lemma (templated by SLT)").

This is the decision/evidence record confirming that #101's acceptance
criteria are met in-tree. The substantive proof content landed under its
sibling **#100 (PR #163, "faithful cross-row PC handshake")**, which
discharged the BEQ/BNE flag *and* the cross-row next-PC together. #101 was
never formally closed because #163 referenced #100; this record supplies the
criterion-by-criterion evidence and the GitHub closure.

- **Sibling that landed the work:** #100 / PR #163 (merged to `main`).
- **Issue #101 template:** mirror the proven SLT/SLTU comparison chain to
  derive the branch equality flag from the Binary state-machine's per-byte
  facts rather than carrying it as an opaque promise.

## Acceptance criteria — status

#101 listed four acceptance criteria. All are satisfied on `main`.

### 1. EQ aggregation lemma landed and proved — DONE

`binary_eq_chunks_eq_bv_eq_of_wf` is landed in
`ZiskFv/Airs/Binary/BinaryPackedCorrect.lean` and consumed by the Binary
equivalence bridge `ZiskFv/EquivCore/Bridge/Binary.lean`. It is the EQ
analogue of the SLT/SLTU comparison aggregation the issue named as the
template (`binary_lt_chunks_eq_bv_slt_of_wf`).

### 2. BEQ/BNE flag derived, not promised — DONE

The Main `flag` column is *derived* from the OP_EQ Binary provider row, not
assumed:

- `ZiskFv/EquivCore/Bridge/BranchFlag.lean::branch_flag_eq_of_static_row`
  proves `m.flag r_main = (if r1_val == r2_val then 1 else 0)` from a
  static-table OP_EQ Binary row, via the equality byte-chain
  (`static_eq_chain_flags7_iff_eq` in `EquivCore/Bridge/Binary.lean`) and the
  flag-lane projection (`compare_flag_lane_of_match`). This reuses the exact
  comparison `cout` SLT/SLTU's `rd` value uses — surfaced on the `flag` lane —
  so the branch flag inherits SLT/SLTU's verified comparison soundness with no
  new trust.
- `ZiskFv/Compliance/TraceLevelExport/StepStrongControlStore.lean::branch_flag_eq_provided`
  sources the provider row from the accepted trace
  (`main_request_eq_provided`) and concludes the same flag equation at the
  trace layer.
- `stepStrong_beq` / `stepStrong_bne` (same file) then **construct** the
  `BranchPromises.nextPC_matches` field from that derived flag. The
  `equiv_BEQ` / `equiv_BNE` promise binder is a proof term, not a
  caller-supplied assumption, everywhere it appears in the global compliance
  closure.

### 3. Branch next-PC removal completed with #100 — DONE

`ZiskFv/Compliance/Pilot/BranchNextPC.lean::branch_nextPC_flag1_taken`
(BEQ polarity) / `branch_nextPC_flag0_taken` (BNE polarity) cast the
flag-dispatched Main PC mux

```
next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)
```

to the Sail conditional next-PC `if cmp then PC + signExtend imm else PC + 4`.
These rest on the accepted trace's in-circuit `pcHandshakeBetween` transition
certificate (`mainTransition_to_next_pc`) — the #100 cross-row handshake — not
a caller promise. **#100 is CLOSED.**

### 4. Zero new project axioms — DONE

- `trust/generated/baseline-axioms.txt`: `Total entries: 0` (0 project axioms
  in the source ledger).
- `trust/generated/baseline-equiv-axiom-deps.txt`: the per-theorem axiom
  closures `ZiskFv.Equivalence.Beq.equiv_BEQ` and
  `ZiskFv.Equivalence.Bne.equiv_BNE` both record an empty non-kernel
  dependency set.

## Why `equiv_BEQ` still carries a `nextPC_matches` binder — and why that is correct

`equiv_BEQ` / `equiv_BNE` live at the trace-agnostic EquivCore layer: they
relate Sail's `execute_instruction` to `bus_effect` over a raw `exec_row`
list, with no `AcceptedZiskTrace` in scope. The `nextPC_matches` binder on
`BranchPromises` is the **seam** between that layer and the trace-aware
dispatcher; it is fully discharged by `stepStrong_beq` / `stepStrong_bne`
(criterion 2 above).

Removing the binder from `equiv_BEQ` itself would require threading
`AcceptedZiskTrace` / `mainOfTable` / `execRowOf` and the transition
certificate up into `EquivCore/Beq.lean`, inverting the 3-layer tower for all
six branches (which share `BranchPromises` and the `OpEnvelope` dispatch
shape). That refactor changes nothing about trust — the closure is already at
0 axioms and the flag is already derived — so per the repository's
anti-laundering principle ("a PR that is net-zero on trust surface did not
discharge anything; it just moved the trust around") it is deliberately **not**
done. The seam is the correct location for the trace handshake.

## What this record does / does not do

- **Does:** record the criterion-by-criterion evidence and carry the
  `Closes #101` GitHub closure.
- **Does not:** add or remove any axiom, change any `equiv_<OP>` theorem
  statement, or touch the trust baselines. No Lean source changes accompany
  this record.
