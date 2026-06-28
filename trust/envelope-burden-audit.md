# OpEnvelope burden audit

This audit is the issue #61 three-bucket classification for the current
`OpEnvelope` surface. It covers the 65 `OpEnvelope` constructors in
`ZiskFv/Compliance/OpEnvelope.lean`, which cover the 63 canonical RV64IM
opcode theorems plus the `auipc_x0` and `jal_x0` no-rd-write route variants.
The route-named constructors are the seven documented in
`trust/op-envelope-route-constructors.txt`.

Inputs reviewed:

- `ZiskFv/Compliance/OpEnvelope.lean`
- `ZiskFv/Compliance.lean`
- `ZiskFv/Compliance/AeneasBridgeTrust.lean`
- `ZiskFv/Compliance/Defects.lean`
- `ZiskFv/Compliance/SharedBundles.lean`
- `ZiskFv/EquivCore/Promises/*.lean`
- `trust/envelope-surface-add.md`
- `trust/generated/baseline-caller-burden.txt` (63 canonical theorems, 1062 rows)
- `trust/generated/baseline-wrapper-caller-burden.txt` (63 wrappers, 1117 rows)

Buckets:

- (a) Derivable by the construction theorem from accepted trace data:
  component constraints, selected rows, channel balance, static tables, and
  named trace-level premises such as program binding and machine-profile
  invariants.
- (b) Genuine named top-level premise for the trace-level theorem: boot/profile
  assumptions, program binding, `aeneasBridgeTrust`, load memory timeline until
  #76, and `Defects.NoKnownDefect`.
  - (b)-pending-infrastructure: a *real* semantic fact that is a named premise
    only because the live formal model cannot yet represent the source
    constraint. Historically, the next-PC / cross-row PC handshake was the
    canonical case; #100 discharges it via accepted-trace certificates (see the
    cross-row note below).
- (c) Neither: constructor-carried facts that are not consequences of
  constraints/channel balance and should not appear as standalone public
  assumptions. This includes both the subword-store preserved-byte RMW facts
  and the execution-bus shape artifacts (`exec_len`/`e0_mult`/`e1_mult`), the
  latter being pure `bus_effect` bookkeeping with no ZisK circuit counterpart.

## Result

Most constructor fields are bucket (a): they are selected trace data, row
membership, lookup/table soundness, bus entry matching, finite arithmetic
facts, or promise-bundle projections. The public theorem still needs bucket (b)
premises for the Rust/Aeneas lowering boundary, the memory replay boundary, the
machine profile, program binding, and known-defect exclusions.

Bucket (c) is not empty. It now holds **two** classes of constructor-carried
facts that are not consequences of constraints/channel balance:

1. **Subword-store preserved bytes.** The sub-doubleword store constructors
   (`sb`, `sh`, `sw`) expose high-byte read-modify-write facts (`h_m1` through
   `h_m7`, with the width-specific subset per opcode) that are not covered by
   the current named load-only `OpEnvelope.memoryTimelineEvidence`. These facts
   should be folded into the #76 memory replay/timeline construction or replaced
   by a named memory-replay premise that covers store events; they should not
   become per-store public premises. (Recorded on #61 via PR #83.)
2. **Execution-bus shape artifacts.** The branch and FENCE constructors carry
   `exec_len`/`e0_mult`/`e1_mult` (and the underlying `exec_row`) — assertions
   about a phantom `Interaction.ExecutionBusEntry` list with no ZisK circuit
   counterpart. This class was previously misclassified as bucket-(a) and is
   corrected here (P4-PR1 / RESEARCH_PR94_CLOSEOUT.md). See the exec-row
   bucket-(c) section below; it is the same category as class 1, not a parallel
   audit axis.

The previously bucket-(a) "PC/nextPC bus bridge" entry was separately tracked as
bucket-(b)-pending-infrastructure, not bucket-(c), because `nextPC` is a real
semantic effect rather than an exec-bus bookkeeping artifact. #100 discharges
that premise via accepted-trace PC-transition certificates; see the cross-row
note below.

## Bucket (b) Premises

| Premise class | Current surface | Final trace-level role |
|---------------|-----------------|------------------------|
| Program binding and decode | Pure input records, `r1`/`r2`/`rd`/`imm`/`shamt`/`fm`/`pred`/`succ`, opcode pins | Named `ProgramBinding`/decode premise; constructor projections should be generated |
| Boot/profile state | `misa` C-bit facts, `cur_privilege = Machine`, `RISC_V_assumptions`, `ModeRegsFull`, PMA/mstatus/mseccfg values | Named initial-state/profile invariant; not 63 separate assumptions |
| Aeneas lowering bridge | `env.aeneasBridgeTrust` in `Compliance.lean` | Named bridge premise until generated Aeneas Lean is imported by the main proof |
| Load memory timeline | `env.memoryTimelineEvidence` for LD/LBU/LHU/LWU/LB/LH/LW routes | Named memory premise until #76 derives it from Mem AIR/replay |
| Known defects | `Defects.NoKnownDefect env` | Named claim-weakening premise until signed MUL, signed DIV/REM, and FENCE defects retire |

The raw `False` binders that still appear in the legacy signed-MUL and
signed-DIV/REM wrappers are not `OpEnvelope` fields. The global theorem obtains
them only by applying `Defects.NoKnownDefect`, so the trace-level statement
should expose the named defect predicate, not raw contradictions.

## Field-Shape Classification

| Field shape | Examples | Bucket | Disposition |
|-------------|----------|--------|-------------|
| Data records and operands | `PureSpec.*Input`, `BranchInstrOperands`, `ModeRegsFull`, `BusRows`, `r1`, `r2`, `rd`, `imm`, `shamt`, `misa_val`, `mseccfg` | (a)/(b source) | Data is selected from the accepted trace; program/profile meaning comes from named bucket-(b) premises |
| Main row activation and opcode pins | `MainRowPins`, `h_flag`, `h_m32`, `h_set_pc`, `h_store_pc`, `row_mode`, jump/FENCE mode pins | (a) except defect/profile pins | Derived from Main constraints, decode, and Aeneas-backed row lowering; FENCE good-shape restriction is `NoKnownDefect` |
| Provider validators and row indices | `Valid_Binary`, `Valid_BinaryExtension`, `Valid_Mem`, `Valid_ArithMul`, `Valid_ArithDiv`, `r_main`, `r_mem`, `r_a`, `r_binary` | (a) | Selected by the accepted trace and channel-balance witnesses |
| Static lookup witnesses | `providerTable`, `providerRow`, `h_component`, `h_table_spec`, `h_provider_row`, `StaticLookupSoundness`, `Arith*TableWitness` | (a) | Derivable from component constraints and lookup-aware Clean soundness |
| Operation-bus matches | `h_match_static`, `h_match_primary`, `h_match_secondary`, `h_msg`, Main/Mem provider interaction equality | (a) | Derivable from channel balance plus selected provider rows |
| Memory-bus entry matches | `StorePcMemoryWitness`, `ExternalArithMemoryWitness`, `h_main_b_match`, `h_main_c_match`, `register_write_lanes_match` | (a) | Derivable from Main/Mem row constraints and memory-bus channel balance |
| Promise bundles | `RTypePromises`, `ITypePromises`, `BranchPromises`, `UTypePromises`, `JumpPromises`, `Shift*Promises`, `LoadStructuralPromises`, `StorePromises`, `FencePromises` | (a)/(b source) | Bus shape and register/PC bridges are generated; embedded profile facts are projections of named boot/profile premises |
| Pure/state bridge equalities | `input_r1_eq`, `input_r2_eq`, `input_pc_eq`, `h_input_rs1`, `h_cur_privilege`, `h_mseccfg`, `h_input_imm`, `h_not_throws` | (a)/(b source) | Construct input records from state/program data; privilege/profile facts come from bucket (b) profile invariant |
| Arithmetic row facts and ranges | `h_row_constraints`, `ByteBounds`, `Arith*ChunkRangeWitness`, `Arith*CarryRangeWitness`, `h_rs*_value`, `h_a23`, `h_b23`, `h_c23`, `h_sext_choice`, `h_na_bool`, `h_nb_bool`, `h_nr_bool`, `h_np_xor`, `remainder_bound` | (a), with defect-gated exceptions | Unsigned paths are constructive today; signed defect paths remain under `NoKnownDefect` until repaired |
| Load memory timeline | `OpEnvelope.memoryTimelineEvidence` for load arms; `LoadStructuralPromises.withMemoryTimelineEvidence` in dispatch | (b) now, (a) after #76 | Named residual memory boundary |
| Subword-store preserved bytes | `sb.h_m1..h_m7`, `sh.h_m2..h_m7`, `sw.h_m4..h_m7` | (c) | See bucket-(c) finding (class 1) below |
| Execution-bus shape artifacts | branch/FENCE `exec_row`, `h_exec_len`, `h_e0_mult`, `h_e1_mult` | (c) | Phantom `Interaction.ExecutionBusEntry` bookkeeping; no ZisK bus carries it. See exec-row bucket-(c) section (class 2) below |
| PC / next-PC bus bridge | former `h_nextPC_matches`, PC handshake | discharged via #100 | Real semantic effect; now derived from accepted-trace PC-transition certificates + per-op decode/provenance. See cross-row note below |

## Per-Family Classification

| Family / constructors | Bucket (a) constructor burden | Bucket (b) premise source | Bucket (c) |
|-----------------------|-------------------------------|---------------------------|------------|
| Branch: `beq`, `bne`, `blt`, `bge`, `bltu`, `bgeu` | Branch input, operands, Main row pins | Program binding; `misa.C = 0` as profile invariant; `aeneasBridgeTrust` until imported; next-PC now discharged by #100 accepted-trace certificates | exec-row shape facts (`exec_len`/`e0_mult`/`e1_mult`); see exec-row bucket-(c) section |
| FENCE: `fence` | `MainRowPins`, PC bus shape | Machine privilege/profile; `NoKnownDefect` restricts to ZisK's known-good FENCE shape; next-PC now discharged by #100 accepted-trace certificates | `exec_row` exec-bus shape facts; see exec-row bucket-(c) section |
| U/J control flow: `lui`, `auipc`, `auipc_x0`, `jal`, `jal_x0`, `jalr` | Store-PC memory witness, row provenance, subset facts, PC/offset finite arithmetic, no-write variants | Program binding; `misa`, privilege, and `mseccfg` profile facts; `aeneasBridgeTrust` | None |
| Binary/Add/ITYPE: `add_via_binary`, `addi_via_binary`, `addw`, `subw`, `addiw`, `sub`, `and`, `or`, `xor`, `slt`, `sltu`, `andi`, `ori`, `xori`, `slti`, `sltiu` | Static Binary lookup table, provider row, operation-bus match, input-lane bridges, write-lane bridge, R/I-type promises | Program binding and Aeneas bridge | None |
| Shift: `sll`, `srl`, `sra`, `slli`, `srli`, `srai`, `sllw`, `srlw`, `sraw`, `slliw`, `srliw`, `sraiw` | Static BinaryExtension lookup, shift amount pins, R/shift promise bundles or expanded W-form promise fields | Program binding and Aeneas bridge | None |
| Stores: `sd` | Main c/store row, `StorePromises`, store-PC zero, address bridge, store byte lanes | Program/profile assumptions for Sail store semantics | None |
| Stores: `sb`, `sh`, `sw` | Same Main c/store row facts as `sd`, plus opcode width pins and low written-byte lanes | Program/profile assumptions for Sail store semantics | Preserved high-byte memory facts, listed below |
| Loads: `ld`, `lbu`, `lhu`, `lwu`, `lb_via_static_match`, `lh_via_static_match`, `lw_via_static_match` | Main b/c rows, Mem provider row, `Valid_Mem`, MemAlign witnesses for narrow zero-extend loads, BinaryExtension sign-extension provider for LB/LH/LW, address and rd-index facts | `memoryTimelineEvidence` until #76; program/profile assumptions | None beyond the named memory premise |
| ArithMul unsigned/non-defect: `mulhu`, `mulw` | ArithMul row constraints, table/range/carry witnesses, op-bus match, external-arith memory witness, operand/result packing facts | Program binding and Aeneas bridge | None |
| ArithMul signed defect-gated: `mul`, `mulh`, `mulhsu` | Constructor fields are ordinary row/table/bus facts, but dispatch false-eliminates from `NoKnownDefect` | `NoKnownDefect` excludes the current signed-MUL defect region | None under current defect-qualified theorem |
| ArithDiv unsigned/non-defect: `divu`, `divuw`, `remu`, `remuw` | ArithDiv row constraints, table/range/carry/remainder witnesses, op-bus match, external-arith memory witness, operand/result packing facts | Program binding and Aeneas bridge | None |
| ArithDiv signed defect-gated: `div`, `divw`, `rem`, `remw` | ArithDiv row + sign facts; divisor-zero/overflow handled in-model — `div`/`divw` consume `div_boundary_constraints` (row-local flag machinery, `arith.pil` 0–30), `rem`/`remw` derive it from the carry-chain identity; the `h_op2_ne`/`h_no_overflow` caller promises are retired (#114). Dispatch defect-qualified | `NoKnownDefect` excludes the current signed-DIV/REM defect region | None under current defect-qualified theorem |

## Bucket-(c) Finding, class 1: Subword Store Preserved Bytes

`OpEnvelope.sb`, `OpEnvelope.sh`, and `OpEnvelope.sw` carry the preserved
high-byte facts that let Sail's byte/halfword/word store update be compared to
ZisK's 8-lane memory-bus store entry:

- `sb`: `h_m1`, `h_m2`, `h_m3`, `h_m4`, `h_m5`, `h_m6`, `h_m7`
- `sh`: `h_m2`, `h_m3`, `h_m4`, `h_m5`, `h_m6`, `h_m7`
- `sw`: `h_m4`, `h_m5`, `h_m6`, `h_m7`

Each fact has shape `state.mem[bus.e2.ptr.toNat + i]? = some (byteAt bus.e2 i :
BitVec 8)` for a byte lane not overwritten by the narrow store. It assumes that
the store event's preserved byte lanes already agree with Sail memory before
the store.

This is not derivable from Main row constraints or channel balance alone. Those
facts determine the store pointer and the low written bytes, but they do not by
themselves connect the pre-store Sail memory map to the high lanes of the
memory-bus event. It is also not a defensible final public premise to ask the
trace theorem caller for per-store preserved-byte equalities.

Disposition: move this burden into the memory replay construction. The right
target is either an extension of `OpEnvelope.memoryTimelineEvidence` to store
events or, preferably, #76 deriving the store replay step from Mem AIR accepted
rows so these facts become bucket (a). Until then, the trace-level theorem
should not claim that all store-memory facts have been hidden behind named
public premises.

## Bucket-(c) Finding, class 2: Execution-Bus Shape Artifacts

This is the same bucket-(c) category as class 1 (subword-store preserved bytes
above) — a constructor-carried fact that is not a consequence of constraints or
channel balance — applied to the branch and FENCE control-flow constructors.
Source: P4-PR1 / `docs/ai/plan/RESEARCH_PR94_CLOSEOUT.md`. It corrects an earlier
bucket-(a) classification (the per-family rows above listed branch/FENCE
"exec-row shape" as derivable bucket-(a) burden; that was aspirational and false
against the live ensemble).

The branch and FENCE constructors carry `exec_row : List
(Interaction.ExecutionBusEntry FGL)` and the shape assertions `h_exec_len`,
`h_e0_mult`, `h_e1_mult` over it. These have **no ZisK circuit counterpart**:

- `Interaction.ExecutionBusEntry` is a legacy port. Its file docstring states it
  is a "Minimal ZisK port of `OpenvmFv/Fundamentals/Interaction.lean`"
  (`ZiskFv/Airs/Bus/Interaction.lean:5`), and the structure itself
  (`Interaction.lean:41`) notes the RV32 (openvm-fv) and RV64 (zisk-fv) shapes
  coincide (`Interaction.lean:38`). It is an openvm import, not a ZisK bus
  message.
- **ZisK has exactly three buses**, none of them an execution bus:
  `OPERATION_BUS_ID = BusId(0)` (`zisk/common/src/bus/data_bus_operation.rs:11`),
  `ROM_BUS_ID = BusId(1)` (`zisk/common/src/bus/data_bus_rom.rs:9`), and
  `MEM_BUS_ID = BusId(2)` (`zisk/common/src/bus/data_bus_mem.rs:5`). The
  operation-bus payload is `[op, op_type, a, b]`
  (`data_bus_operation.rs:366`) — no PC, no next-PC, no execution-bus shape.
- The live Clean ensemble (`fullRv64imEnsemble`) finishes only the OpBus and
  MemBus channels; nothing in the formal model wires `exec_row` to any channel
  or constraint. The `h_exec_len`/`h_e0_mult`/`h_e1_mult` facts only gate the
  structural `if` inside the `bus_effect` interpreter — they assert the shape of
  a list the real Clean circuit never produces.

Disposition: these are **pure artifacts** of the `bus_effect` /
`Interaction.ExecutionBusEntry` conclusion form. They carry no real-circuit
content and cannot be derived from the accepted trace, because there is no trace
object to derive them from. They are **eliminated** (not derived, not named-as-a-
real-premise) when the canonical conclusion is restated off the foreign openvm
`bus_effect` onto the ZisK-native channels — a tracked, lower-priority retirement
(P6-style negative-diff campaign over the 63-opcode shared conclusion form). Until
then they remain explicit named residuals, honestly classified as bucket-(c)
artifacts rather than bucket-(a) derivations.

## Cross-row note: PC / next-PC — DISCHARGED (#100, 2026-06-27)

> **UPDATE (#100 landed):** `h_nextPC_matches` is now **DISCHARGED for all 63
> opcodes** and is no longer a residual. It is derived from a new accepted-trace
> certificate `AcceptedZiskTrace.transitions_hold` (the `main.pil:409-410`
> cross-row PC-handshake polynomial constraint, brought into the model via an
> additive `Air.Flat.Component.transition` field) plus per-op decode pins + the
> existing PC-provenance bridge — NOT from `constraints_hold`. This is an honest
> **trust-surface SHIFT** (cross-world promise → in-circuit certificate +
> dischargeable decode), documented in `trust/trusted-base.md` →
> "Accepted-Trace Certificates", including the within-segment `i+1 < length`
> boundary (final-row next-PC = cross-segment #103). The historical analysis
> below records the pre-#100 state.

`h_nextPC_matches` (branch / FENCE / jump next-PC) is the **one semantically
real** fact in the exec-bus cluster: `bus_effect` writes `Register.nextPC` and
this equates it to the Sail next-PC. Unlike the exec-row artifacts, it is not an
artifact to be eliminated — it is a real effect. ~~But it is **not derivable from
the live ensemble today**~~ (pre-#100), so it *was* reclassified from bucket-(a) to
**bucket-(b)-pending-infrastructure** for **every** opcode (not just branches);
sequential next-PC = `pc + 4` is *also* a cross-row property.

The blocker is a **cross-row ceiling** in the live model:

- The live `Air.Flat.Component` model evaluates each row independently. The
  component is defined as "one circuit whose constraints are checked
  independently on each row. There are no direct adjacent-row constraints"
  (`build/clean-lean/Clean/Air/FlatComponent.lean:7-10`), and
  `Table.environment row = Environment.fromArray row table.data`
  (`FlatComponent.lean:149-150`) is built from a **single row**;
  `EnsembleWitness.Constraints` ranges over `∀ row, … ConstraintsHold
  (environment row)` (`FlatComponent.lean:171-172`). There is no `Var` that
  reaches `row-1`.
- The live Clean Main component is deliberately single-row: its header states
  "Cross-row pc_handshake stays in Bridge as a separate adjacency theorem" and
  it emits only the 9 per-row asserts plus channels
  (`ZiskFv/AirsClean/Main/Constraints.lean:12-13`).
- The cross-row PC-transition constraint (`constraint_18`) **is** extracted, but
  only into the dead legacy `[Circuit F ExtF C]` model
  (`build/extraction/Extraction/Main.lean:97`,
  `constraint_18_every_row`, parameterized over the legacy typeclass) — and
  nothing under `ZiskFv/` imports `Extraction.*`. Before #100, `constraint_18`
  was **not** in `trace.constraints` and `pc_handshake` was **not** derivable.

Returning `h_nextPC_matches` to bucket-(a) required a foundational cross-row
capability for the Clean ensemble (a rotation-capable component or shadow-column
encoding), plus branch flag aggregation. #100 takes the accepted-trace certificate
route documented in `trust/trusted-base.md` rather than deriving it from
`constraints_hold`. This historical audit originally recorded next-PC as an
explicit named premise with a tracked prerequisite.

## Non-Findings

Load byte agreement is not bucket (c) anymore. It is exposed as
`OpEnvelope.memoryTimelineEvidence` and threaded through
`LoadStructuralPromises.withMemoryTimelineEvidence`, so it is bucket (b) until
#76 derives it.

The signed MUL and signed DIV/REM contradiction binders in wrappers are not
bucket (c) constructor fields. They are legacy wrapper surfaces reached from
the global theorem only through `Defects.NoKnownDefect`. When those defects are
retired, the relevant arithmetic operand/sign/range fields must move to bucket
(a), not become new public premises.
