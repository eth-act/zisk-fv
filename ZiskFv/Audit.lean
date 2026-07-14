import ZiskFv.Soundness
import ZiskFv.Completeness

/-!
# `ZiskFv.Audit` — the single audit surface

**This file *is* the audit surface. Everything else is implementation.**

An auditor should be able to open this one file and, without chasing into any
other module, read off:

1. the two root theorems — soundness and completeness — with their full types;
2. the one proven, unconditional completeness fact in this build (the Sail→shape
   bridge);
3. the exact axiom closure of each root theorem (the machine-checked trust
   ledger), frozen here as a golden test so that any stray `sorry`, or any newly
   introduced trusted premise, breaks the build rather than passing review
   silently;
4. a pretty-printed snapshot of each root statement, likewise frozen, so that an
   accidental change to what is *claimed* (not just what is *trusted*) also
   breaks the build.

This file re-states nothing new: it only `#check`s and `#print axioms` the
theorems proven elsewhere and pins their output. Updating any snapshot below is a
deliberate change to the public audit surface and must be explained in the PR
that does it.

Narrative trust boundary and known carve-outs live alongside this file:

* `trust/trusted-base.md` — the narrative trust boundary (extraction
  assumptions, the conditional Aeneas/memory-seed inputs, the current axiom
  ledgers under `trust/generated/`).
* `trust/defects.md` — the enumerated known defects excluded by the soundness
  scope (`RowOutsideDefectRegion`) and the completeness decode gap
  (`knownDecodeGap`).

## The two roots

* `ZiskFv.Compliance.root_soundness` (`ZiskFv/Soundness.lean`) — the advertised
  soundness endpoint. Every state transition of an `AcceptedZiskTrace` that
  avoids the enumerated defects agrees with the Sail RV64IM model. The older
  `ZiskFv.Compliance.zisk_riscv_compliant_program_bus` is an *internal* per-arm
  channel-balance lemma that `root_soundness` is built on; it is not the audit
  endpoint.
* `ZiskFv.Completeness.root_completeness` (`ZiskFv/Completeness.lean`) — the
  advertised completeness endpoint, dual to soundness: conditional on one
  `ZiskCompletenessObligations` record (honest and obvious from the type) until
  the Aeneas bridge lands.

## Trusted extraction (outside the Lean axiom ledger)

* Sail-to-Lean extraction for the official `riscv/sail-riscv` semantics.
* ZisK RV64IM circuit-to-Lean extraction from the flake-pinned ZisK/PIL inputs.
-/

/-! ## Statement snapshots (frozen)

A change to any of these means the *claim* changed; update the snapshot only in
the PR that deliberately changes what a root theorem states. -/

open ZiskFv.Compliance in
/--
info: root_soundness : ∀ (numInstructions : ℕ) (ziskTrace : AcceptedZiskTrace numInstructions)
  (sailTrace : SailTrace numInstructions) (ziskStep : (i : Fin numInstructions) → ZiskStep ziskTrace i)
  (programDecodes : (i : Fin numInstructions) → ProgramDecode ziskTrace i (ziskStep i))
  (inputsAgree : (i : Fin numInstructions) → InputsAgree ziskTrace sailTrace i (ziskStep i))
  (bootSeed : BootSegmentMemorySeed ziskTrace sailTrace ziskStep),
  (∀ (i : Fin numInstructions), RowOutsideDefectRegion ziskTrace i (ziskStep i)) →
    ∀ (i : Fin numInstructions), StepSound ziskTrace sailTrace i (ziskStep i)
-/
#guard_msgs (whitespace := lax) in
#check @root_soundness

open ZiskFv.Completeness in
/--
info: root_completeness : ∀ (state : SailDecode.SailState),
  SailDecode.IsaExtensionsEnabled state →
    ∀ (z : OutstandingZiskPredicates), ZiskCompletenessObligations z → EventualCompleteness state z
-/
#guard_msgs (whitespace := lax) in
#check @root_completeness

open ZiskFv.Completeness in
/--
info: sail_executable_within_supported_decode_shape : ∀ (state : SailDecode.SailState) (raw : SailDecode.RawInstruction),
  SailDecode.IsaExtensionsEnabled state →
    SailDecode.SailRv64imExecutableRawIn state raw → Rv64imShapes.SupportedDecodeShape raw
-/
#guard_msgs (whitespace := lax) in
#check @sail_executable_within_supported_decode_shape

/-! ## Axiom-closure golden tests (frozen)

Each `#print axioms` is pinned. A stray `sorry` (would add `sorryAx`) or a newly
introduced trusted premise anywhere below a root theorem changes this output and
breaks the build. The `riscv_*` / reservation / `plat_term_write` /
`get_16_random_bits` entries are the trusted Sail-extraction primitives; the
remaining `propext` / `Classical.choice` / `Lean.ofReduceBool` /
`Lean.trustCompiler` / `Quot.sound` are the standard permitted axioms. -/

open ZiskFv.Compliance in
/--
info: 'ZiskFv.Compliance.root_soundness' depends on axioms: [cancel_reservation, get_16_random_bits, load_reservation, match_reservation, plat_term_write, propext, riscv_f16Add, riscv_f16Div, riscv_f16Eq, riscv_f16Le, riscv_f16Le_quiet, riscv_f16Lt, riscv_f16Lt_quiet, riscv_f16Mul, riscv_f16MulAdd, riscv_f16Sqrt, riscv_f16Sub, riscv_f16ToF32, riscv_f16ToF64, riscv_f16ToI32, riscv_f16ToI64, riscv_f16ToUi32, riscv_f16ToUi64, riscv_f16roundToInt, riscv_f32Add, riscv_f32Div, riscv_f32Eq, riscv_f32Le, riscv_f32Le_quiet, riscv_f32Lt, riscv_f32Lt_quiet, riscv_f32Mul, riscv_f32MulAdd, riscv_f32Sqrt, riscv_f32Sub, riscv_f32ToBF16, riscv_f32ToF16, riscv_f32ToF64, riscv_f32ToI32, riscv_f32ToI64, riscv_f32ToUi32, riscv_f32ToUi64, riscv_f32roundToInt, riscv_f64Add, riscv_f64Div, riscv_f64Eq, riscv_f64Le, riscv_f64Le_quiet, riscv_f64Lt, riscv_f64Lt_quiet, riscv_f64Mul, riscv_f64MulAdd, riscv_f64Sqrt, riscv_f64Sub, riscv_f64ToF16, riscv_f64ToF32, riscv_f64ToI32, riscv_f64ToI64, riscv_f64ToUi32, riscv_f64ToUi64, riscv_f64roundToInt, riscv_i32ToF16, riscv_i32ToF32, riscv_i32ToF64, riscv_i64ToF16, riscv_i64ToF32, riscv_i64ToF64, riscv_ui32ToF16, riscv_ui32ToF32, riscv_ui32ToF64, riscv_ui64ToF16, riscv_ui64ToF32, riscv_ui64ToF64, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms root_soundness

open ZiskFv.Completeness in
/--
info: 'ZiskFv.Completeness.root_completeness' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms root_completeness

open ZiskFv.Completeness in
/--
info: 'ZiskFv.Completeness.sail_executable_within_supported_decode_shape' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sail_executable_within_supported_decode_shape
