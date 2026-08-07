import ZiskFv.Soundness
import ZiskFv.Completeness

/-!
# `ZiskFv.Audit` — the audit surface

One file an auditor can open to read off, without chasing into any other module:

1. the soundness endpoint and the completeness endpoints, with their full types;
2. the exact axiom closure of each — the machine-checked trust ledger;
3. both of the above frozen as golden tests, so that a stray `sorry`, a newly
   introduced trusted premise, or a silent change to what is *claimed* breaks
   `lake build` rather than passing review unnoticed.

This file re-states nothing new: it only `#check`s and `#print axioms` theorems
proven elsewhere and pins their output. Updating a snapshot below is a deliberate
change to the public audit surface and must be explained in the PR that does it.

## Relation to the trust gate

`trust/scripts/check-strong-export-{binders,closure}.sh` already freeze
`root_soundness`' binder list and its `ZiskFv.*` project-axiom closure. This file
is not a replacement for them; it adds three things they do not cover:

* it fires during `lake build`, not in a separate olean-consuming script run;
* it pins the *full* closure (Lean kernel axioms and the Sail-translated
  primitives included), not only the `ZiskFv.*` entries;
* it covers the completeness endpoints, which have no script gate at all.

## Narrative boundary

* `trust/trusted-base.md` — the narrative trust boundary: extraction
  assumptions, the conditional Aeneas and memory-seed inputs, and the current
  ledgers under `trust/generated/`.
* `trust/defects.md` — the enumerated known defects excluded from the soundness
  scope (`RowOutsideDefectRegion`) and the completeness decode gap
  (`knownDecodeGap`).

## The endpoints

* `ZiskFv.Compliance.root_soundness` (`ZiskFv/Soundness.lean`) — the advertised
  soundness endpoint. Every state transition of an `AcceptedZiskTrace` that
  avoids the enumerated defects agrees with the Sail RV64IM model.
  `ZiskFv.Compliance.zisk_riscv_compliant_program_bus` is the *internal* per-arm
  channel-balance lemma it consumes, not the endpoint.
* `ZiskFv.Completeness.sail_executable_within_supported_decode_shape` — the one
  unconditional completeness fact in this build: every Sail-executable RV64IM
  raw word lands in the hand-written `SupportedDecodeShape` enumeration. It
  asserts nothing about ZisK.
* `ZiskFv.Completeness.skeletal_root_completeness` — the end-to-end acceptance
  statement, honestly conditional on the five ZisK obligation predicates until
  the Aeneas bridge lands.

## Trusted extraction (outside the Lean axiom ledger)

* Sail-to-Lean extraction for the official `riscv/sail-riscv` semantics.
* ZisK RV64IM circuit-to-Lean extraction from the flake-pinned ZisK/PIL inputs.
-/

/-! ## Statement snapshots (frozen)

A change here means the *claim* changed; update a snapshot only in the PR that
deliberately changes what an endpoint states. -/

open ZiskFv.Compliance in
/--
info: root_soundness : ∀ (numInstructions rawLength : ℕ) (ziskTrace : AcceptedZiskTrace numInstructions)
  (sailTrace : SailTrace numInstructions) (ziskStep : (i : Fin numInstructions) → ZiskStep ziskTrace i)
  (start : Fin rawLength → Fin ziskTrace.programLength) (addr : Fin rawLength → Fin 18446744069414584321)
  (rawProgram : Fin rawLength → BitVec 32)
  (programBinding : RawProgramBinding.ProgramRowsBinding ziskTrace start addr rawProgram)
  (rawProgramDecodes : (i : Fin numInstructions) → RawProgramDecode ziskTrace i (ziskStep i) start addr rawProgram)
  (inputsAgree : (i : Fin numInstructions) → InputsAgree ziskTrace sailTrace i (ziskStep i))
  (bootSeed : BootSegmentMemorySeed ziskTrace sailTrace ziskStep),
  (∀ (i : Fin numInstructions), RowOutsideDefectRegion ziskTrace i (ziskStep i)) →
    ∀ (i : Fin numInstructions),
      StepSound ziskTrace sailTrace i (ziskStep i)
        (rowDecode_of_programDecode ziskTrace i
          (programDecode_of_rawProgramDecode ziskTrace i (ziskStep i) start addr rawProgram programBinding
            (rawProgramDecodes i)))
-/
#guard_msgs (whitespace := lax) in
#check @root_soundness

open ZiskFv.Completeness in
/--
info: sail_executable_within_supported_decode_shape : ∀ (state : SailDecode.SailState) (raw : SailDecode.RawInstruction),
  SailDecode.IsaExtensionsEnabled state →
    SailDecode.SailRv64imExecutableRawIn state raw → Rv64imShapes.SupportedDecodeShape raw
-/
#guard_msgs (whitespace := lax) in
#check @sail_executable_within_supported_decode_shape

open ZiskFv.Completeness in
/--
info: skeletal_root_completeness : ∀ (state : SailDecode.SailState),
  SailDecode.IsaExtensionsEnabled state →
    ∀ (z : OutstandingZiskPredicates),
      z.decoderAcceptsInShape →
        z.loweringTotal → z.rowTotal → z.opcodeTotal → z.soundnessContract → EventualCompleteness state z
-/
#guard_msgs (whitespace := lax) in
#check @skeletal_root_completeness

/-! ## Axiom-closure snapshots (frozen)

Each `#print axioms` is pinned. A stray `sorry` (which would add `sorryAx`) or a
newly introduced trusted premise anywhere below an endpoint changes this output
and breaks the build. The `riscv_*` / reservation / `plat_term_write` /
`get_16_random_bits` entries are the trusted Sail-extraction primitives; the
remaining `propext` / `Classical.choice` / `Quot.sound` / `Lean.ofReduceBool` /
`Lean.trustCompiler` entries are the standard permitted Lean axioms. -/

/--
info: 'ZiskFv.Compliance.root_soundness' depends on axioms: [cancel_reservation,
 get_16_random_bits,
 load_reservation,
 match_reservation,
 plat_term_write,
 propext,
 riscv_f16Add,
 riscv_f16Div,
 riscv_f16Eq,
 riscv_f16Le,
 riscv_f16Le_quiet,
 riscv_f16Lt,
 riscv_f16Lt_quiet,
 riscv_f16Mul,
 riscv_f16MulAdd,
 riscv_f16Sqrt,
 riscv_f16Sub,
 riscv_f16ToF32,
 riscv_f16ToF64,
 riscv_f16ToI32,
 riscv_f16ToI64,
 riscv_f16ToUi32,
 riscv_f16ToUi64,
 riscv_f16roundToInt,
 riscv_f32Add,
 riscv_f32Div,
 riscv_f32Eq,
 riscv_f32Le,
 riscv_f32Le_quiet,
 riscv_f32Lt,
 riscv_f32Lt_quiet,
 riscv_f32Mul,
 riscv_f32MulAdd,
 riscv_f32Sqrt,
 riscv_f32Sub,
 riscv_f32ToBF16,
 riscv_f32ToF16,
 riscv_f32ToF64,
 riscv_f32ToI32,
 riscv_f32ToI64,
 riscv_f32ToUi32,
 riscv_f32ToUi64,
 riscv_f32roundToInt,
 riscv_f64Add,
 riscv_f64Div,
 riscv_f64Eq,
 riscv_f64Le,
 riscv_f64Le_quiet,
 riscv_f64Lt,
 riscv_f64Lt_quiet,
 riscv_f64Mul,
 riscv_f64MulAdd,
 riscv_f64Sqrt,
 riscv_f64Sub,
 riscv_f64ToF16,
 riscv_f64ToF32,
 riscv_f64ToI32,
 riscv_f64ToI64,
 riscv_f64ToUi32,
 riscv_f64ToUi64,
 riscv_f64roundToInt,
 riscv_i32ToF16,
 riscv_i32ToF32,
 riscv_i32ToF64,
 riscv_i64ToF16,
 riscv_i64ToF32,
 riscv_i64ToF64,
 riscv_ui32ToF16,
 riscv_ui32ToF32,
 riscv_ui32ToF64,
 riscv_ui64ToF16,
 riscv_ui64ToF32,
 riscv_ui64ToF64,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ZiskFv.Compliance.root_soundness

/--
info: 'ZiskFv.Completeness.sail_executable_within_supported_decode_shape' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ZiskFv.Completeness.sail_executable_within_supported_decode_shape

/--
info: 'ZiskFv.Completeness.skeletal_root_completeness' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ZiskFv.Completeness.skeletal_root_completeness
