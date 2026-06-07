import ZiskFv.Compliance.Dispatch.Branch
import ZiskFv.Compliance.Dispatch.NoMemOrSimple
import ZiskFv.Compliance.Dispatch.RTYPE
import ZiskFv.Compliance.Dispatch.ITYPE
import ZiskFv.Compliance.Dispatch.Shift
import ZiskFv.Compliance.Dispatch.ADD_RTYPEW
import ZiskFv.Compliance.Dispatch.LDSD
import ZiskFv.Compliance.Dispatch.DIVU
import ZiskFv.Compliance.Dispatch.Misc
import ZiskFv.Compliance.Dispatch.Remaining
import ZiskFv.Compliance.Defects

/-!
# Compliance.lean — unified channel-balance global theorem

This file aggregates the ten per-family dispatchers in
`Compliance/Dispatch/` into the global theorem
`zisk_riscv_compliant_program_bus`.

`OpEnvelope.exec_eq` is the conjunction of the ten per-family
conclusions. For any `OpEnvelope` arm, *exactly one* family's
`exec_eq_<family>` produces the real channel-balance statement; the
others return `True`. The conjunction is therefore exactly "this
arm's channel-balance statement holds". `zisk_riscv_compliant_program_bus`
proves the conjunction by invoking each dispatcher in turn.

## Coverage

All 63 RV64IM opcode arms are covered with a real (non-`True`)
channel-balance statement, partitioned across the ten dispatchers:

| Dispatcher (`Compliance/Dispatch/`) | Arms                                       |
|-------------------------------------|--------------------------------------------|
| `Branch`        | BEQ, BNE, BLT, BGE, BLTU, BGEU (6)                            |
| `NoMemOrSimple` | LUI, AUIPC, FENCE (3)                                        |
| `RTYPE`         | SUB, AND, OR, XOR, SLT, SLTU (6)                             |
| `ITYPE`         | ANDI, ORI, XORI, SLTI, SLTIU (5)                             |
| `Shift`         | SLL, SRL, SRA, SLLI, SRLI, SRAI (6)                          |
| `ADD_RTYPEW`    | ADD, ADDW, SUBW (3)                                          |
| `LDSD`          | LD, SD (2)                                                   |
| `DIVU`          | DIVU (1)                                                     |
| `Misc`          | LB, LH, LW, ADDI, ADDIW (5)                                  |
| `Remaining`     | the remaining 26 (loads/stores/W-shifts/Mul/Div/Rem/JAL/JALR)|

## Trust note

No new axioms — the closure is exactly the union of the 63 wrappers'
closures plus the trivial `state_effect_via_channels_eq_bus_effect_2`
bridge. The V2 trust gate enforces this.

`zisk_riscv_compliant_program_bus` is the single public global theorem. It is
conditional on `OpEnvelope.completenessBurden`, which marks that the theorem
starts from an already-constructed envelope rather than proving accepted-trace
completeness. Load-memory replay evidence is exposed separately through
`OpEnvelope.AcceptedFullExecutionMemoryTraceAtEnvelope` and
`OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope`: load
arms carry a shared accepted full-execution memory trace plus per-envelope
selected prefix and selected Mem-row coverage, while non-load arms carry no
memory trace data. The accepted trace construction includes the duplicate-free
memory-row invariant used to derive selected occurrence uniqueness internally.
The theorem derives the load-scoped construction package, generated Mem burden,
and replay construction internally.
It is also defect-aware while
`trust/defects.md` contains open claim-weakening defects: the `h_known_bugs`
binder is orthogonal to the validity witnesses already bundled in
`OpEnvelope`. Validity says the current modeled constraints hold;
`h_known_bugs` says this envelope is not inside a ledgered defect region.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

/-- Unified per-arm conclusion: conjunction of the ten family-
    specific `exec_eq_<family>` Props. Exactly one family fires
    non-trivially for any given arm; the others are `True`. -/
def OpEnvelope.exec_eq (env : OpEnvelope state m r_main) : Prop :=
  env.exec_eq_branch
    ∧ env.exec_eq_nomem
    ∧ env.exec_eq_rtype_binary
    ∧ env.exec_eq_itype_binary
    ∧ env.exec_eq_shift
    ∧ env.exec_eq_add_rtypew
    ∧ env.exec_eq_ldsd
    ∧ env.exec_eq_divu
    ∧ env.exec_eq_misc
    ∧ env.exec_eq_remaining

/-- **Known-defect-aware channel-balance global theorem.**

    The memory input is exactly the accepted AIR/Main/Mem trace construction
    for the selected envelope. This is the point where the load replay proof
    actually starts: generated Mem facts, chronological rows, prefix read
    soundness, initial memory agreement, and the selected prefix cursor are
    already present in `construction`. -/
theorem zisk_riscv_compliant_program_bus
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (construction : env.AcceptedAirMainMemFullTraceConstructionAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq := by
  obtain ⟨_h_row_burden, _h_table_provider_burden, _h_route_burden⟩ :=
    h_burden
  have h_generated_mem_trace :
      env.GeneratedMemFullTraceConstructionAtEnvelope :=
    env.generatedMemFullTraceConstructionAtEnvelope_of_acceptedAirMainMemTrace
      construction
  have h_mem_rows_construction :
      env.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope :=
    env.acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_generatedTraceAtEnvelope
      h_generated_mem_trace
  have h_mem_rows_trace : env.AcceptedFullMemoryBusRowsTraceAtEnvelope :=
    env.acceptedFullMemoryBusRowsTraceAtEnvelope_of_construction
      h_mem_rows_construction
  have h_full_mem_bus_trace : env.AcceptedFullMemoryBusTraceAtEnvelope :=
    env.acceptedFullMemoryBusTraceAtEnvelope_of_rowsTraceAtEnvelope
      h_mem_rows_trace
  have h_mem_execution_trace : env.AcceptedMemoryBusExecutionTraceAtEnvelope :=
    env.acceptedMemoryBusExecutionTraceAtEnvelope_of_fullTraceAtEnvelope
      h_full_mem_bus_trace
  have h_full_mem_trace : env.AcceptedFullMemoryTraceAtEnvelope :=
    env.acceptedFullMemoryTraceAtEnvelope_of_memoryBusExecutionTraceAtEnvelope
      h_mem_execution_trace
  have h_memory_burden : env.memoryBurden :=
    env.memoryBurden_of_acceptedFullMemoryTraceAtEnvelope h_full_mem_trace
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zisk_riscv_compliant_program_bus_branch env
  · exact zisk_riscv_compliant_program_bus_nomem env
  · exact zisk_riscv_compliant_program_bus_rtype_binary env
  · exact zisk_riscv_compliant_program_bus_itype_binary env
  · exact zisk_riscv_compliant_program_bus_shift env
  · exact zisk_riscv_compliant_program_bus_add_rtypew env
  · exact zisk_riscv_compliant_program_bus_ldsd env h_memory_burden
  · exact zisk_riscv_compliant_program_bus_divu_except_known_defects env h_known_bugs
  · exact zisk_riscv_compliant_program_bus_misc env h_memory_burden
  · exact zisk_riscv_compliant_program_bus_remaining env h_memory_burden h_known_bugs

/-- Generated Mem construction variant of the known-defect-aware global
    theorem.

    This exposes what the current replay proof actually consumes: generated
    Mem trace construction plus the selected prefix cursor. The accepted
    AIR/Main/Mem provenance wrappers above this theorem remain useful
    integration targets, but the load replay proof itself only needs this
    generated construction boundary. -/
theorem zisk_riscv_compliant_program_bus_of_generatedMemFullTraceConstructionAtEnvelope
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (generatedConstruction :
      env.GeneratedMemFullTraceConstructionAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq := by
  obtain ⟨_h_row_burden, _h_table_provider_burden, _h_route_burden⟩ :=
    h_burden
  have h_mem_rows_construction :
      env.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope :=
    env.acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_generatedTraceAtEnvelope
      generatedConstruction
  have h_mem_rows_trace : env.AcceptedFullMemoryBusRowsTraceAtEnvelope :=
    env.acceptedFullMemoryBusRowsTraceAtEnvelope_of_construction
      h_mem_rows_construction
  have h_full_mem_bus_trace : env.AcceptedFullMemoryBusTraceAtEnvelope :=
    env.acceptedFullMemoryBusTraceAtEnvelope_of_rowsTraceAtEnvelope
      h_mem_rows_trace
  have h_mem_execution_trace : env.AcceptedMemoryBusExecutionTraceAtEnvelope :=
    env.acceptedMemoryBusExecutionTraceAtEnvelope_of_fullTraceAtEnvelope
      h_full_mem_bus_trace
  have h_full_mem_trace : env.AcceptedFullMemoryTraceAtEnvelope :=
    env.acceptedFullMemoryTraceAtEnvelope_of_memoryBusExecutionTraceAtEnvelope
      h_mem_execution_trace
  have h_memory_burden : env.memoryBurden :=
    env.memoryBurden_of_acceptedFullMemoryTraceAtEnvelope h_full_mem_trace
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zisk_riscv_compliant_program_bus_branch env
  · exact zisk_riscv_compliant_program_bus_nomem env
  · exact zisk_riscv_compliant_program_bus_rtype_binary env
  · exact zisk_riscv_compliant_program_bus_itype_binary env
  · exact zisk_riscv_compliant_program_bus_shift env
  · exact zisk_riscv_compliant_program_bus_add_rtypew env
  · exact zisk_riscv_compliant_program_bus_ldsd env h_memory_burden
  · exact zisk_riscv_compliant_program_bus_divu_except_known_defects env h_known_bugs
  · exact zisk_riscv_compliant_program_bus_misc env h_memory_burden
  · exact zisk_riscv_compliant_program_bus_remaining env h_memory_burden h_known_bugs

/-- Split generated Mem construction variant of the known-defect-aware global
    theorem. -/
theorem zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionAtEnvelope
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (splitConstruction :
      env.GeneratedMemFullTraceSplitConstructionAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_generatedMemFullTraceConstructionAtEnvelope
    env h_burden
    (env.generatedMemFullTraceConstructionAtEnvelope_of_split
      splitConstruction)
    h_known_bugs

/-- Provider-prefix wrapper for the public global theorem.

    This keeps existing provider-shaped integrations available, but the public
    theorem above no longer consumes this higher-level package as its primary
    memory premise. -/
theorem zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderPrefixSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (h_full_memory_prefix_source :
      env.AcceptedFullExecutionMemoryProviderPrefixSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq := by
  have h_full_memory_source :
      env.AcceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope :=
    env.acceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope_of_providerPrefixSource
      h_full_memory_prefix_source
  have h_accepted_mem_trace_at_envelope :
      env.AcceptedAirMainMemFullTraceConstructionAtEnvelope :=
    env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_providerTraceCursorSource
      h_full_memory_source
  exact
    zisk_riscv_compliant_program_bus
      env h_burden h_accepted_mem_trace_at_envelope h_known_bugs

/-- Split accepted AIR/Main/Mem construction variant of
    `zisk_riscv_compliant_program_bus`.

    This is the narrowest current memory boundary for load replay with split
    Mem obligations: local generated rows, row-order facts, replay facts, and
    the selected prefix cursor. It deliberately does not require the older
    all-row read-replay embedding. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemSplitTraceConstructionAtEnvelope
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (splitConstruction :
      env.AcceptedAirMainMemFullTraceSplitConstructionAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus
    env h_burden
    (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_split
      splitConstruction)
    h_known_bugs

/-- Shared split accepted AIR/Main/Mem trace plus selected-prefix variant of
    the public global theorem.

    This is the factored target for accepted full-execution integration:
    construct the shared split Mem trace once, then supply the selected
    chronological prefix cursor for the current load envelope. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemSplitTraceAndPrefix
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (splitTrace : env.AcceptedAirMainMemFullTraceSplitAtEnvelope)
    (selectedPrefix :
      env.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope
        (env.acceptedAirMainMemFullTraceAtEnvelope_of_splitTrace
          splitTrace))
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedAirMainMemSplitTraceConstructionAtEnvelope
    env h_burden
    (env.acceptedAirMainMemFullTraceSplitConstructionAtEnvelope_of_splitTraceAndPrefix
      splitTrace selectedPrefix)
    h_known_bugs

/-- Variant of the global theorem whose memory input is the shared
    full-execution trace object plus ordinary per-envelope coverage.

    This is the source-shaped target for future accepted-full-execution
    integration: construct one `AcceptedFullExecutionMemoryTrace`, prove the
    selected load coverage for the current envelope, then lower to the current
    split public theorem boundary internally. -/
theorem zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTrace
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (fullTrace : AcceptedFullExecutionMemoryTrace m)
    (coverage :
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope fullTrace)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus env h_burden
    (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_providerTraceCursorSource
      (env.acceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope_of_cursorSource
        (env.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_rowCursorSelectionSource
          (env.acceptedFullExecutionMemoryRowCursorSelectionSourceAtEnvelope_of_traceConstruction
            (env.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_traceWithCoverage
              (env.acceptedFullExecutionMemoryTraceWithCoverageAtEnvelope_of_split
                (env.acceptedFullExecutionMemoryTraceAtEnvelope_of_fullTrace
                  fullTrace)
                (env.acceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope_of_fullTraceCoverage
                  fullTrace coverage)))))))
    h_known_bugs

/-- Variant of the global theorem whose memory input is the packed
    full-execution construction object.

    This is useful for upstream integrations that can construct the
    load-scoped accepted Mem trace, selected cursor, witness-selected Mem table,
    replay embedding, and selected envelope row together. The split
    shared-trace and per-envelope coverage inputs of
    `zisk_riscv_compliant_program_bus` are projected internally. -/
theorem zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceConstruction
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (construction :
      env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus env h_burden
    (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_providerTraceCursorSource
      (env.acceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope_of_rowCursorSelectionSource
        (env.acceptedFullExecutionMemoryRowCursorSelectionSourceAtEnvelope_of_traceConstruction
          construction)))
    h_known_bugs

/-- Variant of the global theorem whose memory input is source-shaped
    full-execution evidence.

    This exposes the split-indexed source boundary already present in
    `OpEnvelope`: accepted full execution supplies the shared accepted Mem trace,
    selected envelope row, and prefix-state evidence; the selected cursor and
    packed construction object are built internally. -/
theorem zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (source : env.AcceptedFullExecutionMemoryTraceSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceConstruction
    env h_burden
    (env.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_traceWithCoverage
      (env.acceptedFullExecutionMemoryTraceWithCoverageAtEnvelope_of_source
        source))
    h_known_bugs

/-- Variant of the global theorem whose memory input is cursor-shaped
    full-execution source evidence.

    This is the theorem boundary closest to accepted execution replay: prove
    the shared accepted Mem trace, selected envelope row, selected chronological
    prefix cursor, and selected occurrence uniqueness; the source predicate,
    selected coverage, and packed replay construction are derived internally. -/
theorem zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceCursorSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (cursorSource :
      env.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceSource
    env h_burden
    (env.acceptedFullExecutionMemoryTraceSourceAtEnvelope_of_cursorSource
      cursorSource)
    h_known_bugs

/-- Variant of the global theorem whose memory input is provider-row
    cursor-shaped full-execution source evidence. This is the primary theorem's
    memory boundary exposed under a descriptive wrapper name. -/
theorem zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderTraceCursorSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (providerCursorSource :
      env.AcceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus env h_burden
    (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_providerTraceCursorSource
      providerCursorSource)
    h_known_bugs

/-- Variant of the global theorem whose memory input is provider-row cursor
    evidence for the concrete FullEnsemble Mem table identified by upstream
    routing.

    This is the route-friendly provider boundary: direct `LD` balance can
    construct the selected provider row in the concrete mutable Mem table it
    finds, and the selected prefix cursor lowers directly to the accepted
    AIR/Main/Mem trace construction consumed by replay. -/
theorem zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderTableCursorSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (providerTableCursorSource :
      env.AcceptedFullExecutionMemoryProviderTableCursorSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq := by
  obtain ⟨_h_row_burden, _h_table_provider_burden, _h_route_burden⟩ :=
    h_burden
  have h_accepted_mem_trace_at_envelope :
      env.AcceptedAirMainMemFullTraceConstructionAtEnvelope :=
    env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_providerTableCursorSource
      providerTableCursorSource
  have h_generated_mem_trace :
      env.GeneratedMemFullTraceConstructionAtEnvelope :=
    env.generatedMemFullTraceConstructionAtEnvelope_of_acceptedAirMainMemTrace
      h_accepted_mem_trace_at_envelope
  have h_mem_rows_construction :
      env.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope :=
    env.acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_generatedTraceAtEnvelope
      h_generated_mem_trace
  have h_mem_rows_trace : env.AcceptedFullMemoryBusRowsTraceAtEnvelope :=
    env.acceptedFullMemoryBusRowsTraceAtEnvelope_of_construction
      h_mem_rows_construction
  have h_full_mem_bus_trace : env.AcceptedFullMemoryBusTraceAtEnvelope :=
    env.acceptedFullMemoryBusTraceAtEnvelope_of_rowsTraceAtEnvelope
      h_mem_rows_trace
  have h_mem_execution_trace : env.AcceptedMemoryBusExecutionTraceAtEnvelope :=
    env.acceptedMemoryBusExecutionTraceAtEnvelope_of_fullTraceAtEnvelope
      h_full_mem_bus_trace
  have h_full_mem_trace : env.AcceptedFullMemoryTraceAtEnvelope :=
    env.acceptedFullMemoryTraceAtEnvelope_of_memoryBusExecutionTraceAtEnvelope
      h_mem_execution_trace
  have h_memory_burden : env.memoryBurden :=
    env.memoryBurden_of_acceptedFullMemoryTraceAtEnvelope h_full_mem_trace
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zisk_riscv_compliant_program_bus_branch env
  · exact zisk_riscv_compliant_program_bus_nomem env
  · exact zisk_riscv_compliant_program_bus_rtype_binary env
  · exact zisk_riscv_compliant_program_bus_itype_binary env
  · exact zisk_riscv_compliant_program_bus_shift env
  · exact zisk_riscv_compliant_program_bus_add_rtypew env
  · exact zisk_riscv_compliant_program_bus_ldsd env h_memory_burden
  · exact zisk_riscv_compliant_program_bus_divu_except_known_defects env h_known_bugs
  · exact zisk_riscv_compliant_program_bus_misc env h_memory_burden
  · exact zisk_riscv_compliant_program_bus_remaining env h_memory_burden h_known_bugs

/-- Variant of the global theorem whose memory input is the unpacked accepted
    AIR/Main/Mem trace construction plus full-ensemble witness facts.

    This exposes the current upstream construction target without requiring
    callers to first package it as
    `AcceptedFullExecutionMemoryTraceConstructionAtEnvelope`: accepted full
    execution must provide the accepted Mem trace construction, mutable-Mem
    read/replay embeddings, and selected envelope Mem-row occurrence. The
    selected cursor is already in `construction`, and occurrence uniqueness is
    derived from the accepted trace's `rowsNodup` field. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemTraceConstruction
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (construction : env.AcceptedAirMainMemFullTraceConstructionAtEnvelope)
    (embedded :
      env.MutableMemReadReplayRowsEmbeddedAtAcceptedTraceConstruction
        program witness construction)
    (replayEmbedded :
      env.MutableMemReplayRowsEmbeddedAtAcceptedTraceConstruction
        program witness construction)
    (selectedEnvelopeRow :
      env.SelectedEnvelopeMemRowAtAcceptedTraceConstructionWithWitness
        program witness construction embedded replayEmbedded)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceCursorSource
    env h_burden
    (env.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_traceConstruction
      (env.acceptedFullExecutionMemoryTraceConstructionWithWitness_of_fields
        program witness construction embedded replayEmbedded
        selectedEnvelopeRow))
    h_known_bugs

/-- Provider-shaped variant of
    `zisk_riscv_compliant_program_bus_of_acceptedAirMainMemTraceConstruction`.

    This is the construction-level accepted-execution target after replacing
    selected envelope-row equality with concrete primary/dual provider-row
    replay coverage in the witness-selected mutable Mem table. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderTraceConstruction
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (construction : env.AcceptedAirMainMemFullTraceConstructionAtEnvelope)
    (embedded :
      env.MutableMemReadReplayRowsEmbeddedAtAcceptedTraceConstruction
        program witness construction)
    (replayEmbedded :
      env.MutableMemReplayRowsEmbeddedAtAcceptedTraceConstruction
        program witness construction)
    (selectedProviderRow :
      env.SelectedMemProviderRowAtAcceptedTraceConstructionWithWitness
        program witness construction embedded replayEmbedded)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderPrefixSource
    env h_burden
    (env.acceptedFullExecutionMemoryProviderPrefixSourceAtEnvelope_of_providerTraceConstruction
      (env.acceptedFullExecutionMemoryProviderTraceConstructionWithWitness_of_fields
        program witness construction embedded replayEmbedded
        selectedProviderRow))
    h_known_bugs

/-- Split-construction variant of
    `zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderTraceConstruction`.

    This exposes the accepted AIR/Main/Mem obligations before they are packed:
    generated Mem row facts, row-order facts, and replay facts remain separated
    in `splitConstruction`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderSplitConstruction
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (splitConstruction :
      env.AcceptedAirMainMemFullTraceSplitConstructionAtEnvelope)
    (embedded :
      env.MutableMemReadReplayRowsEmbeddedAtAcceptedTraceConstruction
        program witness
        (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_split
          splitConstruction))
    (replayEmbedded :
      env.MutableMemReplayRowsEmbeddedAtAcceptedTraceConstruction
        program witness
        (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_split
          splitConstruction))
    (selectedProviderRow :
      env.SelectedMemProviderRowAtAcceptedTraceConstructionWithWitness
        program witness
        (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_split
          splitConstruction)
        embedded replayEmbedded)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderTraceConstruction
    env h_burden program witness
    (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_split
      splitConstruction)
    embedded replayEmbedded selectedProviderRow h_known_bugs

/-- Variant of the global theorem whose memory input is accepted AIR/Main/Mem
    trace data plus the full RV64IM witness and mutable-Mem embeddings.

    This exposes the next upstream integration target without changing the
    remaining proof burden: accepted full execution still has to construct the
    `AcceptedAirMainMemFullTrace`, the witness-level read and replay
    embeddings, and the selected per-envelope coverage. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemFullTrace
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (coverage :
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
        (AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace
          program witness acceptedTrace embedded replayEmbedded))
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTrace env h_burden
    (AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace
      program witness acceptedTrace embedded replayEmbedded)
    coverage h_known_bugs

/-- Variant of the global theorem whose memory input is unpacked accepted
    AIR/Main/Mem trace data plus provider-shaped selected-load evidence.

    This is the provider-row successor to
    `zisk_riscv_compliant_program_bus_of_acceptedAirMainMemSelection`: accepted
    execution supplies the shared trace and embeddings, then each load envelope
    supplies selected provider-row replay coverage and selected chronological
    prefix cursor. Occurrence uniqueness is still derived internally from
    `rowsNodup`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selection :
      env.AcceptedFullExecutionMemoryProviderTraceSelectionAtEnvelope
        program witness acceptedTrace embedded replayEmbedded)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderPrefixSource
    env h_burden
    (env.acceptedFullExecutionMemoryProviderPrefixSourceAtEnvelope_of_providerSelection
      program witness acceptedTrace embedded replayEmbedded selection)
    h_known_bugs

/-- Split accepted AIR/Main/Mem trace variant of
    `zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderSelection`.

    This keeps generated Mem row facts, row-order facts, and replay facts
    separated at the accepted-execution boundary, then repacks only through the
    explicit split-selection adapter needed by the existing FullEnsemble table
    predicates. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderSplitSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTraceSplit m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selection :
      env.AcceptedFullExecutionMemoryProviderSplitTraceSelectionAtEnvelope
        program witness acceptedTrace embedded replayEmbedded)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderSelection
    env h_burden program witness acceptedTrace.toAcceptedAirMainMemFullTrace
    embedded replayEmbedded
    (env.acceptedFullExecutionMemoryProviderTraceSelectionAtEnvelope_of_split
      program witness acceptedTrace embedded replayEmbedded selection)
    h_known_bugs

/-- Variant of the global theorem whose shared memory input is the named
    accepted-execution Mem row extraction package.

    This is the current global extraction target factored into two pieces:
    the shared chronological Mem row trace plus mutable-Mem embeddings, and the
    per-envelope selected-load coverage for that shared extraction. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowExtraction
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryRowExtraction m)
    (coverage :
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
        extraction.toFullTrace)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTrace env h_burden
    extraction.toFullTrace coverage h_known_bugs

/-- Split variant of
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowExtraction`.

    Accepted full-execution integration can keep accepted AIR/Main/Mem
    generated-row, row-order, and replay facts separated in `extraction`; this
    wrapper repacks only at the existing full-trace compliance boundary. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowSplitExtraction
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryRowSplitExtraction m)
    (coverage :
      env.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope
        extraction.toRowExtraction.toFullTrace)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowExtraction
    env h_burden extraction.toRowExtraction coverage h_known_bugs

/-- Variant of the global theorem whose memory input is the named shared row
    extraction plus unpacked selected-load evidence.

    Accepted full execution should eventually construct `extraction` once per
    program trace and `selection` for each selected load envelope. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowExtractionSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryRowExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryRowSelectionAtEnvelope extraction)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceCursorSource
    env h_burden
    (env.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_rowSelection
      extraction selection)
    h_known_bugs

/-- Split variant of
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowExtractionSelection`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowSplitExtractionSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryRowSplitExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryRowSelectionAtEnvelope
        extraction.toRowExtraction)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowExtractionSelection
    env h_burden extraction.toRowExtraction selection h_known_bugs

/-- Variant of the global theorem whose memory input is the named shared row
    extraction plus cursor-shaped selected-load evidence.

    This is the sharper accepted-full-execution integration target: construct
    the shared chronological Mem row extraction once, then for each load prove
    the selected mutable-Mem provider-row occurrence and selected chronological
    prefix cursor. Occurrence uniqueness is derived internally from the
    accepted trace's duplicate-free row invariant. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowCursorSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryRowExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryRowCursorSelectionAtEnvelope extraction)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceCursorSource
    env h_burden
    (env.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_rowCursorSelection
      extraction selection)
    h_known_bugs

/-- Split variant of
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowCursorSelection`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowSplitCursorSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryRowSplitExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryRowCursorSelectionAtEnvelope
        extraction.toRowExtraction)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowCursorSelection
    env h_burden extraction.toRowExtraction selection h_known_bugs

/-- Variant of the global theorem whose memory input is the named shared row
    extraction plus provider-row cursor-shaped selected-load evidence. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowCursorSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryRowExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryProviderRowCursorSelectionAtEnvelope
        extraction)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderTraceCursorSource
    env h_burden
    (env.acceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope_of_providerRowCursorSelection
      extraction selection)
    h_known_bugs

/-- Split variant of
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowCursorSelection`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitCursorSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryRowSplitExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryProviderRowCursorSelectionAtEnvelope
        extraction.toRowExtraction)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowCursorSelection
    env h_burden extraction.toRowExtraction selection h_known_bugs

/-- Split-trace provider-selection variant indexed by the named shared row
    split extraction.

    Unlike
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitCursorSelection`,
    the selected provider-row/prefix evidence is stated over the split
    accepted AIR/Main/Mem trace itself, not over
    `extraction.toRowExtraction`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitTraceSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryRowSplitExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryProviderRowSplitTraceSelectionAtEnvelope
        extraction)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderSplitSelection
    env h_burden extraction.program extraction.witness
    extraction.acceptedTrace extraction.embedded extraction.replayEmbedded
    selection h_known_bugs

/-- Generated split Mem construction variant of
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitTraceSelection`.

    This exposes the current honest memory boundary at the top-level theorem:
    callers must provide the generated split Mem construction, both
    witness-level mutable-Mem embedding predicates, and the per-load
    provider-row/prefix selection indexed by the extraction built from those
    facts. -/
theorem zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionProviderSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    {initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (construction :
      ZiskFv.AirsClean.Mem.GeneratedMemFullTraceSplitConstruction
        initialState rows)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness rows)
    (selection :
      env.AcceptedFullExecutionMemoryProviderRowSplitTraceSelectionAtEnvelope
        (AcceptedFullExecutionMemoryRowSplitExtraction.ofGeneratedMemTrace
          program witness construction embedded replayEmbedded))
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitTraceSelection
    env h_burden
    (AcceptedFullExecutionMemoryRowSplitExtraction.ofGeneratedMemTrace
      program witness construction embedded replayEmbedded)
    selection h_known_bugs

/-- Replay-provider split-trace selection variant indexed by the named shared
    row split extraction.

    This is the all-event replay counterpart of
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitTraceSelection`:
    selected provider-row coverage uses
    `SelectedMemProviderReplayRowInFullEnsembleMemTableAtEnvelope`, so callers
    stay on the mutable-Mem replay embedding route. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplayProviderRowSplitTraceSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryRowSplitExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryReplayProviderRowSplitTraceSelectionAtEnvelope
        extraction)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus
    env h_burden
    (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_replayProviderRowSplitTraceSelectionSource
      (env.acceptedFullExecutionMemoryReplayProviderRowSplitTraceSelectionSourceAtEnvelope_of_selection
        extraction selection))
    h_known_bugs

/-- Generated split Mem construction variant using replay-provider selected
    coverage.

    This exposes the same generated split Mem construction and mutable-Mem
    embedding obligations as
    `zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionProviderSelection`,
    but the per-load selected provider row is stated against the all-event
    replay projection. -/
theorem zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionReplayProviderSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    {initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (construction :
      ZiskFv.AirsClean.Mem.GeneratedMemFullTraceSplitConstruction
        initialState rows)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness rows)
    (selection :
      env.AcceptedFullExecutionMemoryReplayProviderRowSplitTraceSelectionAtEnvelope
        (AcceptedFullExecutionMemoryRowSplitExtraction.ofGeneratedMemTrace
          program witness construction embedded replayEmbedded))
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplayProviderRowSplitTraceSelection
    env h_burden
    (AcceptedFullExecutionMemoryRowSplitExtraction.ofGeneratedMemTrace
      program witness construction embedded replayEmbedded)
    selection h_known_bugs

/-- Replay-only split-trace selection variant.

    This is the narrower replay-provider boundary: the shared extraction
    carries the generated split Mem construction, one concrete mutable Mem
    table from the full RV64IM witness, and the all-event replay embedding for
    that table. It does not require the read-only mutable-Mem embedding. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplayRowSplitTraceSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (extraction : AcceptedFullExecutionMemoryReplayRowSplitExtraction m)
    (selection :
      env.AcceptedFullExecutionMemoryReplayRowSplitTraceSelectionAtEnvelope
        extraction)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus
    env h_burden
    (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_replayRowSplitTraceSelectionSource
      (env.acceptedFullExecutionMemoryReplayRowSplitTraceSelectionSourceAtEnvelope_of_selection
        extraction selection))
    h_known_bugs

/-- Accepted split AIR/Main/Mem trace variant using replay-only selected
    coverage.

    This wrapper is closer to the accepted full-execution target than the
    generated split variant: callers provide the accepted split Mem trace plus
    the witness-level all-event mutable-Mem replay embedding directly. The
    concrete mutable Mem table is selected internally. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemFullTraceSplitReplayRowSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTraceSplit m)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selection :
      env.AcceptedFullExecutionMemoryReplayRowSplitTraceSelectionAtEnvelope
        (AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofAcceptedAirMainMemTrace
          program witness acceptedTrace replayEmbedded))
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplayRowSplitTraceSelection
    env h_burden
    (AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofAcceptedAirMainMemTrace
      program witness acceptedTrace replayEmbedded)
    selection h_known_bugs

/-- Accepted split AIR/Main/Mem trace variant whose per-load input is
    provider-row coverage plus prefix-state equality. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemFullTraceSplitReplayRowStateSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTraceSplit m)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selection :
      env.AcceptedFullExecutionMemoryReplayRowSplitTraceStateSelectionAtEnvelope
        (AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofAcceptedAirMainMemTrace
          program witness acceptedTrace replayEmbedded))
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedAirMainMemFullTraceSplitReplayRowSelection
    env h_burden program witness acceptedTrace replayEmbedded
    (env.acceptedFullExecutionMemoryReplayRowSplitTraceSelectionAtEnvelope_of_stateSelection
      (AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofAcceptedAirMainMemTrace
        program witness acceptedTrace replayEmbedded)
      selection)
    h_known_bugs

/-- Generated split Mem construction variant using replay-only selected
    coverage.

    Compared with
    `zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionReplayProviderSelection`,
    this wrapper drops the read-only mutable-Mem embedding premise. The
    selected provider row is stated against the concrete mutable Mem table
    selected from the witness and the all-event replay projection. -/
theorem zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionReplayRowSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    {initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (construction :
      ZiskFv.AirsClean.Mem.GeneratedMemFullTraceSplitConstruction
        initialState rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness rows)
    (selection :
      env.AcceptedFullExecutionMemoryReplayRowSplitTraceSelectionAtEnvelope
        (AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofGeneratedMemTrace
          program witness construction replayEmbedded))
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplayRowSplitTraceSelection
    env h_burden
    (AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofGeneratedMemTrace
      program witness construction replayEmbedded)
    selection h_known_bugs

/-- Replay-only generated split Mem construction variant whose per-load input
    is provider-row coverage plus prefix-state equality.

    This is closer to the accepted full-execution integration target than
    `zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionReplayRowSelection`:
    callers identify the selected provider replay row and prove Sail/replay
    prefix-state agreement, while the selected prefix cursor is constructed
    internally. -/
theorem zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionReplayRowStateSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    {initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (construction :
      ZiskFv.AirsClean.Mem.GeneratedMemFullTraceSplitConstruction
        initialState rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness rows)
    (selection :
      env.AcceptedFullExecutionMemoryReplayRowSplitTraceStateSelectionAtEnvelope
        (AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofGeneratedMemTrace
          program witness construction replayEmbedded))
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionReplayRowSelection
    env h_burden program witness construction replayEmbedded
    (env.acceptedFullExecutionMemoryReplayRowSplitTraceSelectionAtEnvelope_of_stateSelection
      (AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofGeneratedMemTrace
        program witness construction replayEmbedded)
      selection)
    h_known_bugs

/-- Variant of the global theorem whose memory input is the load-scoped
    row-extraction/cursor-selection source package.

    This is the single per-envelope package expected from accepted
    full-execution memory integration: non-load envelopes carry no memory
    data, while load envelopes carry the shared row extraction plus selected
    mutable-Mem row and selected chronological prefix cursor. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowCursorSelectionSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (source :
      env.AcceptedFullExecutionMemoryRowCursorSelectionSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceCursorSource
    env h_burden
    (env.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_rowCursorSelectionSource
      source)
    h_known_bugs

/-- Split variant of
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowCursorSelectionSource`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowSplitCursorSelectionSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (source :
      env.AcceptedFullExecutionMemoryRowSplitCursorSelectionSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceCursorSource
    env h_burden
    (env.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_rowSplitCursorSelectionSource
      source)
    h_known_bugs

/-- Variant of the global theorem whose memory input is load-scoped
    provider-row extraction/cursor-selection evidence. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowCursorSelectionSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (source :
      env.AcceptedFullExecutionMemoryProviderRowCursorSelectionSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderTraceCursorSource
    env h_burden
    (env.acceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope_of_providerRowCursorSelectionSource
      source)
    h_known_bugs

/-- Split variant of
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowCursorSelectionSource`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitCursorSelectionSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (source :
      env.AcceptedFullExecutionMemoryProviderRowSplitCursorSelectionSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderTraceCursorSource
    env h_burden
    (env.acceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope_of_providerRowSplitCursorSelectionSource
      source)
    h_known_bugs

/-- Split-trace source variant of
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitCursorSelectionSource`.

    The per-envelope selected provider-row/prefix evidence is stated over the
    split accepted AIR/Main/Mem trace itself, so this wrapper does not require
    callers to provide evidence over `extraction.toRowExtraction`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitTraceSelectionSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (source :
      env.AcceptedFullExecutionMemoryProviderRowSplitTraceSelectionSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderTraceCursorSource
    env h_burden
    (env.acceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope_of_providerRowSplitTraceSelectionSource
      source)
    h_known_bugs

/-- Replay-provider split-trace source variant of
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitTraceSelectionSource`.

    The selected provider row is stated against the all-event mutable-Mem
    replay projection, with primary rows carrying `wr = 0`, so callers do not
    route selected-load coverage through the read-only replay embedding. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplayProviderRowSplitTraceSelectionSource
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (source :
      env.AcceptedFullExecutionMemoryReplayProviderRowSplitTraceSelectionSourceAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus
    env h_burden
    (env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_replayProviderRowSplitTraceSelectionSource
      source)
    h_known_bugs

/-- Variant whose memory input is the split provider-shaped accepted
    AIR/Main/Mem construction package.

    This is one step closer to accepted full-execution data than
    `zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitTraceSelectionSource`:
    the selected prefix is carried by the split construction, while selected
    provider-row coverage and mutable-Mem embeddings remain explicit
    witness-level obligations. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderSplitTraceConstruction
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (construction :
      env.AcceptedFullExecutionMemoryProviderSplitTraceConstructionAtEnvelope)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowSplitTraceSelectionSource
    env h_burden
    (env.acceptedFullExecutionMemoryProviderRowSplitTraceSelectionSourceAtEnvelope_of_providerSplitTraceConstruction
      construction)
    h_known_bugs

/-- Split-indexed variant of
    `zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderSplitConstruction`.

    The mutable-Mem embedding obligations and selected provider-row coverage
    are stated over the split construction itself, avoiding a caller-visible
    detour through `acceptedAirMainMemFullTraceConstructionAtEnvelope_of_split`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderSplitTraceConstruction
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (splitConstruction :
      env.AcceptedAirMainMemFullTraceSplitConstructionAtEnvelope)
    (embedded :
      env.MutableMemReadReplayRowsEmbeddedAtAcceptedSplitTraceConstruction
        program witness splitConstruction)
    (replayEmbedded :
      env.MutableMemReplayRowsEmbeddedAtAcceptedSplitTraceConstruction
        program witness splitConstruction)
    (selectedProviderRow :
      env.SelectedMemProviderRowAtAcceptedSplitTraceConstructionWithWitness
        program witness splitConstruction embedded replayEmbedded)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderSplitTraceConstruction
    env h_burden
    (env.acceptedFullExecutionMemoryProviderSplitTraceConstructionWithWitness_of_fields
      program witness splitConstruction embedded replayEmbedded
      selectedProviderRow)
    h_known_bugs

/-- Variant of the global theorem whose per-envelope memory input is the
    unpacked selected-prefix and selected witness Mem-row evidence.

    This is the next accepted-execution integration shape after constructing
    the shared accepted AIR/Main/Mem trace and mutable-Mem embeddings. It still
    leaves the semantic Mem trace construction itself explicit in
    `acceptedTrace`. -/
theorem zisk_riscv_compliant_program_bus_of_acceptedAirMainMemSelection
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    {length : ℕ}
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble
          length program).ensemble)
    (acceptedTrace : ZiskFv.AirsClean.Mem.AcceptedAirMainMemFullTrace m)
    (embedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (replayEmbedded :
      ZiskFv.AirsClean.FullEnsemble.MutableMemReplayRowsEmbeddedInTrace
        witness acceptedTrace.rows)
    (selection :
      env.AcceptedFullExecutionMemoryTraceSelectionAtEnvelope
        program witness acceptedTrace embedded replayEmbedded)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq :=
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceCursorSource
    env h_burden
    (env.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_selection
      program witness acceptedTrace embedded replayEmbedded selection)
    h_known_bugs

end ZiskFv.Compliance
