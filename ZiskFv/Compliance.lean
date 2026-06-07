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

    For any `OpEnvelope` arm, the channel-balance form of the
    conclusion (`= state_effect_via_channels …`) holds outside the
    defect regions recorded by `Defects.NoKnownDefect`. -/
theorem zisk_riscv_compliant_program_bus
    (env : OpEnvelope state m r_main)
    (h_burden : env.completenessBurden)
    (h_full_memory_trace :
      env.AcceptedFullExecutionMemoryTraceAtEnvelope)
    (h_full_memory_coverage :
      env.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope
        h_full_memory_trace)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq := by
  obtain ⟨_h_row_burden, _h_table_provider_burden, _h_route_burden⟩ :=
    h_burden
  let h_mem_trace_with_coverage :
      env.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope :=
    env.acceptedFullExecutionMemoryTraceWithCoverageAtEnvelope_of_split
      h_full_memory_trace h_full_memory_coverage
  let h_mem_construction :
      env.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope :=
    env.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_traceWithCoverage
      h_mem_trace_with_coverage
  let h_mem_extraction :
      env.AcceptedFullExecutionMemoryCursorExtractionAtEnvelope :=
    env.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_acceptedTraceConstruction
      h_mem_construction
  let h_trace_with_table :
      env.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope :=
    env.acceptedAirMainMemFullTraceWithMemTableAtEnvelope_of_fullEnsemble
      h_mem_extraction.fullTraceTable
  let h_accepted_mem_trace :
      env.AcceptedAirMainMemFullTraceAtEnvelope :=
    env.acceptedTraceOfFullTraceWithMemTable h_trace_with_table
  have _h_selected_mem_row :
      env.SelectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope
        h_accepted_mem_trace :=
    env.selectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope_of_envelopeMemRowReplay
      h_mem_extraction.fullTraceTable
      h_mem_extraction.selectedEnvelopeRow
  have h_selected_mem_prefix :
      env.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope
        h_accepted_mem_trace :=
    h_mem_extraction.selectedPrefix
  have h_accepted_mem_trace_at_envelope :
      env.AcceptedAirMainMemFullTraceConstructionAtEnvelope :=
    env.acceptedAirMainMemFullTraceConstructionAtEnvelope_of_traceAndPrefix
      h_accepted_mem_trace h_selected_mem_prefix
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
    (env.acceptedFullExecutionMemoryTraceAtEnvelope_of_fullTrace fullTrace)
    (env.acceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope_of_fullTraceCoverage
      fullTrace coverage)
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
    (env.acceptedFullExecutionMemoryTraceAtEnvelope_of_traceConstruction
      construction)
    (env.acceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope_of_traceConstruction
      construction)
    h_known_bugs

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
  zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceConstruction
    env h_burden
    (env.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_acceptedAirMainMemSelection
      program witness acceptedTrace embedded replayEmbedded selection)
    h_known_bugs

end ZiskFv.Compliance
