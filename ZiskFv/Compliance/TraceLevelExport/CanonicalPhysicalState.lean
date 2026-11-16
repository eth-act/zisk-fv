import ZiskFv.Compliance.TraceLevelExport.ActualMainMutableProjection
import ZiskFv.Compliance.TraceLevelExport.PhysicalRegisterFold
import ZiskFv.Compliance.TraceLevelExport.MappedMemoryInvariant
import ZiskFv.Compliance.TraceLevelExport.OldCanonicalExecution
import ZiskFv.Compliance.TraceLevelExport.CanonicalSourceParser

/-!
# Actual physical register/memory agreement at source cuts

The memory fold visits the entire actual Main mutable projection, and the
register fold visits every actual physical C request. Source auxiliaries
stutter by the proved six-message/C-write facts, not by adding dummy Sail
instructions or deleting RAW balance entries. PC agreement remains an
architectural-source-start property; it is NOT asserted at an internal JALR PC.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open CanonicalExecutionRows
open RawProgramBinding
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

section Source

variable {m rawLength : Nat}
variable (rawProgram : Fin rawLength → BitVec 32) (selected : Fin m → Fin rawLength)
variable (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
variable (trace : AcceptedZiskTrace (sourceEnd L))
variable (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
variable (binding : ProgramRowsBinding trace start addr rawProgram)
variable (steps : ∀ i, ZiskStep trace (physicalStart L i))
variable (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
  start addr rawProgram)
variable (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
  (physicalStart L i).val = addr (selected i))

local notation "D" => (fun i => rowDecode_of_programDecode trace (physicalStart L i)
  (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
    start addr rawProgram binding (rawDecodes i)))

include binding atPc

/-- Simultaneous agreement with ACTUAL physical memory replay and ACTUAL
physical C-register writeback. Only preceding real architectural soundness is
used; this is an internal inductive consequence, not a new root premise. -/
theorem canonical_physical_state_at_source_cut
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (j : Nat) (h : j ≤ m)
    (sounds : ∀ i : Fin m, i.val < j →
      StepSound trace (mappedSailTrace L steps init)
        (physicalStart L i) (steps i) (D i)) :
    (mappedSailStates L steps init j h).mem =
        replayMemoryAfterBusRows init.mem
          (((actualMainMutablePhysicalSlots trace).take
            (rowPrefix (sourceWidth L) j)).flatten) ∧
      (∀ k : Fin 32, k ≠ 0 →
        (mappedSailStates L steps init j h).regs.get? (reg_of_fin k) =
          some (cast (by rw [register_type_reg_of_fin_equiv])
            (actualPhysicalRegFile trace (rowPrefix (sourceWidth L) j)
              (prefix_mono (sourceWidth L) h) k))) := by
  constructor
  · rw [actual_main_mutable_prefix_flatten rawProgram selected L trace
      start addr binding steps rawDecodes atPc j h]
    exact mapped_mem_prefix_of_stepSound L steps init D j h sounds
  · exact mappedRegAgree_actualPhysical_prefix rawProgram selected L trace
      start addr binding steps rawDecodes atPc init regBoot j h sounds

/-- Crossing the actual expanded first row changes neither physical mutable
memory replay nor the actual physical register file. All physical rows remain
in their respective folds; there is NO auxiliary Sail/ZiskStep. -/
theorem expanded_auxiliary_physical_state_stutter
    (i : Fin m) (two : (L i).width = 2)
    (memory : Std.ExtHashMap Nat (BitVec 8)) :
    replayMemoryAfterBusRows memory
        (((actualMainMutablePhysicalSlots trace).take ((physicalStart L i).val + 1)).flatten) =
      replayMemoryAfterBusRows memory
        (((actualMainMutablePhysicalSlots trace).take (physicalStart L i).val).flatten) ∧
      actualPhysicalRegFile trace ((physicalStart L i).val + 1)
          (Nat.succ_le_of_lt (physicalStart L i).isLt) =
        actualPhysicalRegFile trace (physicalStart L i).val
          (Nat.le_of_lt (physicalStart L i).isLt) := by
  let p := physicalStart L i
  let row : Fin trace.mainTable.table.length := ⟨p.val, trace.mainTable_index p⟩
  have projected := expanded_main_first_mutable_replay_rows_nil trace start addr rawProgram
    binding (selected i) (L i) two row (atPc i)
  have neutral := expanded_main_first_replay_and_register_neutral trace start addr rawProgram
    binding (selected i) (L i) two row (atPc i) memory
  constructor
  · have hp : p.val < (actualMainMutablePhysicalSlots trace).length := by
      simpa [actualMainMutablePhysicalSlots] using p.isLt
    have atSlot : (actualMainMutablePhysicalSlots trace)[p.val]'hp = [] := by
      simpa [actualMainMutablePhysicalSlots, physicalMainMutableReplayRowsAt, row]
        using projected
    have atOption : (actualMainMutablePhysicalSlots trace)[p.val]? = some [] := by
      rw [List.getElem?_eq_getElem hp, atSlot]
    dsimp only [p] at atOption
    simp only [List.take_succ, atOption, Option.toList_some, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil]
  · rw [actualPhysicalRegFile_succ]
    exact actualCRegisterAction_of_none trace row neutral.2 _

end Source

/-- Shared same-witness transport. These inputs are conclusions of
old_root_canonical_comparison for the SAME selected words and lowerings;
the public-caller results construct them rather than adding a state oracle. -/
private theorem actual_physical_states_of_canonical_data {n rawLength : Nat}
    (oldTrace : AcceptedZiskTrace n)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (oldSteps : ∀ i : Fin n, ZiskStep oldTrace i)
    (start : Fin rawLength → Fin oldTrace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding oldTrace start addr rawProgram)
    (rawDecodes : ∀ i, RawProgramDecode oldTrace i (oldSteps i) start addr rawProgram)
    (selected : Fin n → Fin rawLength)
    (lowering : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
    (room : sourceEnd lowering ≤ oldTrace.mainTable.table.length)
    (starts : ∀ i, sourceStart lowering i = i.val)
    (selectedPc : ∀ i, addr (selected i) =
      (mainOfTable oldTrace.program oldTrace.mainTable).pc i.val)
    (states : ∀ (j : Nat) (hj : j ≤ n),
      mappedSailStates lowering
          (oldCanonicalSteps oldTrace lowering room starts oldSteps) init j hj =
        chainedSailStates oldSteps init j)
    (copiedSound : ∀ i : Fin n,
      StepSound (recountWithinMain oldTrace (sourceEnd lowering) room)
        (mappedSailTrace lowering (oldCanonicalSteps oldTrace lowering room starts oldSteps) init)
        (physicalStart lowering i) (oldCanonicalSteps oldTrace lowering room starts oldSteps i)
        (oldCanonicalDecoded oldTrace lowering room starts oldSteps
          (fun j => rowDecode_of_programDecode oldTrace j
            (programDecode_of_rawProgramDecode oldTrace j (oldSteps j) start addr rawProgram
              binding (rawDecodes j))) i))
    (rawWitness : Nonempty (∀ i : Fin n,
      RawProgramDecode (recountWithinMain oldTrace (sourceEnd lowering) room)
        (physicalStart lowering i) (oldCanonicalSteps oldTrace lowering room starts oldSteps i)
        start addr rawProgram))
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64))) :
    (∀ i : Fin n,
      rowPrefix (sourceWidth lowering) (i.val + 1) < oldTrace.mainTable.table.length ∧
        (chainedSailStates oldSteps init (i.val + 1)).regs.get? Register.PC =
          some (register_type_pc_equiv ▸ BitVec.ofNat 64
            ((mainOfTable oldTrace.program oldTrace.mainTable).pc
              (rowPrefix (sourceWidth lowering) (i.val + 1))).val)) ∧
    ∀ (j : Nat) (hj : j ≤ n),
      (chainedSailStates oldSteps init j).mem =
          replayMemoryAfterBusRows init.mem
            (((actualMainMutablePhysicalSlots
              (recountWithinMain oldTrace (sourceEnd lowering) room)).take
              (rowPrefix (sourceWidth lowering) j)).flatten) ∧
        (∀ k : Fin 32, k ≠ 0 →
          (chainedSailStates oldSteps init j).regs.get? (reg_of_fin k) =
            some (cast (by rw [register_type_reg_of_fin_equiv])
              (actualPhysicalRegFile (recountWithinMain oldTrace (sourceEnd lowering) room)
                (rowPrefix (sourceWidth lowering) j)
                (prefix_mono (sourceWidth lowering) hj) k))) := by
  let trace := recountWithinMain oldTrace (sourceEnd lowering) room
  let steps := oldCanonicalSteps oldTrace lowering room starts oldSteps
  let oldDecoded := fun i => rowDecode_of_programDecode oldTrace i
    (programDecode_of_rawProgramDecode oldTrace i (oldSteps i) start addr rawProgram
      binding (rawDecodes i))
  let copiedDecoded := oldCanonicalDecoded oldTrace lowering room starts oldSteps oldDecoded
  obtain ⟨newRaw⟩ := rawWitness
  have newBinding : ProgramRowsBinding trace start addr rawProgram := binding
  let decoded := fun i => rowDecode_of_programDecode trace (physicalStart lowering i)
    (programDecode_of_rawProgramDecode trace (physicalStart lowering i) (steps i)
      start addr rawProgram newBinding (newRaw i))
  have atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart lowering i).val = addr (selected i) := by
    intro i
    change (mainOfTable oldTrace.program oldTrace.mainTable).pc
      (sourceStart lowering i) = addr (selected i)
    rw [starts i]
    exact (selectedPc i).symm
  have sameProducer (i : Fin n) :
      stepProducerRow (physicalStart lowering i) (steps i) (decoded i) =
        stepProducerRow (physicalStart lowering i) (steps i) (copiedDecoded i) := by
    have actualStop := mapped_producer_successor_eq_source_stop rawProgram selected lowering
      trace start addr newBinding steps newRaw atPc i
    have copiedProducer := oldCanonicalProducer oldTrace lowering room starts oldSteps
      oldDecoded i
    have oldWidth := source_width_at_selected_pc oldTrace i (oldSteps i)
      start addr rawProgram binding (rawDecodes i) (selected i) (lowering i)
      (selectedPc i).symm
    have oldPlacement := ExecutionSpanLegacy.producer_eq_index_or_succ i
      (oldSteps i) (oldDecoded i)
    have startEq : (physicalStart lowering i).val = i.val := starts i
    change (lowering i).width = stepProducerRow i (oldSteps i) (oldDecoded i) + 1 - i.val
      at oldWidth
    change stepProducerRow (physicalStart lowering i) (steps i) (decoded i) + 1 =
      (physicalStart lowering i).val + (lowering i).width at actualStop
    change stepProducerRow (physicalStart lowering i) (steps i) (copiedDecoded i) =
      stepProducerRow i (oldSteps i) (oldDecoded i) at copiedProducer
    omega
  have sound : ∀ i : Fin n,
      StepSound trace (mappedSailTrace lowering steps init)
        (physicalStart lowering i) (steps i) (decoded i) := by
    intro i
    have channels := channelOutput_eq_of_producer_eq (physicalStart lowering i)
      (steps i) (decoded i) (copiedDecoded i) (sameProducer i)
    apply (stepSound_iff (physicalStart lowering i) (steps i) (decoded i)).mpr
    change execute_instruction (sailInstructionOf (physicalStart lowering i) (steps i))
        (mappedSailTrace lowering steps init (physicalStart lowering i)) =
      ZiskFv.Channels.state_effect_via_channels
        (stepChannelOutput (physicalStart lowering i) (steps i) (decoded i))
        (mappedSailTrace lowering steps init (physicalStart lowering i))
    rw [channels]
    exact (stepSound_iff (physicalStart lowering i) (steps i) (copiedDecoded i)).mp
      (copiedSound i)
  constructor
  · intro i
    have stop := mapped_producer_successor_eq_source_stop rawProgram selected lowering trace
      start addr newBinding steps newRaw atPc i
    have endpoint := prefix_succ (sourceWidth lowering) i
    change rowPrefix (sourceWidth lowering) (i.val + 1) =
      (physicalStart lowering i).val + (lowering i).width at endpoint
    constructor
    · have successor := ExecutionSpanLegacy.producer_has_successor (physicalStart lowering i)
        (steps i) (decoded i)
      rw [stop, ← endpoint] at successor
      exact successor
    · have pc := mappedSailStates_pc_of_stepSound lowering steps init i (decoded i) (sound i)
      rw [stop, ← endpoint] at pc
      simpa only [steps, trace, states (i.val + 1) (Nat.succ_le_of_lt i.isLt)] using pc
  · intro j hj
    have actual := canonical_physical_state_at_source_cut rawProgram selected lowering trace
      start addr newBinding steps newRaw atPc init regBoot j hj (fun i _ => sound i)
    simpa only [steps, trace, states j hj] using actual

/-- The ENTIRE OLD root domain yields agreement with the actual recounted
physical memory and register folds. Source selections, span room, new decode
data and all instruction/channel equalities are CONCLUSIONS of old evidence,
not new caller promises. The original seven-field seed remains unchanged. -/
theorem old_root_actual_canonical_physical_state
    (n rawLength : Nat) (oldTrace : AcceptedZiskTrace n)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (oldSteps : ∀ i : Fin n, ZiskStep oldTrace i)
    (start : Fin rawLength → Fin oldTrace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding oldTrace start addr rawProgram)
    (rawDecodes : ∀ i, RawProgramDecode oldTrace i (oldSteps i) start addr rawProgram)
    (core : ∀ i, InputsAgreeCore oldTrace (chainedSailTrace oldSteps init) i (oldSteps i))
    (pcBoot : ∀ (_ : 0 < n), ((mainOfTable oldTrace.program oldTrace.mainTable).pc 0).val =
      (init.regs.get? Register.PC).elim 0 BitVec.toNat)
    (aligned : StepRowsAligned oldTrace oldSteps (fun i => rowDecode_of_programDecode oldTrace i
      (programDecode_of_rawProgramDecode oldTrace i (oldSteps i) start addr rawProgram
        binding (rawDecodes i))))
    (bootSeed : BootSegmentMemorySeed oldTrace (chainedSailTrace oldSteps init) oldSteps)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (avoid : ∀ i, RowOutsideDefectRegion oldTrace i (oldSteps i)) :
    ∃ selected : Fin n → Fin rawLength,
      ∃ lowering : ∀ i, SuccessfulRowLowering (rawProgram (selected i)),
        ∃ room : sourceEnd lowering ≤ oldTrace.mainTable.table.length,
          ∀ (j : Nat) (hj : j ≤ n),
            (chainedSailStates oldSteps init j).mem =
                replayMemoryAfterBusRows init.mem
                  (((actualMainMutablePhysicalSlots
                    (recountWithinMain oldTrace (sourceEnd lowering) room)).take
                    (rowPrefix (sourceWidth lowering) j)).flatten) ∧
              (∀ k : Fin 32, k ≠ 0 →
                (chainedSailStates oldSteps init j).regs.get? (reg_of_fin k) =
                  some (cast (by rw [register_type_reg_of_fin_equiv])
                    (actualPhysicalRegFile
                      (recountWithinMain oldTrace (sourceEnd lowering) room)
                      (rowPrefix (sourceWidth lowering) j)
                      (prefix_mono (sourceWidth lowering) hj) k))) := by
  obtain ⟨selected, lowering, room, starts, selectedPc, states, copiedSound,
      rawWitness, readInputs⟩ :=
    old_root_canonical_comparison n rawLength oldTrace init oldSteps start addr rawProgram
      binding rawDecodes core pcBoot aligned bootSeed regBoot avoid
  exact ⟨selected, lowering, room,
    (actual_physical_states_of_canonical_data oldTrace init oldSteps start addr rawProgram
      binding rawDecodes selected lowering room starts selectedPc states copiedSound rawWitness
      regBoot).2⟩

/-- The ACTUAL current public Root caller domain constructs ONE shared source
parse and its actual physical state comparison. All sixteen caller types are
the existing current definitions; selected words, source success, placement
and copied decode/state data are derived, never extra caller promises.
This remains the legacy public placement domain, not a mapped Root cutover. -/
theorem root_domain_parsed_canonical_physical_state
    (n rawLength : Nat) (oldTrace : AcceptedZiskTrace n)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (oldSteps : ∀ i : Fin n, ZiskStep oldTrace i)
    (start : Fin rawLength → Fin oldTrace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding oldTrace start addr rawProgram)
    (rawDecodes : ∀ i, RawProgramDecode oldTrace i (oldSteps i) start addr rawProgram)
    (core : ∀ i, InputsAgreeCore oldTrace (chainedSailTrace oldSteps init) i (oldSteps i))
    (pcBoot : ∀ (_ : 0 < n), ((mainOfTable oldTrace.program oldTrace.mainTable).pc 0).val =
      (init.regs.get? Register.PC).elim 0 BitVec.toNat)
    (aligned : StepRowsAligned oldTrace oldSteps (fun i => rowDecode_of_programDecode oldTrace i
      (programDecode_of_rawProgramDecode oldTrace i (oldSteps i) start addr rawProgram
        binding (rawDecodes i))))
    (bootSeed : BootSegmentMemorySeed oldTrace (chainedSailTrace oldSteps init) oldSteps)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (avoid : ∀ i, RowOutsideDefectRegion oldTrace i (oldSteps i)) :
    ∃ selected : Fin n → Fin rawLength,
      ∃ lowering : ∀ i, SuccessfulRowLowering (rawProgram (selected i)),
        ∃ room : sourceEnd lowering ≤ oldTrace.mainTable.table.length,
          CanonicalSourceParser.canonicalParse oldTrace addr rawProgram n =
              some (List.ofFn (fun i => (⟨selected i, lowering i⟩ :
                Σ k, SuccessfulRowLowering (rawProgram k))), sourceEnd lowering) ∧
            (∀ last : Fin n, last.val + 1 = n → sourceEnd lowering =
              stepProducerRow last (oldSteps last) (rowDecode_of_programDecode oldTrace last
                (programDecode_of_rawProgramDecode oldTrace last (oldSteps last) start addr
                  rawProgram binding (rawDecodes last))) + 1) ∧
            (∀ i : Fin n,
              rowPrefix (sourceWidth lowering) (i.val + 1) < oldTrace.mainTable.table.length ∧
                (chainedSailStates oldSteps init (i.val + 1)).regs.get? Register.PC =
                  some (register_type_pc_equiv ▸ BitVec.ofNat 64
                    ((mainOfTable oldTrace.program oldTrace.mainTable).pc
                      (rowPrefix (sourceWidth lowering) (i.val + 1))).val)) ∧
            (∀ (j : Nat) (hj : j ≤ n),
              (chainedSailStates oldSteps init j).mem =
                  replayMemoryAfterBusRows init.mem
                    (((actualMainMutablePhysicalSlots
                      (recountWithinMain oldTrace (sourceEnd lowering) room)).take
                      (rowPrefix (sourceWidth lowering) j)).flatten) ∧
                (∀ k : Fin 32, k ≠ 0 →
                  (chainedSailStates oldSteps init j).regs.get? (reg_of_fin k) =
                    some (cast (by rw [register_type_reg_of_fin_equiv])
                      (actualPhysicalRegFile
                        (recountWithinMain oldTrace (sourceEnd lowering) room)
                        (rowPrefix (sourceWidth lowering) j)
                        (prefix_mono (sourceWidth lowering) hj) k)))) := by
  obtain ⟨selected, lowering, room, starts, selectedPc, states, copiedSound,
      rawWitness, readInputs⟩ :=
    old_root_canonical_comparison n rawLength oldTrace init oldSteps start addr rawProgram
      binding rawDecodes core pcBoot aligned bootSeed regBoot avoid
  refine ⟨selected, lowering, room, ?_, ?_, ?_⟩
  · exact CanonicalSourceParser.canonicalParse_complete oldTrace start addr rawProgram binding
      selected lowering room (by intro i; rw [starts i]; exact (selectedPc i).symm)
  · intro last final
    have width := source_width_at_selected_pc oldTrace last (oldSteps last)
      start addr rawProgram binding (rawDecodes last) (selected last) (lowering last)
      (selectedPc last).symm
    have placement := ExecutionSpanLegacy.producer_eq_index_or_succ last (oldSteps last)
      (rowDecode_of_programDecode oldTrace last
        (programDecode_of_rawProgramDecode oldTrace last (oldSteps last) start addr rawProgram
          binding (rawDecodes last)))
    have endpoint := prefix_succ (sourceWidth lowering) last
    change rowPrefix (sourceWidth lowering) (last.val + 1) =
      sourceStart lowering last + (lowering last).width at endpoint
    rw [final, starts last] at endpoint
    change sourceEnd lowering = last.val + (lowering last).width at endpoint
    change (lowering last).width = stepProducerRow last (oldSteps last)
      (rowDecode_of_programDecode oldTrace last
        (programDecode_of_rawProgramDecode oldTrace last (oldSteps last) start addr rawProgram
          binding (rawDecodes last))) + 1 - last.val at width
    omega
  · exact actual_physical_states_of_canonical_data oldTrace init oldSteps start addr rawProgram
      binding rawDecodes selected lowering room starts selectedPc states copiedSound rawWitness
      regBoot

end ZiskFv.Compliance.SerializedExecutionRows
