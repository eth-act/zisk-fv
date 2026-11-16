import ZiskFv.Compliance.TraceLevelExport.CanonicalSourceParser
import ZiskFv.Compliance.TraceLevelExport.CanonicalPhysicalState

/-!
# Checked parsing and actual physical state at the next source cut

The parse consumes the full source-width prefix. Its continuation PC and its
register/memory state are the existing actual-Main refinement, not new parser
oracles. Expanded JALR's internal row is retained in both physical folds and
never receives a fictitious Sail step. This does not prove runtime completion.
-/

namespace ZiskFv.Compliance.CanonicalSourceParser

open CanonicalExecutionRows RawProgramBinding SerializedExecutionRows
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

include atPc

/-- The parser's derived next-source boundary has the real retired PC and the
actual physical register/memory fold. Soundness is required only for preceding
architectural instructions, exactly as in the existing physical-cut induction. -/
theorem parsed_next_source_cut
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (i j : Fin m) (next : j.val = i.val + 1)
    (sounds : ∀ k : Fin m, k.val < j.val →
      StepSound trace (mappedSailTrace L steps init)
        (physicalStart L k) (steps k) (D k)) :
    canonicalParse trace addr rawProgram m =
        some (List.ofFn (fun k => (⟨selected k, L k⟩ :
          Σ k, SuccessfulRowLowering (rawProgram k))), sourceEnd L) ∧
      (mappedSailTrace L steps init (physicalStart L j)).regs.get? Register.PC =
        some (register_type_pc_equiv ▸ BitVec.ofNat 64
          ((mainOfTable trace.program trace.mainTable).pc (physicalStart L j).val).val) ∧
      (mappedSailStates L steps init j.val (Nat.le_of_lt j.isLt)).mem =
        replayMemoryAfterBusRows init.mem
          (((actualMainMutablePhysicalSlots trace).take
            (rowPrefix (sourceWidth L) j.val)).flatten) ∧
      (∀ k : Fin 32, k ≠ 0 →
        (mappedSailStates L steps init j.val (Nat.le_of_lt j.isLt)).regs.get? (reg_of_fin k) =
          some (cast (by rw [register_type_reg_of_fin_equiv])
            (actualPhysicalRegFile trace (rowPrefix (sourceWidth L) j.val)
              (prefix_mono (sourceWidth L) (Nat.le_of_lt j.isLt)) k))) := by
  have parsed := canonicalParse_at_source_starts rawProgram selected L trace
    start addr binding (by simpa only [physicalStart_val] using atPc)
  have pc := mapped_pc_at_next_source_start rawProgram selected L trace start addr
    binding steps rawDecodes atPc init i j next (sounds i (by omega))
  have physical := canonical_physical_state_at_source_cut rawProgram selected L trace
    start addr binding steps rawDecodes atPc init regBoot j.val (Nat.le_of_lt j.isLt) sounds
  exact ⟨parsed, pc, physical⟩

end Source

/-- A nonfinal width2 source lowering is the real expanded JALR arm. The next
architectural step is at row2; its PC and memory/register prestate follow the
entire actual two-row physical fold. The remaining lowering is still consumed
by the parser, without forcing width1 or using old starts=i. -/
theorem nonfinal_expansion_parsed_physical_cut {rawLength : Nat}
    (rawProgram : Fin rawLength → BitVec 32) (selected : Fin 2 → Fin rawLength)
    (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
    (trace : AcceptedZiskTrace (sourceEnd L))
    (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (steps : ∀ i, ZiskStep trace (physicalStart L i))
    (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
      start addr rawProgram)
    (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
      (physicalStart L i).val = addr (selected i))
    (two : (L (0 : Fin 2)).width = 2)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (sound : StepSound trace (mappedSailTrace L steps init)
      (physicalStart L (0 : Fin 2)) (steps (0 : Fin 2))
      (rowDecode_of_programDecode trace (physicalStart L (0 : Fin 2))
        (programDecode_of_rawProgramDecode trace (physicalStart L (0 : Fin 2))
          (steps (0 : Fin 2)) start addr rawProgram binding (rawDecodes (0 : Fin 2))))) :
    sourceStart L (1 : Fin 2) = 2 ∧
      canonicalParse trace addr rawProgram 2 =
        some (List.ofFn (fun k => (⟨selected k, L k⟩ :
          Σ k, SuccessfulRowLowering (rawProgram k))), 2 + (L (1 : Fin 2)).width) ∧
      (mappedSailTrace L steps init (physicalStart L (1 : Fin 2))).regs.get? Register.PC =
        some (register_type_pc_equiv ▸ BitVec.ofNat 64
          ((mainOfTable trace.program trace.mainTable).pc (physicalStart L (1 : Fin 2)).val).val) ∧
      (mappedSailStates L steps init 1 (by decide)).mem =
        replayMemoryAfterBusRows init.mem
          (((actualMainMutablePhysicalSlots trace).take 2).flatten) ∧
      (∀ k : Fin 32, k ≠ 0 →
        (mappedSailStates L steps init 1 (by decide)).regs.get? (reg_of_fin k) =
          some (cast (by rw [register_type_reg_of_fin_equiv])
            (actualPhysicalRegFile trace (rowPrefix (sourceWidth L) 1)
              (prefix_mono (sourceWidth L) (by decide : 1 ≤ 2)) k))) := by
  obtain ⟨second, parsed⟩ := nonfinal_expansion_canonicalParse rawProgram selected L trace
    start addr binding (by simpa only [physicalStart_val] using atPc) two
  have cut := parsed_next_source_cut rawProgram selected L trace start addr binding steps
    rawDecodes atPc init regBoot (0 : Fin 2) (1 : Fin 2) rfl (by
      intro k before
      have zero : k = (0 : Fin 2) := by apply Fin.ext; change k.val = 0; omega
      subst k
      exact sound)
  have cutRow : rowPrefix (sourceWidth L) 1 = 2 := second
  refine ⟨second, parsed, cut.2.1, ?_, cut.2.2.2⟩
  have memory := cut.2.2.1
  change (mappedSailStates L steps init 1 (by decide)).mem =
    replayMemoryAfterBusRows init.mem
      (((actualMainMutablePhysicalSlots trace).take (rowPrefix (sourceWidth L) 1)).flatten)
    at memory
  simpa only [cutRow] using memory

end ZiskFv.Compliance.CanonicalSourceParser
