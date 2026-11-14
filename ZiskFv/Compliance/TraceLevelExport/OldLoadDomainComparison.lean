import ZiskFv.Soundness

/-!
# Additive old-root-domain comparison for the seven-load PC retarget

This module is built against the OLD load claim/Core/defect definitions, not
425/426. The old root theorem already proves its own register/memory/PC
induction under OLD Sail-input-PC avoidance. Reusing that checked theorem and
its actual architectural retire proves the Main/state PC tie without a new
bridge premise and without invoking a new Main-PC avoidance hypothesis.

The result-only predicate below transcribes precisely the proposed425 change:
load PC bounds move to Main.pc; all six narrow-load forge conjuncts and all
non-load cases stay unchanged. It is NOT a replacement root argument or an
independent caller promise. The old unwrapped load predicate is untouched.
-/

namespace ZiskFv.Compliance.OldLoadDomainComparison

open RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

/-- Exact result-only transcription of the seven proposed PC-domain changes. -/
def loadAvoidAtMain {n : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) : ZiskStep trace i → Prop
  | .ld _ => MainSequentialPcDomain trace i
  | .lbu _ | .lb _ =>
      MainSequentialPcDomain trace i ∧
        ¬ Defects.MemAlignNarrowLoadLaneForge trace.program trace.witness
          1 (busLd trace i (Pilot.execRowOf trace i)).e1 ∧
        ¬ Defects.MemAlignSkippableProveForge trace.program trace.witness
          (busLd trace i (Pilot.execRowOf trace i)).e1
  | .lhu _ | .lh _ =>
      MainSequentialPcDomain trace i ∧
        ¬ Defects.MemAlignNarrowLoadLaneForge trace.program trace.witness
          2 (busLd trace i (Pilot.execRowOf trace i)).e1 ∧
        ¬ Defects.MemAlignSkippableProveForge trace.program trace.witness
          (busLd trace i (Pilot.execRowOf trace i)).e1
  | .lwu _ | .lw _ =>
      MainSequentialPcDomain trace i ∧
        ¬ Defects.MemAlignNarrowLoadLaneForge trace.program trace.witness
          4 (busLd trace i (Pilot.execRowOf trace i)).e1 ∧
        ¬ Defects.MemAlignSkippableProveForge trace.program trace.witness
          (busLd trace i (Pilot.execRowOf trace i)).e1
  | step => RowOutsideDefectRegion trace i step

/-- This local algebraic step is used only AFTER the whole old-root theorem
below derives its bridge. It is not itself the no-stronger-domain certificate. -/
private theorem load_avoid_iff_of_derived_pc {n : Nat}
    (trace : AcceptedZiskTrace n) (binding : SailTrace n) (i : Fin n)
    (step : ZiskStep trace i) (core : InputsAgreeCore trace binding i step)
    (bridge : ((mainOfTable trace.program trace.mainTable).pc i.val).val =
      ((binding i).regs.get? Register.PC).elim 0 BitVec.toNat) :
    RowOutsideDefectRegion trace i step ↔ loadAvoidAtMain trace i step := by
  cases step <;> try rfl
  all_goals
    have pc := h_pc_bridge_of_pcBridge bridge core.h_opcode_assumptions.1
    simp only [RowOutsideDefectRegion, loadAvoidAtMain, MainSequentialPcDomain,
      mainPcVal, SequentialPcDomain, pc]

/-- The ENTIRE OLD root domain implies the derived PC tie and the exact new
load avoidance domain. No h_bridge/new-domain/read-presence binder is added.
The checked root used here still has the OLD Sail-input-PC load predicate. -/
theorem old_root_domain_pc_and_load_avoid
    (n rawLength : Nat) (trace : AcceptedZiskTrace n)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecodes : ∀ i : Fin n, RawProgramDecode trace i (steps i) start addr rawProgram)
    (core : ∀ i : Fin n, InputsAgreeCore trace (chainedSailTrace steps init) i (steps i))
    (pcBoot : ∀ (_ : 0 < n), ((mainOfTable trace.program trace.mainTable).pc 0).val =
      (init.regs.get? Register.PC).elim 0 BitVec.toNat)
    (rowsAligned : StepRowsAligned trace steps (fun i => rowDecode_of_programDecode trace i
      (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
        binding (rawDecodes i))))
    (bootSeed : BootSegmentMemorySeed trace (chainedSailTrace steps init) steps)
    (regBoot : ∀ k : Fin 32, k ≠ 0 →
      init.regs.get? (reg_of_fin k) =
        some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (oldAvoid : ∀ i : Fin n, RowOutsideDefectRegion trace i (steps i)) :
    ∀ i : Fin n,
      (((mainOfTable trace.program trace.mainTable).pc i.val).val =
        ((chainedSailTrace steps init i).regs.get? Register.PC).elim 0 BitVec.toNat) ∧
      (RowOutsideDefectRegion trace i (steps i) ↔ loadAvoidAtMain trace i (steps i)) ∧
      loadAvoidAtMain trace i (steps i) := by
  have sound := root_soundness n rawLength trace init steps start addr rawProgram
    binding rawDecodes core pcBoot rowsAligned bootSeed regBoot oldAvoid
  have bridge (j : Nat) (hj : j < n) :
      ((mainOfTable trace.program trace.mainTable).pc j).val =
        ((chainedSailTrace steps init ⟨j, hj⟩).regs.get? Register.PC).elim 0 BitVec.toNat := by
    cases j with
    | zero => simpa only [chainedSailTrace, chainedSailStates] using pcBoot hj
    | succ j =>
        exact pcBridge_succ_of_stepSound (chainedSailTrace_retireChain steps init)
          rowsAligned j hj (sound ⟨j, Nat.lt_of_succ_lt hj⟩)
  intro i
  have tie := bridge i.val i.isLt
  have equivalent := load_avoid_iff_of_derived_pc trace (chainedSailTrace steps init)
    i (steps i) (core i) tie
  exact ⟨tie, equivalent, equivalent.mp (oldAvoid i)⟩

end ZiskFv.Compliance.OldLoadDomainComparison
