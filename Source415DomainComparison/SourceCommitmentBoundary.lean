import Source415DomainComparison.ForwardCompletion

/-! Boundary of the proved forward direction. The old16 contract has no
committed bus124/125 provider tables. Completion preserves all old physical
execution tables but chooses these two missing source histograms. It cannot
preserve both arbitrary external base commitments. This is NOT a counterexample
to full upstream PIL validity: an external real-source commitment would need
its actual source equations/projection relation, not a new caller promise.
No hypothesis below is added to either accepted contract or root theorem.
-/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open PackedVirtualTableSources
open _root_.Extraction.PackedVirtualTables (source125)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

 theorem forward_source125_independent {p : Nat} {program : Program p}
    (old : OldWitness p program) (hc : old.Constraints) (hb : old.BalancedChannels)
    (left right : Witness FGL) :
    project (forwardRaw old hc hb left) source125 =
      project (forwardRaw old hc hb right) source125 :=
  (forwardRaw_projections old hc hb left).2.2.2.2.1.trans
    (forwardRaw_projections old hc hb right).2.2.2.2.1.symm

/-- The exact source125 projection cannot be an identity on arbitrary external
bases under old HC+HB alone. The two explicit bases distinguish that claim from
preservation of the original model's actual execution-table projection. -/
 theorem forward_not_arbitrary_source125_identity {p : Nat} {program : Program p}
    (old : OldWitness p program) (hc : old.Constraints) (hb : old.BalancedChannels) :
    ¬ (∀ base : Witness FGL,
      project (forwardRaw old hc hb base) source125 = project base source125) := by
  intro identity
  have zero := identity (fun _ => 0)
  have one := identity (fun _ => 1)
  have different : project (fun _ => (0 : FGL)) source125 =
      project (fun _ => (1 : FGL)) source125 :=
    zero.symm.trans ((forward_source125_independent old hc hb _ _).trans one)
  have atZero := congrFun different (binaryIndex ⟨0, by decide⟩)
  exact (zero_ne_one : (0 : FGL) ≠ 1) atZero

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
