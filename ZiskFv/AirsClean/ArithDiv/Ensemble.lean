import ZiskFv.AirsClean.ArithDiv.Circuit
import Clean.Air.Vm

/-!
# ArithDiv minimal ensemble (Phase C4 — D-5)

Assembles the ArithDiv DIV carry-chain `Component` into a minimal
`Air.Flat` ensemble and takes it through `toFormal` to a
`FormalEnsemble`, proving the ensemble-assembly API
(`SoundEnsemble.empty` / `addTable` / `toFormal`) composes for the
ArithDiv Component.

ArithDiv's `main` has **no channel interaction** (the Arith op-bus is a
shared channel, wired family-terminal — plan phase C7/CZ). So the
ensemble is just the single ArithDiv Component with empty channels —
`addTable`'s `channelsWithGuarantees ⊆ finished` and
`channelsWithRequirements`-disjointness obligations are trivially
discharged (both channel lists are empty). No `addFinishedChannel`
step is needed.

`toFormal`'s `AssumptionsConsistency` obligation discharges because the
Component carries `Assumptions := True` (plan D-2 / F-4 — the 11-clause
carry-chain `Spec` follows from the 11 definitional `assertZero`s, no
caller assumption). The resulting ensemble soundness is genuine — not
vacuous: its trust closure is `arithDiv_circuit_completeness` (a
declared completeness-direction axiom), no `sorry`, no `False`-style
assumption.

## Trust note

No axioms added here. Closure: `arithDiv_circuit_completeness`
(completeness-direction, non-security-critical) via the Component.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks
open Air.Flat

/-- The minimal ArithDiv ensemble: the single ArithDiv DIV carry-chain
    Component, no channels, taken through `toFormal` to a
    `FormalEnsemble`.

    `toFormal`'s `AssumptionsConsistency` discharges because the
    Component carries `Assumptions := True` (plan D-2 / F-4). The
    ensemble soundness is genuine — its trust closure is
    `arithDiv_circuit_completeness`, no `sorry`. -/
def arithDivEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable component
        (by simp [circuit_norm, component, circuit, arithDivElaborated])
        (by simp [circuit_norm, component, circuit, arithDivElaborated])
    |>.toFormal (fun _ => True) (fun _ => True)
        (by
          -- AssumptionsConsistency: the ArithDiv Component carries
          -- `Assumptions := True`, so every witness table's per-row
          -- assumption is `True`.
          intro _ _ table h_mem row _
          have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
          simp only [circuit_norm, Ensemble.allTables] at h
          rcases h with h | h <;>
            (rw [h]
             simp [circuit_norm, Air.Flat.Component.Assumptions,
               component, circuit, arithDivElaborated]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.ArithDiv
