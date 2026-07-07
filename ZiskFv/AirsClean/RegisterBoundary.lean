import Clean.Circuit.Basic
import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks
import ZiskFv.Channels.MemoryBus

/-!
# RegisterBoundary Clean component (issue #225) — register-file boot / reload MemBus emissions

ZisK's register memory-consistency argument telescopes on the shared MemBus.  The interior
per-row `MEMORY_REG_OP` (`mem_op = 3`) push-prev / pull-current pairs are emitted by the Main
component (`Main/Constraints.lean`).  This component supplies the two *boundary* terms that close
the per-register chain, which ZisK's PIL emits outside the per-row Main access loop:

* **boot** — `global_init_mem` (`mem/pil/mem.pil:507-508`, per-register call site
  `main/pil/main.pil:535-537`): `direct_global_update_assumes([MEMORY_REG_OP, addr, 0, 8, ...zeros])`,
  seeding every tracked register to value 0 at timestamp 0.  It is a consumer/pull, so it rides a
  `-1` multiplicity.
* **reload** — `reg_pre_load` "Proves the last access." (`main/pil/main.pil:450`):
  `mem_proves(MEMORY_REG_OP, addr, last_reg_mem_step, last_reg_value)`, a provider/push at `+1`.

One component row models one register's boundary pair (the PIL `for (ireg ...)` loop iteration),
carrying the register pointer plus the reload timestamp and value; the boot value is the literal 0.
The `mem_op = 3` messages of the whole ensemble balance when boot(`-1`) + reload(`+1`) telescope
against Main's push-prev(`+`) / pull-current(`-`) — see `Compliance/RegisterMemBusBalance.lean`.

Scope: this is the single-segment global boot + last-access reload only.  The cross-segment
continuation terms (the `MAIN_CONTINUATION_ID` block and `main.pil:454`'s
`sel:(1-main_last_segment)` continuation pull) are out of scope (#103/#76).

## Trust note

`Assumptions := True` makes the ensemble `AssumptionsConsistency` obligation trivial (the added
`rw [h]; trivial` disjunct in `fullRv64imSoundEnsemble_assumptionsConsistency`).  The component has
no algebraic constraints: it is a deliberately under-constrained *provider* of boundary MemBus
messages.  That is sound in the soundness direction — an under-constrained provider never makes
`root_soundness` vacuous (the anti-laundering hazard, an overstrong validator, runs the other way).
The bus emissions carry `MemBusChannel.Guarantees = True`, so no caller assumption is needed.  No
axioms.
-/

namespace ZiskFv.AirsClean.RegisterBoundary

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

/-- One register's boundary data: its MemBus pointer, and the reload (last-access) timestamp and
    value.  The boot message is always `(mem_op=3, ptr=reg, timestamp=0, value=0)`. -/
structure RegisterBoundaryRow (F : Type) where
  reg : F
  reloadTimestamp : F
  reloadValue_0 : F
  reloadValue_1 : F
deriving ProvableStruct

/-- The boot pull message `[MEMORY_REG_OP, reg, 0, 8, 0, 0]` (`mem.pil:507-508`). -/
@[reducible]
def bootMessageExpr (row : Var RegisterBoundaryRow FGL) : MemBusMessage (Expression FGL) :=
  { mem_op := 3
    ptr := row.reg
    timestamp := 0
    width := 8
    value_0 := 0
    value_1 := 0 }

/-- The reload push message `[MEMORY_REG_OP, reg, reloadTimestamp, 8, reloadValue_0, reloadValue_1]`
    (`main.pil:450`, `reg_pre_load` "Proves the last access."). -/
@[reducible]
def reloadMessageExpr (row : Var RegisterBoundaryRow FGL) : MemBusMessage (Expression FGL) :=
  { mem_op := 3
    ptr := row.reg
    timestamp := row.reloadTimestamp
    width := 8
    value_0 := row.reloadValue_0
    value_1 := row.reloadValue_1 }

/-- Value-level boot message (evaluation target for the balance witness). -/
@[reducible]
def bootMessage (row : RegisterBoundaryRow FGL) : MemBusMessage FGL :=
  { mem_op := 3
    ptr := row.reg
    timestamp := 0
    width := 8
    value_0 := 0
    value_1 := 0 }

/-- Value-level reload message (evaluation target for the balance witness). -/
@[reducible]
def reloadMessage (row : RegisterBoundaryRow FGL) : MemBusMessage FGL :=
  { mem_op := 3
    ptr := row.reg
    timestamp := row.reloadTimestamp
    width := 8
    value_0 := row.reloadValue_0
    value_1 := row.reloadValue_1 }

theorem eval_bootMessageExpr
    (env : Environment FGL) (row : Var RegisterBoundaryRow FGL) :
    eval env (bootMessageExpr row) = bootMessage (eval env row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [bootMessageExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor

theorem eval_reloadMessageExpr
    (env : Environment FGL) (row : Var RegisterBoundaryRow FGL) :
    eval env (reloadMessageExpr row) = reloadMessage (eval env row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [reloadMessageExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor

/-- The two boundary emissions: boot pull (`-1`) then reload push (`+1`).  Bare `emit`s
    (`assumeGuarantees = false`), exactly like Main's mem emits. -/
@[circuit_norm]
def main (row : Var RegisterBoundaryRow FGL) : Circuit FGL Unit := do
  MemBusChannel.emit (-1) (bootMessageExpr row)
  MemBusChannel.emit 1 (reloadMessageExpr row)

/-- The elaborated circuit: two channel emissions, no fresh witnesses, no algebraic constraints. -/
@[reducible] def registerBoundaryElaborated :
    ElaboratedCircuit FGL RegisterBoundaryRow unit where
  name := "RegisterBoundary"
  main := main
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [MemBusChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel
      [ MemBusChannel.emitted (-1) (bootMessageExpr row)
      , MemBusChannel.emitted 1 (reloadMessageExpr row) ]
  channelsLawful := by
    simp only [circuit_norm, main, bootMessageExpr, reloadMessageExpr, MemBusChannel]

/-- RegisterBoundary as a Clean `GeneralFormalCircuit`.  `Assumptions := True` and `Spec := True`:
    the component asserts no algebraic relation; its only obligations are the two bus emissions'
    `MemBusChannel.Guarantees = True` requirements. -/
def circuit : GeneralFormalCircuit FGL RegisterBoundaryRow unit :=
  { registerBoundaryElaborated with
    Assumptions := fun _ _ => True
    Spec := fun _ _ _ => True
    ProverAssumptions := fun _ _ _ => True
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      intro _
      trivial
    completeness := by
      circuit_proof_start [MemBusChannel] }

/-- RegisterBoundary as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := { circuit := circuit }

/-- Project the generic component `Spec` to the trivial RegisterBoundary `Spec`. -/
theorem component_spec (env : Environment FGL) :
    component.Spec env = True := by
  rfl

/-- The component's MemBus interactions: the boot pull and the reload push. -/
theorem component_interactionsWith_memBus :
    component.operations.interactionsWith MemBusChannel.toRaw =
      [ ((MemBusChannel.emitted (-1) (bootMessageExpr component.rowInputVar)).toRaw)
      , ((MemBusChannel.emitted 1 (reloadMessageExpr component.rowInputVar)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw,
      [ ((MemBusChannel.emitted (-1) (bootMessageExpr component.rowInputVar)).toRaw)
      , ((MemBusChannel.emitted 1 (reloadMessageExpr component.rowInputVar)).toRaw) ]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, registerBoundaryElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons, List.map_nil]

end ZiskFv.AirsClean.RegisterBoundary
