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

/-- RegisterBoundary as a Clean `GeneralFormalCircuit`.  `Assumptions := True` and `Spec := True`:
    the component asserts no algebraic relation; its only obligations are the two bus emissions'
    `MemBusChannel.Guarantees = True` requirements. -/
def circuit : GeneralFormalCircuit FGL RegisterBoundaryRow unit  where
  name := "RegisterBoundary"
  main := main
  channelsWithRequirements := [MemBusChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel
      [ MemBusChannel.emitted (-1) (bootMessageExpr row)
      , MemBusChannel.emitted 1 (reloadMessageExpr row) ]
  Assumptions := fun _ _ => True
  Spec := fun _ _ _ => True
  ProverAssumptions := fun _ _ _ => True
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    intro _
    simp [MemBusChannel]
  completeness := by
    circuit_proof_start [MemBusChannel]

/-! ## The component-owned register enumeration

`reg` used to be a free witness cell. That was looser than ZisK in a way that matters: the register
address is a **compile-time constant** there, and a prover has no say in it.

* PIL: `main.pil:535-537` boots each register with
  `global_init_mem(sel: 1, addr: ireg + REGS_IN_MAIN_FROM, value: zeros)` inside a compile-time
  `for` loop, and `main.pil:445-450` reloads each with `reg_pre_load(addr: ireg + REGS_IN_MAIN_FROM,
  ...)` in the same loop. `std_direct.pil`'s `direct_initial_checks` rejects any expression of
  degree > 0 in a direct update, so the address cannot be witness data at all.
* Extraction, which is what this proof consumes: `build/extraction/Extraction/Main.lean` carries
  exactly **62** `mem_op = 3` memory-bus direct terms, at literal addresses **1 through 31, each
  twice** — the boot pull and the reload push for `x1` .. `x31`.

So the register index is component-owned data, not prover data, and it belongs in the fixed schema.
Pinning it costs no trust: it *reduces* what a prover may supply, which is the safe direction for a
provider. It also gives the row count for free — `Table.fixed_domain` bounds any materialized
prefix by `capacity`, so a witness cannot carry a 32nd boundary row.

What this repairs, concretely: two rows could previously carry the same `reg`, so one register could
have two boot anchors and its accesses could split into two disjoint chains. The register telescope
cannot close over that. -/

/-- `REGS_IN_MAIN` (`main.pil:15-17`): the registers `x1` .. `x31` that Main tracks. -/
def registerBoundaryCapacity : Nat := 31

/-- The four effective `RegisterBoundaryRow` slots map to three raw witness cells plus the one
    component-owned `reg` column. `ProvableStruct` order puts `reg` at slot `0`. -/
def registerBoundaryFixedLayout (slot : Fin 4) : Sum (Fin 3) (Fin 1) :=
  if h_reg : slot.val = 0 then
    .inr ⟨0, by omega⟩
  else
    .inl ⟨slot.val - 1, by have := slot.isLt; omega⟩

/-- Register `x(i+1)` at physical row `i`, mirroring `ireg + REGS_IN_MAIN_FROM` with
    `REGS_IN_MAIN_FROM = 1`. -/
def registerBoundaryFixedValues (_slot : Fin 1)
    (row : Fin registerBoundaryCapacity) : FGL :=
  ((row.val + 1 : ℕ) : FGL)

/-- Component-owned RegisterBoundary fixed schema. -/
def registerBoundaryFixedColumns : IndexedFixedColumns FGL 3 where
  capacity := registerBoundaryCapacity
  capacity_pos := by decide
  effectiveWidth := 4
  fixedWidth := 1
  layout := registerBoundaryFixedLayout
  values := registerBoundaryFixedValues

/-- The three raw witness cells of a boundary row, in `ProvableStruct` order minus `reg`. -/
def rawRow (row : RegisterBoundaryRow FGL) : Array FGL :=
  #[row.reloadTimestamp, row.reloadValue_0, row.reloadValue_1]

/-- Materialization of a boundary row, as a literal: the fixed `reg` cell then the three raw
    cells. `Array.ofFn` over the literal width `4` reduces definitionally. -/
theorem materialize_rawRow (index : ℕ) (row : RegisterBoundaryRow FGL) :
    registerBoundaryFixedColumns.materialize index (rawRow row)
      = #[registerBoundaryFixedColumns.fixedAt 0 index,
          row.reloadTimestamp, row.reloadValue_0, row.reloadValue_1] := by
  rfl

/-- **What materialization actually does to a boundary row: it overwrites `reg`.**

    The decoded row keeps the three witness cells and takes its register index from the
    component's fixed schema, *whatever the prover wrote*. This is the repair, stated:
    the register index is component-owned data, so it is not a degree of freedom. -/
theorem eval_rawRow_materialize_reg (index : Nat) (data : ProverData FGL)
    (row : RegisterBoundaryRow FGL) :
    Eval.eval
      (Environment.fromArray (registerBoundaryFixedColumns.materialize index (rawRow row)) data)
      (varFromOffset (F := FGL) RegisterBoundaryRow 0)
      = { row with reg := registerBoundaryFixedColumns.fixedAt 0 index } := by
  cases row
  simp_all [registerBoundaryFixedColumns, IndexedFixedColumns.materialize,
    IndexedFixedColumns.fixedAt, registerBoundaryFixedLayout, registerBoundaryFixedValues,
    rawRow, Environment.fromArray, ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.varFromOffset_eq_varFromOffset, ProvableType.eval_field,
    ProvableStruct.varFromOffset, ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, Expression.eval,
    ProvableStruct.varFromOffset.go, explicit_provable_type, circuit_norm]

/-- **A materialized boundary row decodes back to itself, once `reg` agrees with the fixed cell.**
    The mirror of Main's `eval_mainRawRow_materialize`. -/
theorem eval_rawRow_materialize (index : Nat) (data : ProverData FGL)
    (row : RegisterBoundaryRow FGL)
    (h_reg : row.reg = registerBoundaryFixedColumns.fixedAt 0 index) :
    Eval.eval
      (Environment.fromArray (registerBoundaryFixedColumns.materialize index (rawRow row)) data)
      (varFromOffset (F := FGL) RegisterBoundaryRow 0) = row := by
  rw [eval_rawRow_materialize_reg, ← h_reg]

/-- **Each register has exactly one boundary row.** Row `i` carries register `x(i+1)`, so two rows
    carrying the same register are the same row.

    This is what the fidelity repair buys, and what the register telescope's coverage argument
    needs: the boot pull for a register is unique, so that register's accesses cannot split into
    two disjoint chains. Before the repair `reg` was a free witness cell and this was false. -/
theorem materialized_reg_eq (index : Nat) (h_lt : index < registerBoundaryCapacity)
    (data : ProverData FGL) (row : RegisterBoundaryRow FGL) :
    (Eval.eval
      (Environment.fromArray (registerBoundaryFixedColumns.materialize index (rawRow row)) data)
      (varFromOffset (F := FGL) RegisterBoundaryRow 0)).reg = ((index + 1 : ℕ) : FGL) := by
  rw [eval_rawRow_materialize_reg]
  simp [IndexedFixedColumns.fixedAt, registerBoundaryFixedColumns, registerBoundaryFixedValues,
    Nat.mod_eq_of_lt h_lt]

/-- Two boundary rows carrying the same register sit at the same index. -/
theorem materialized_index_unique {i j : Nat}
    (h_i : i < registerBoundaryCapacity) (h_j : j < registerBoundaryCapacity)
    (data : ProverData FGL) (rowI rowJ : RegisterBoundaryRow FGL)
    (h : (Eval.eval
            (Environment.fromArray (registerBoundaryFixedColumns.materialize i (rawRow rowI)) data)
            (varFromOffset (F := FGL) RegisterBoundaryRow 0)).reg
        = (Eval.eval
            (Environment.fromArray (registerBoundaryFixedColumns.materialize j (rawRow rowJ)) data)
            (varFromOffset (F := FGL) RegisterBoundaryRow 0)).reg) :
    i = j := by
  rw [materialized_reg_eq i h_i, materialized_reg_eq j h_j] at h
  have h_val := congrArg Fin.val h
  rw [Fin.val_natCast, Fin.val_natCast,
    Nat.mod_eq_of_lt (by simp [registerBoundaryCapacity] at h_i ⊢; omega),
    Nat.mod_eq_of_lt (by simp [registerBoundaryCapacity] at h_j ⊢; omega)] at h_val
  omega

/-- RegisterBoundary as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL :=
  { circuit := circuit
    rawWidth := 3
    fixedColumns := some registerBoundaryFixedColumns }

/-- **The register index of a materialized row, for an arbitrary raw row.** Slot `0` is the fixed
    cell, so this holds whatever the prover put in the witness cells — it does not need the raw row
    to have come from a `RegisterBoundaryRow`. -/
theorem reg_of_materialize (index : Nat) (raw : Array FGL) (data : ProverData FGL) :
    (Eval.eval
      (Environment.fromArray (registerBoundaryFixedColumns.materialize index raw) data)
      component.rowInputVar).reg
      = registerBoundaryFixedColumns.fixedAt 0 index := by
  simp [Air.Flat.Component.rowInputVar, component,
    registerBoundaryFixedColumns, IndexedFixedColumns.materialize,
    registerBoundaryFixedLayout, Environment.fromArray,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.varFromOffset_eq_varFromOffset, ProvableType.eval_field,
    ProvableStruct.varFromOffset, ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, Expression.eval,
    ProvableStruct.varFromOffset.go, explicit_provable_type, circuit_norm]


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
  simp only [component, circuit, Component.exposedChannels, expose, List.mem_singleton, List.map_cons, List.map_nil]

end ZiskFv.AirsClean.RegisterBoundary
