import ZiskFv.AirsClean.FullEnsemble.Balance.RegisterChainBridges
import ZiskFv.Compliance.TraceLevelExport.Dispatcher

/-!
# The segment PC seed (`SegmentPcSeed`) — #330 Phase 5

`h_pc_bridge` is the one `InputsAgree` field present in **all 63** `Inputs_<op>` structures: it
asserts that the Main `pc` column at a row equals the Sail PC at that step. Today it is assumed
once per opcode structure, i.e. at every row.

This module replaces those with **two** premises, in the shape `BootSegmentMemorySeed` established
for memory (#185/#115):

* `boot` — the Sail PC agrees with the Main `pc` column at step `0`;
* `succ` — the Sail PC at step `j + 1` is the **next-PC mux** the Main row at `j` computes.

The reduction is genuine rather than a repackaging, because `succ` never mentions the `pc` column.
Converting "Sail's PC advanced to the mux value" into "Sail's PC equals the next row's `pc` column"
is done by the circuit's own transition constraint, via
`mainOfTable_pc_eq_nextPcMux_of_transitions_hold` — which is derived from
`AcceptedZiskTrace.transitions_hold` and costs no premise. Without that constraint `succ` would not
imply agreement at all.

`succ` is the honest content: `SailTrace` is a bare `Fin n → SailState`
(`ZiskFv/Compliance/SailTrace.lean:20`) with no chaining whatsoever, so *something* must say the
Sail states form an execution. This says it once, for every step, instead of 63 times.

## Scope

This is the PC arm only. The register fields (`h_a_*_t` / `h_b_*_t`) stay assumed; they go through
the MemBus and are Phase 4, gated on the register-partition ordering question (`main.pil:277-279`,
the #169/#19 axis). This arm is independent of that.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

variable {numInstructions : ℕ}

/-- The next-PC mux the Main row at `j` computes, in the named-column view: the value ZisK's
    transition constraint forces into row `j + 1`'s `pc`. Mirrors `pcHandshakeBetween`'s right-hand
    side (`ZiskFv/AirsClean/Main/Circuit.lean:~745`, `main.pil:90`). -/
noncomputable def nextPcMux (ziskTrace : AcceptedZiskTrace numInstructions) (j : ℕ) : FGL :=
  (mainOfTable ziskTrace.program ziskTrace.mainTable).set_pc j *
      ((mainOfTable ziskTrace.program ziskTrace.mainTable).c_0 j
        + (mainOfTable ziskTrace.program ziskTrace.mainTable).jmp_offset1 j)
    + (1 - (mainOfTable ziskTrace.program ziskTrace.mainTable).set_pc j) *
      ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc j
        + (mainOfTable ziskTrace.program ziskTrace.mainTable).jmp_offset2 j)
    + (mainOfTable ziskTrace.program ziskTrace.mainTable).flag j *
      ((mainOfTable ziskTrace.program ziskTrace.mainTable).jmp_offset1 j
        - (mainOfTable ziskTrace.program ziskTrace.mainTable).jmp_offset2 j)

/-- The two-premise PC seed: boot agreement plus the Sail execution's PC successor.

    Replaces the 63 per-opcode `h_pc_bridge` assumptions. See the module docstring for why `succ`
    is weaker than assuming agreement per row. -/
structure SegmentPcSeed
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace ziskTrace.numInstructions) where
  /-- Boot: the Sail PC at step `0` is the Main `pc` column at row `0`. -/
  boot : ∀ (h : 0 < ziskTrace.numInstructions),
    ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc 0).val
      = ((binding ⟨0, h⟩).regs.get? Register.PC).elim 0 BitVec.toNat
  /-- Execution successor: the Sail PC at step `j + 1` is the next-PC mux the Main row at `j`
      computed. States that `binding` advances as an execution; says nothing about the `pc`
      column at `j + 1`. -/
  succ : ∀ (j : ℕ) (h : j + 1 < ziskTrace.numInstructions),
    (nextPcMux ziskTrace j).val
      = ((binding ⟨j + 1, h⟩).regs.get? Register.PC).elim 0 BitVec.toNat

/-- Away from row `0` the Main `segment_l1` column is `0`, hence never `1`.

    `SEGMENT_L1` is the component-owned fixed column `[1, 0, 0, …]`
    (`Main/Circuit.lean:mainFixedValues`), so the PC transition gate is open at every row but the
    first. This makes the non-boundary side condition of
    `mainOfTable_pc_eq_nextPcMux_of_transitions_hold` **derivable** rather than a premise: the
    recurrence applies unconditionally at every `1 ≤ i`. -/
theorem mainOfTable_segment_l1_ne_one_of_pos
    {length : ℕ} {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    {table : Air.Flat.Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (index : ℕ) (h_pos : 0 < index) (h_lt : index < table.table.length)
    (h_capacity : index < ZiskFv.AirsClean.Main.mainFixedCapacity) :
    (mainOfTable program table).segment_l1 index ≠ 1 := by
  simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable_segment_l1]
  rw [mainTableRowAtOrZero_segment_l1_eq_fixedAt program table index h_lt h_component]
  cases table with
  | mk component rawRows data raw_uniform_width fixed_domain =>
    change component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
      at h_component
    subst component
    rw [Air.Flat.Table.fixedAt_of_fixedColumns _ ZiskFv.AirsClean.Main.mainFixedColumns rfl,
      ZiskFv.AirsClean.Main.mainFixedColumns_segment_l1_nonfirst index h_pos h_capacity]
    decide

/-- Every in-range Main row index is inside the component's fixed-column capacity, from the table's
    own `fixed_domain` field. Discharges the capacity side condition of
    `mainOfTable_segment_l1_ne_one_of_pos` without a premise. -/
theorem mainTable_index_lt_capacity
    {length : ℕ} {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    {table : Air.Flat.Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (index : ℕ) (h_lt : index < table.table.length) :
    index < ZiskFv.AirsClean.Main.mainFixedCapacity := by
  have h_raw : index < table.rawRows.length := by
    simpa only [Air.Flat.Table.table_length] using h_lt
  cases table with
  | mk component rawRows data raw_uniform_width fixed_domain =>
    change component = ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
      at h_component
    subst component
    exact lt_of_lt_of_le h_raw (fixed_domain ZiskFv.AirsClean.Main.mainFixedColumns rfl)

/-- **The PC arm.** From the two seed premises, the Main `pc` column agrees with the Sail PC at
    every executed step — the content of `h_pc_bridge` in all 63 `Inputs_<op>` structures.

    Row `0` is `seed.boot`. Every later row is `seed.succ` composed with the circuit's own PC
    recurrence (`mainOfTable_pc_eq_nextPcMux_of_transitions_hold`), whose non-boundary side
    condition is discharged from the fixed `SEGMENT_L1` schema rather than assumed. The circuit
    constraint is doing real work here: `succ` speaks only about the next-PC mux, never about the
    `pc` column. -/
theorem pcBridge_of_pcSeed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    (seed : SegmentPcSeed ziskTrace binding)
    (i : Fin ziskTrace.numInstructions) :
    ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc i.val).val
      = ((binding i).regs.get? Register.PC).elim 0 BitVec.toNat := by
  have h_lt : i.val < ziskTrace.mainTable.table.length := ziskTrace.mainTable_index i
  have h_isLt := i.isLt
  match h_i : i.val with
  | 0 =>
      have h_pos : 0 < ziskTrace.numInstructions := by omega
      have h_eq : i = ⟨0, h_pos⟩ := Fin.ext (by simpa using h_i)
      subst h_eq
      simpa using seed.boot h_pos
  | j + 1 =>
      have h_succ_lt : j + 1 < ziskTrace.numInstructions := by omega
      have h_index_lt : i.val < ziskTrace.mainTable.length := by
        simpa only [Air.Flat.Table.table_length] using h_lt
      have h_not_boundary :
          (mainOfTable ziskTrace.program ziskTrace.mainTable).segment_l1 i.val ≠ 1 :=
        mainOfTable_segment_l1_ne_one_of_pos ziskTrace.mainTable_component i.val
          (by omega) h_lt
          (mainTable_index_lt_capacity ziskTrace.mainTable_component i.val h_lt)
      have h_rec :=
        ZiskFv.AirsClean.FullEnsemble.mainOfTable_pc_eq_nextPcMux_of_transitions_hold
          ziskTrace.transitions_hold ziskTrace.mainTable_mem ziskTrace.mainTable_component
          ⟨i.val, h_index_lt⟩ h_not_boundary
      have h_eq : i = ⟨j + 1, h_succ_lt⟩ := Fin.ext (by simpa using h_i)
      subst h_eq
      rw [h_rec]
      simpa only [nextPcMux, Nat.add_sub_cancel] using seed.succ j h_succ_lt

/-- **The consumption point.** `Inputs_<op>.h_pc_bridge` is stated against the operand bundle's
    named PC (`h_input_pc : (binding i).regs.get? Register.PC = .some v`), so this is the form the
    dispatcher actually needs: given the seed and that naming, the field follows.

    This is what makes `SegmentPcSeed` load-bearing rather than decorative — it produces exactly the
    field that all 63 `Inputs_<op>` structures currently assume. -/
theorem h_pc_bridge_of_pcSeed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    (seed : SegmentPcSeed ziskTrace binding)
    (i : Fin ziskTrace.numInstructions) {v : BitVec 64}
    (h_input_pc : (binding i).regs.get? Register.PC = .some v) :
    ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc i.val).val = v.toNat := by
  simpa only [h_input_pc, Option.elim] using pcBridge_of_pcSeed seed i

end ZiskFv.Compliance
