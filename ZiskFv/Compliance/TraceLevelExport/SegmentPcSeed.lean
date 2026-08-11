import ZiskFv.AirsClean.FullEnsemble.Balance.RegisterChainBridges
import ZiskFv.Compliance.TraceLevelExport.Dispatcher

/-!
# The segment PC seed (`SegmentPcSeed`) — #330 Phase 5

`h_pc_bridge` is the one `InputsAgree` field present in **all 63** `Inputs_<op>` structures: it
asserts that the Main `pc` column at a row equals the Sail PC at that step. It used to be assumed
once per opcode structure, i.e. at every row.

`root_soundness` now assumes `InputsAgreeCore` (`Inputs_<op>` minus that field) plus **two**
premises from this module, in the shape `BootSegmentMemorySeed` established for memory (#185/#115):

* `boot` — the Sail PC agrees with the Main `pc` column at step `0`;
* `succ` — the Sail PC at step `j + 1` is the **next-PC mux** the Main row at `j` computes.

## What this is, and what it is not

Both directions are proved in this file, so be precise about the claim:

* `inputsAgree_of_pcSeed` — core + seed ⟹ the full per-row `InputsAgree`;
* `pcSeed_of_inputsAgree` — the full per-row `InputsAgree` ⟹ the seed.

Over an `AcceptedZiskTrace` the two bundles are therefore **inter-derivable**. This is a
*restructuring* of the premise, NOT a reduction in logical strength. Claiming otherwise would be
laundering, and the converse direction above is what proves it would be.

What genuinely changes:

* the caller supplies **2** facts about a segment instead of one PC equation per executed row;
* `succ` never mentions the `pc` column — it says the Sail PC advances to the value the ZisK row
  computes, so cross-machine PC agreement is asserted at one point (`boot`) plus a successor law,
  instead of independently at every row;
* the per-row bridging is done by the circuit's own transition constraint, via
  `mainOfTable_pc_eq_nextPcMux_of_transitions_hold`, derived from
  `AcceptedZiskTrace.transitions_hold` at no premise cost;
* the trust ledger gains one named premise where it had 63 scattered fields.

This is the same bargain `BootSegmentMemorySeed` (#185/#115) struck for memory, and it is the
prerequisite for the genuinely weaker statement rather than a substitute for it. `SailTrace` is a
bare `Fin n → SailState` (`ZiskFv/Compliance/SailTrace.lean:20`) with **no chaining**, so *something*
must say the Sail states form an execution. Making `SailTrace` a chained execution would let `succ`
be discharged by induction from `boot` alone — a real strength reduction, and now a local change at
the root rather than 63 structure edits. That follow-on is tracked on #330.

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

    Replaces the 63 per-opcode `h_pc_bridge` assumptions as the root premise. It is
    inter-derivable with them, not weaker — see the module docstring for exactly what changes. -/
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

/-! ## Phase 7 groundwork: what `succ` is actually asserting

`succ` is stated against `nextPcMux`. The three lemmas below make explicit that this value is
exactly what the circuit hands the Sail model through the execution bus, which is what turns
"chain `SailTrace`" from a vague plan into a mechanical one.
-/

/-- The circuit's PC recurrence in successor form: the Main `pc` column at row `j + 1` **is** the
    next-PC mux the row at `j` computed. Derived from `AcceptedZiskTrace.transitions_hold`; both
    side conditions (`segment_l1 ≠ 1` off row `0`, fixed-column capacity) are discharged here, so
    this costs no premise. -/
theorem mainOfTable_pc_succ_eq_nextPcMux
    {ziskTrace : AcceptedZiskTrace numInstructions} (j : ℕ)
    (h_row : j + 1 < ziskTrace.mainTable.table.length) :
    (mainOfTable ziskTrace.program ziskTrace.mainTable).pc (j + 1) = nextPcMux ziskTrace j := by
  have h_len : j + 1 < ziskTrace.mainTable.length := by
    simpa only [Air.Flat.Table.table_length] using h_row
  have h_rec :=
    ZiskFv.AirsClean.FullEnsemble.mainOfTable_pc_eq_nextPcMux_of_transitions_hold
      ziskTrace.transitions_hold ziskTrace.mainTable_mem ziskTrace.mainTable_component
      ⟨j + 1, h_len⟩
      (mainOfTable_segment_l1_ne_one_of_pos ziskTrace.mainTable_component (j + 1)
        (by omega) h_row
        (mainTable_index_lt_capacity ziskTrace.mainTable_component (j + 1) h_row))
  simpa only [nextPcMux, Nat.add_sub_cancel] using h_rec

/-- **The exec-bus producer entry carries the mux.** `bus_effect` writes
    `Register.nextPC := BitVec.ofNat 64 (execution_bus[1]!.pc).val`
    (`ZiskFv/SailSpec/BusEffect.lean`), and `Pilot.execRowOf`'s producer entry is definitionally
    the Main `pc` column at row `i + 1`. So the value ZisK pushes into Sail's `nextPC` for step `i`
    is exactly `nextPcMux ziskTrace i`.

    This is the fact that makes `SegmentPcSeed.succ` mechanically dischargeable rather than
    irreducible: `succ` says "the Sail PC at `j + 1` is the mux at `j`", and this says "the mux at
    `j` is what the circuit already wrote into Sail's `nextPC` at step `j`". What remains is the
    Sail-side retire law — see `SailRetireChain` below. -/
theorem execRowOf_producer_pc_eq_nextPcMux
    {ziskTrace : AcceptedZiskTrace numInstructions} (i : Fin ziskTrace.numInstructions)
    (h_row : i.val + 1 < ziskTrace.mainTable.table.length) :
    (Pilot.execRowOf ziskTrace i)[1]!.pc = nextPcMux ziskTrace i :=
  mainOfTable_pc_succ_eq_nextPcMux i.val h_row

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
      have h_row : j + 1 < ziskTrace.mainTable.table.length := by omega
      have h_rec := mainOfTable_pc_succ_eq_nextPcMux (ziskTrace := ziskTrace) j h_row
      have h_eq : i = ⟨j + 1, h_succ_lt⟩ := Fin.ext (by simpa using h_i)
      subst h_eq
      rw [h_rec]
      exact seed.succ j h_succ_lt

/-- **The consumption point, per row.** `Inputs_<op>.h_pc_bridge` is stated against the operand
    bundle's named PC (`h_input_pc : (binding i).regs.get? Register.PC = .some v`), so this is the
    form the dispatcher actually needs: given the row's PC agreement and that naming, the field
    follows.

    Stated against the row fact rather than a whole-segment seed, because #330 Phase 7 obtains that
    fact by induction (`pcBridge_succ_of_stepSound`) rather than from a seed. -/
theorem h_pc_bridge_of_pcBridge
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (h_bridge : ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc i.val).val
      = ((binding i).regs.get? Register.PC).elim 0 BitVec.toNat)
    {v : BitVec 64}
    (h_input_pc : (binding i).regs.get? Register.PC = .some v) :
    ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc i.val).val = v.toNat := by
  simpa only [h_input_pc, Option.elim] using h_bridge

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

/-- **The collapse.** Rebuild the full per-row `InputsAgree` from the caller-supplied
    `InputsAgreeCore` and the single segment-wide `SegmentPcSeed`.

    This is where the 63 assumed `h_pc_bridge` fields stop being premises. Each arm
    feeds `h_pc_bridge_of_pcSeed` the row's own Sail-PC naming, which every op already
    carries in one of three places:

    * 45 ops name it directly, as `h_input_pc`;
    * the 7 signed M-extension ops carry it inside `promises` (`input_pc_eq`);
    * the 11 memory ops carry it as the first conjunct of `<op>_state_assumptions`.

    None of those three is a new premise — all were already fields of the same structure.
    What the seed supplies is the other half: that the Main `pc` column equals that named
    PC, which used to be assumed and is now derived. -/
def inputsAgree_of_pcBridge {numInstructions : ℕ}
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    (i : Fin ziskTrace.numInstructions)
    (h_bridge : ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc i.val).val
      = ((binding i).regs.get? Register.PC).elim 0 BitVec.toNat) :
    (zs : ZiskStep ziskTrace i) → InputsAgreeCore ziskTrace binding i zs →
      InputsAgree ziskTrace binding i zs
  | .sub _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .and _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .or _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .xor _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .slt _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .sltu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .andi _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .ori _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .xori _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .slti _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .sltiu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .sll _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .srl _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .sra _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .slli _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .srli _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .srai _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .add _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .addi _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .subw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .addw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .addiw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .sllw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .srlw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .sraw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .slliw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .srliw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .sraiw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .mul _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.promises.input_pc_eq }
  | .mulh _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.promises.input_pc_eq }
  | .mulhsu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.promises.input_pc_eq }
  | .mulw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .mulhu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .div _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.promises.input_pc_eq }
  | .rem _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.promises.input_pc_eq }
  | .divw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.promises.input_pc_eq }
  | .remw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.promises.input_pc_eq }
  | .divu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .divuw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .remu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .remuw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .beq _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .bne _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .blt _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .bge _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .bltu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .bgeu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .lui _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .auipc _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .jal _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .jalr _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }
  | .sb _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .sh _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .sw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .sd _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .ld _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .lbu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .lhu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .lwu _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .lb _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .lh _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .lw _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_opcode_assumptions.1 }
  | .fence _, core =>
      { core with h_pc_bridge := h_pc_bridge_of_pcBridge h_bridge core.h_input_pc }

/-- The seed-driven form, kept for the callers that still hold a `SegmentPcSeed`. -/
def inputsAgree_of_pcSeed {numInstructions : ℕ}
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    (seed : SegmentPcSeed ziskTrace binding)
    (i : Fin ziskTrace.numInstructions) :
    (zs : ZiskStep ziskTrace i) → InputsAgreeCore ziskTrace binding i zs →
      InputsAgree ziskTrace binding i zs :=
  inputsAgree_of_pcBridge i (pcBridge_of_pcSeed seed i)

/-- **The row's Sail PC is named.** Every `InputsAgree` arm carries `(binding i).regs.get? PC =
    some v` somewhere — 45 ops as `h_input_pc`, the 7 signed M-ext ops inside `promises`, the 11
    memory ops as the first conjunct of `<op>_state_assumptions`. Projecting just the `some` is what
    the retire-chain bridge needs, because `Option.elim` throws it away. -/
theorem pcNamed_of_inputsAgree {numInstructions : ℕ}
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    (i : Fin ziskTrace.numInstructions) :
    (zs : ZiskStep ziskTrace i) → InputsAgree ziskTrace binding i zs →
      ∃ v : BitVec 64, (binding i).regs.get? Register.PC = .some v
  | .sub _, ia => ⟨_, ia.h_input_pc⟩
  | .and _, ia => ⟨_, ia.h_input_pc⟩
  | .or _, ia => ⟨_, ia.h_input_pc⟩
  | .xor _, ia => ⟨_, ia.h_input_pc⟩
  | .slt _, ia => ⟨_, ia.h_input_pc⟩
  | .sltu _, ia => ⟨_, ia.h_input_pc⟩
  | .andi _, ia => ⟨_, ia.h_input_pc⟩
  | .ori _, ia => ⟨_, ia.h_input_pc⟩
  | .xori _, ia => ⟨_, ia.h_input_pc⟩
  | .slti _, ia => ⟨_, ia.h_input_pc⟩
  | .sltiu _, ia => ⟨_, ia.h_input_pc⟩
  | .sll _, ia => ⟨_, ia.h_input_pc⟩
  | .srl _, ia => ⟨_, ia.h_input_pc⟩
  | .sra _, ia => ⟨_, ia.h_input_pc⟩
  | .slli _, ia => ⟨_, ia.h_input_pc⟩
  | .srli _, ia => ⟨_, ia.h_input_pc⟩
  | .srai _, ia => ⟨_, ia.h_input_pc⟩
  | .add _, ia => ⟨_, ia.h_input_pc⟩
  | .addi _, ia => ⟨_, ia.h_input_pc⟩
  | .subw _, ia => ⟨_, ia.h_input_pc⟩
  | .addw _, ia => ⟨_, ia.h_input_pc⟩
  | .addiw _, ia => ⟨_, ia.h_input_pc⟩
  | .sllw _, ia => ⟨_, ia.h_input_pc⟩
  | .srlw _, ia => ⟨_, ia.h_input_pc⟩
  | .sraw _, ia => ⟨_, ia.h_input_pc⟩
  | .slliw _, ia => ⟨_, ia.h_input_pc⟩
  | .srliw _, ia => ⟨_, ia.h_input_pc⟩
  | .sraiw _, ia => ⟨_, ia.h_input_pc⟩
  | .mul _, ia => ⟨_, ia.promises.input_pc_eq⟩
  | .mulh _, ia => ⟨_, ia.promises.input_pc_eq⟩
  | .mulhsu _, ia => ⟨_, ia.promises.input_pc_eq⟩
  | .mulw _, ia => ⟨_, ia.h_input_pc⟩
  | .mulhu _, ia => ⟨_, ia.h_input_pc⟩
  | .div _, ia => ⟨_, ia.promises.input_pc_eq⟩
  | .rem _, ia => ⟨_, ia.promises.input_pc_eq⟩
  | .divw _, ia => ⟨_, ia.promises.input_pc_eq⟩
  | .remw _, ia => ⟨_, ia.promises.input_pc_eq⟩
  | .divu _, ia => ⟨_, ia.h_input_pc⟩
  | .divuw _, ia => ⟨_, ia.h_input_pc⟩
  | .remu _, ia => ⟨_, ia.h_input_pc⟩
  | .remuw _, ia => ⟨_, ia.h_input_pc⟩
  | .beq _, ia => ⟨_, ia.h_input_pc⟩
  | .bne _, ia => ⟨_, ia.h_input_pc⟩
  | .blt _, ia => ⟨_, ia.h_input_pc⟩
  | .bge _, ia => ⟨_, ia.h_input_pc⟩
  | .bltu _, ia => ⟨_, ia.h_input_pc⟩
  | .bgeu _, ia => ⟨_, ia.h_input_pc⟩
  | .lui _, ia => ⟨_, ia.h_input_pc⟩
  | .auipc _, ia => ⟨_, ia.h_input_pc⟩
  | .jal _, ia => ⟨_, ia.h_input_pc⟩
  | .jalr _, ia => ⟨_, ia.h_input_pc⟩
  | .sb _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .sh _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .sw _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .sd _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .ld _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .lbu _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .lhu _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .lwu _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .lb _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .lh _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .lw _, ia => ⟨_, ia.h_opcode_assumptions.1⟩
  | .fence _, ia => ⟨_, ia.h_input_pc⟩

/-- The PC half of a full `InputsAgree`, in the seed's `Option.elim` form.

    Each arm reads the row's `h_pc_bridge` and the row's own Sail-PC naming — the same
    three places `inputsAgree_of_pcSeed` uses, in the opposite direction. -/
theorem pcAgreement_of_inputsAgree {numInstructions : ℕ}
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    (i : Fin ziskTrace.numInstructions) :
    (zs : ZiskStep ziskTrace i) → InputsAgree ziskTrace binding i zs →
      ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc i.val).val
        = ((binding i).regs.get? Register.PC).elim 0 BitVec.toNat
  | .sub _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .and _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .or _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .xor _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .slt _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .sltu _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .andi _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .ori _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .xori _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .slti _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .sltiu _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .sll _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .srl _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .sra _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .slli _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .srli _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .srai _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .add _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .addi _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .subw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .addw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .addiw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .sllw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .srlw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .sraw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .slliw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .srliw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .sraiw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .mul _, ia => by simpa only [ia.promises.input_pc_eq, Option.elim] using ia.h_pc_bridge
  | .mulh _, ia => by simpa only [ia.promises.input_pc_eq, Option.elim] using ia.h_pc_bridge
  | .mulhsu _, ia => by simpa only [ia.promises.input_pc_eq, Option.elim] using ia.h_pc_bridge
  | .mulw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .mulhu _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .div _, ia => by simpa only [ia.promises.input_pc_eq, Option.elim] using ia.h_pc_bridge
  | .rem _, ia => by simpa only [ia.promises.input_pc_eq, Option.elim] using ia.h_pc_bridge
  | .divw _, ia => by simpa only [ia.promises.input_pc_eq, Option.elim] using ia.h_pc_bridge
  | .remw _, ia => by simpa only [ia.promises.input_pc_eq, Option.elim] using ia.h_pc_bridge
  | .divu _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .divuw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .remu _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .remuw _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .beq _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .bne _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .blt _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .bge _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .bltu _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .bgeu _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .lui _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .auipc _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .jal _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .jalr _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge
  | .sb _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .sh _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .sw _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .sd _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .ld _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .lbu _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .lhu _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .lwu _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .lb _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .lh _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .lw _, ia => by simpa only [ia.h_opcode_assumptions.1, Option.elim] using ia.h_pc_bridge
  | .fence _, ia => by simpa only [ia.h_input_pc, Option.elim] using ia.h_pc_bridge

/-- **`SegmentPcSeed` is no stronger than what callers already assumed.** Anything that
    could supply the old 63-field `InputsAgree` family can supply the seed.

    `boot` is row `0`'s PC agreement.  `succ` is row `j + 1`'s PC agreement pushed back
    through the circuit's own PC recurrence — the same
    `mainOfTable_pc_eq_nextPcMux_of_transitions_hold` that `pcBridge_of_pcSeed` uses
    forwards, run in the other direction.

    Together with `inputsAgree_of_pcSeed` this makes the two bundles inter-derivable over
    an `AcceptedZiskTrace`.  Stated plainly: the seed is a **restructuring** of the old
    premise, not a weakening of it.  See the module docstring for what does change, and
    for the chained-`SailTrace` follow-on that would make it a real reduction. -/
def pcSeed_of_inputsAgree {numInstructions : ℕ}
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (ia : ∀ i : Fin ziskTrace.numInstructions,
      InputsAgree ziskTrace binding i (ziskStep i)) :
    SegmentPcSeed ziskTrace binding where
  boot h := pcAgreement_of_inputsAgree ⟨0, h⟩ _ (ia ⟨0, h⟩)
  succ j h := by
    have h_agree := pcAgreement_of_inputsAgree ⟨j + 1, h⟩ _ (ia ⟨j + 1, h⟩)
    rwa [mainOfTable_pc_succ_eq_nextPcMux j (ziskTrace.mainTable_index ⟨j + 1, h⟩)] at h_agree

/-- Forget the PC field: the `InputsAgreeCore` inside a full `InputsAgree`.

    Paired with `pcSeed_of_inputsAgree`, this is how an existing accepted-trace witness
    that already proved the 63-field family supplies the two new root premises. -/
def inputsAgreeCore_of_inputsAgree {numInstructions : ℕ}
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    (i : Fin ziskTrace.numInstructions) :
    (zs : ZiskStep ziskTrace i) → InputsAgree ziskTrace binding i zs →
      InputsAgreeCore ziskTrace binding i zs
  | .sub _, ia => ia.toInputsCore_sub
  | .and _, ia => ia.toInputsCore_and
  | .or _, ia => ia.toInputsCore_or
  | .xor _, ia => ia.toInputsCore_xor
  | .slt _, ia => ia.toInputsCore_slt
  | .sltu _, ia => ia.toInputsCore_sltu
  | .andi _, ia => ia.toInputsCore_andi
  | .ori _, ia => ia.toInputsCore_ori
  | .xori _, ia => ia.toInputsCore_xori
  | .slti _, ia => ia.toInputsCore_slti
  | .sltiu _, ia => ia.toInputsCore_sltiu
  | .sll _, ia => ia.toInputsCore_sll
  | .srl _, ia => ia.toInputsCore_srl
  | .sra _, ia => ia.toInputsCore_sra
  | .slli _, ia => ia.toInputsCore_slli
  | .srli _, ia => ia.toInputsCore_srli
  | .srai _, ia => ia.toInputsCore_srai
  | .add _, ia => ia.toInputsCore_add
  | .addi _, ia => ia.toInputsCore_addi
  | .subw _, ia => ia.toInputsCore_subw
  | .addw _, ia => ia.toInputsCore_addw
  | .addiw _, ia => ia.toInputsCore_addiw
  | .sllw _, ia => ia.toInputsCore_sllw
  | .srlw _, ia => ia.toInputsCore_srlw
  | .sraw _, ia => ia.toInputsCore_sraw
  | .slliw _, ia => ia.toInputsCore_slliw
  | .srliw _, ia => ia.toInputsCore_srliw
  | .sraiw _, ia => ia.toInputsCore_sraiw
  | .mul _, ia => ia.toInputsCore_mul
  | .mulh _, ia => ia.toInputsCore_mulh
  | .mulhsu _, ia => ia.toInputsCore_mulhsu
  | .mulw _, ia => ia.toInputsCore_mulw
  | .mulhu _, ia => ia.toInputsCore_mulhu
  | .div _, ia => ia.toInputsCore_div
  | .rem _, ia => ia.toInputsCore_rem
  | .divw _, ia => ia.toInputsCore_divw
  | .remw _, ia => ia.toInputsCore_remw
  | .divu _, ia => ia.toInputsCore_divu
  | .divuw _, ia => ia.toInputsCore_divuw
  | .remu _, ia => ia.toInputsCore_remu
  | .remuw _, ia => ia.toInputsCore_remuw
  | .beq _, ia => ia.toInputsCore_beq
  | .bne _, ia => ia.toInputsCore_bne
  | .blt _, ia => ia.toInputsCore_blt
  | .bge _, ia => ia.toInputsCore_bge
  | .bltu _, ia => ia.toInputsCore_bltu
  | .bgeu _, ia => ia.toInputsCore_bgeu
  | .lui _, ia => ia.toInputsCore_lui
  | .auipc _, ia => ia.toInputsCore_auipc
  | .jal _, ia => ia.toInputsCore_jal
  | .jalr _, ia => ia.toInputsCore_jalr
  | .sb _, ia => ia.toInputsCore_sb
  | .sh _, ia => ia.toInputsCore_sh
  | .sw _, ia => ia.toInputsCore_sw
  | .sd _, ia => ia.toInputsCore_sd
  | .ld _, ia => ia.toInputsCore_ld
  | .lbu _, ia => ia.toInputsCore_lbu
  | .lhu _, ia => ia.toInputsCore_lhu
  | .lwu _, ia => ia.toInputsCore_lwu
  | .lb _, ia => ia.toInputsCore_lb
  | .lh _, ia => ia.toInputsCore_lh
  | .lw _, ia => ia.toInputsCore_lw
  | .fence _, ia => ia.toInputsCore_fence


end ZiskFv.Compliance
