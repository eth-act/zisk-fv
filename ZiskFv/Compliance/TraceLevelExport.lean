import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.ConstructionAnd
import ZiskFv.Compliance.ConstructionLogic
import ZiskFv.Compliance.ConstructionCompare
import ZiskFv.Compliance.ConstructionIType
import ZiskFv.Compliance.ConstructionShift
import ZiskFv.Compliance.ConstructionAdd
import ZiskFv.Compliance.ConstructionWAlu
import ZiskFv.Compliance.ConstructionLui
import ZiskFv.Compliance.ConstructionAuipc
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.Compliance.ConstructionDivu
import ZiskFv.Compliance.ConstructionDivuw
import ZiskFv.Compliance.ConstructionRemu
import ZiskFv.Compliance.ConstructionRemuw
import ZiskFv.Compliance.ConstructionStore
import ZiskFv.Compliance.ConstructionLoad
import ZiskFv.Compliance.ConstructionBranch
import ZiskFv.Compliance.ConstructionJump
import ZiskFv.Compliance
import ZiskFv.Compliance.Defects

/-!
# TraceLevelExport.lean — P5 trace-level export over the 55 sound constructions

This is the achievable closure of #61.  It exports the per-opcode
`construction_<op>_sound` theorems to a single trace-level statement: given an
accepted full-ensemble trace, a program binding, and a per-row CLASSIFICATION
(`rowData : ∀ i, RowConstructionData …`), EVERY row of the trace satisfies the
canonical per-step `bus_effect`-form compliance conclusion — with NO
caller-supplied `OpEnvelope`.  The envelope for each row is dispatched INSIDE,
per row, from `rowData i` to the matching `construction_<op>_sound`.

## What `RowConstructionData` is (and is NOT)

`RowConstructionData trace binding i` is a 55-arm sum type — one arm per sound
construction archetype.  Each arm carries a single `RowData_<op>` payload that
packages EXACTLY that construction's genuinely-irreducible residual binders
(decode pins, Sail reads, operand/lane bridges, the `execRow` ∀-binder + exec
facts, `h_nextPC_matches`; for loads also `MemoryTimelineEvidence` + the Mem-AIR
provider linkage).  It does NOT package the bucket-(a) op-bus provider-match
evidence: that is derived INSIDE each construction from `trace.balanced` (via the
`exists_*_from_binding` Layer-A wrappers).  The `RowData_<op>` fields are verbatim
copies of each `construction_<op>_sound`'s binders after `(i : Fin trace.length)`,
so the dispatch is a positional `exact construction_<op>_sound trace binding i …`.

## Coverage (stated explicitly — NOT hidden)

This theorem covers ONLY traces whose every row is one of the **55 classifiable,
non-defect RV64IM opcodes**.  The `∀ i, RowConstructionData trace binding i`
premise is exactly this coverage obligation made visible in the type: a witness
per row that the row IS one of the 55 archetypes.  The **8 defect/decode-gap
opcodes** — the 7 signed-M ops (`MUL`, `MULH`, `MULHSU`, `DIV`, `DIVW`, `REM`,
`REMW`) and `FENCE` — have **NO arm** in `RowConstructionData` and are therefore
**out of scope** for this theorem.  Those 8 are covered ONLY by the global
theorem's ∀-env `NoKnownDefect` / decode-gap exclusion
(`zisk_riscv_compliant_program_bus`), which is intentionally contradictory for
the unsound signed-M envelopes and records the FENCE decode gap.  This theorem
makes no claim about them.

## Non-vacuity

The hypotheses are SATISFIABLE for a real trace.  `trace : AcceptedTrace` is the
committed full-ensemble witness; each `rowData i` carries TRUE facts of the real
row `mainOfTable trace.program binding.mainTable` at index `i` (decode pins, lane
bridges, Sail reads of `binding.stateAt i`), and `execRow` is a genuine
top-level ∀-binder inside each arm (the real execution-bus row).  No arm contains
a contradictory hypothesis pair — each arm is exactly the binder list of a
construction theorem that is itself proved (not vacuously) against the committed
trace.  The conclusion's buses (`busSub`/`busSt`/`busLd …`) are the real Main
memory-bus emissions, never free junk chosen to trivialize the goal.

## Residual roll-up

The irreducible residuals carried per arm bottom out in the existing project
residuals — none introduces a new `ZiskFv.*` axiom:
* loads/stores `h_memory_timeline` / RMW-preservation reads → **#76** (memory
  timeline), plus the Mem-AIR `h_mem_*` provider linkage;
* branches + JAL/JALR `h_nextPC_matches` (conditional next-PC) → **#100**
  (cross-row control flow);
* the signed loads (`lb`/`lh`/`lw`) carry `h_static` + `h_match` — the
  sign-extension `BinaryExtension` op-bus lookup linkage that
  `construction_{lb,lh,lw}_sound` themselves take as residual binders (these
  constructions, unlike the ALU ops, do NOT derive their op-bus match internally
  from `trace.balanced`; the `aeneasBridgeTrust` / `SextLoadBridge` coupling is
  the residual).  This is verbatim residual, not bucket-(a) provider-match
  smuggling — the ALU/W/shift arms carry NO op-bus match field (it is derived
  inside their constructions via the `exists_*_from_binding` wrappers).

This file introduces **0 new `ZiskFv.*` axioms**: its trust closure is the union
of the 55 constructions' closures.

## Strengthened export (channel-balance form)

For **43 of the 55 arms** this file ALSO proves a STRICTLY STRONGER per-row export
(`stepStrong_<op>` → `StepComplianceStrong` → `zisk_compliant_of_accepted_trace_strong`):
the EXACT conclusion of the OLD global theorem
`zisk_riscv_compliant_program_bus` (the channel-balance
`= state_effect_via_channels …` form).  Two sound routes are used, both yielding
the identical channel-balance proposition the global theorem produces:

1. **Env-constructed route (22 op-bus ALU arms)** — `SUB AND OR XOR SLT SLTU`,
   `ANDI ORI XORI SLTI SLTIU`, `SLL SRL SRA SLLI SRLI SRAI`, `ADD ADDI`,
   `SUBW ADDW ADDIW`.  The matching `OpEnvelope.<op>` arm is **constructed from
   the accepted trace** per row (re-running each construction's `*_from_binding`
   provider-match + input-packing derivations) and fed to
   `zisk_riscv_compliant_program_bus`.  The three global-theorem hypotheses are
   discharged in place: `aeneasBridgeTrust` from the derived row-binding facts,
   `memoryTimelineConstructionEvidence` trivially (non-load arms), and
   `NoKnownDefect` trivially (non-defect ops — a TRUE fact, not a contradictory
   hypothesis).

2. **Direct-lift route (21 control-flow + U-type + store + load arms)** — `BEQ BNE
   BLT BGE BLTU BGEU`, `LUI AUIPC`, `JAL JALR`, `SB SH SW SD`,
   `LB LH LW LD LBU LHU LWU`.  Each `construction_<op>_sound` already proves the
   `bus_effect`-form per-step conclusion over the real trace row, and
   `state_effect_via_channels` is `@[reducible]`-defeq to `bus_effect.2`.  So
   `rw [state_effect_via_channels_eq_bus_effect_2]` + the construction theorem
   yields the same channel-balance proposition the global theorem produces.  For
   branches this IS the `Equivalence.<B>.equiv_<B>` the global dispatcher
   `zisk_riscv_compliant_program_bus_branch` itself dispatches to; for
   LUI/AUIPC/JAL/JALR/stores/loads it is the channel-balance lift over the same
   concrete `eRdLui`/`busSt`/`busLd` entries the `bus_effect`-form arm uses.  (This
   route sidesteps the `OpEnvelope`-route obstacles that previously blocked the
   stores [whnf BLOWUP on the `Eq.mpr` cast over the `MainRowWithRom` motive] and
   the loads [the `OpEnvelope` load arm's `Var`/`Environment` eval-provenance the
   witness-based constructions bypass]: `zisk_riscv_compliant_program_bus` is never
   invoked, so neither the cast nor the eval-provenance is ever needed.)

Both routes DOMINATE the `bus_effect`-form `StepCompliance`: defeq-stronger
(channel-balance form), over the committed trace's real row data.

The remaining 12 sound arms are **not** strengthened to the channel-balance form
here (they stay in the `bus_effect`-form export above), for this structural
reason — the honest "constructor needs data not produced by the construction"
obstacle, NOT a soundness gap.  (The 6 are the M-ext-unsigned arms; the other 6
are M-ext-signed/FENCE defect/gap arms with no sound construction at all.)
* **M-ext-unsigned (MULW/MULHU/DIVU/DIVUW/REMU/REMUW)** — the direct-lift route is
  available in principle (the constructions conclude in `bus_effect` form), but
  the `bus_effect`-form `StepCompliance` is deliberately the CORRECT export for
  these: the canonical channel-balance equiv requires the TIGHT Arith carry bound
  (`<131072`), which is the known-suspect bound NOT row-locally constructible for
  real carries.  The faithful `bus_effect` form (`<983041`) is the right one;
  these are intentionally LEFT in `bus_effect` form and must NOT be forced.

The strengthened export is genuinely non-vacuous: each envelope is the real
`OpEnvelope.<op>` over the committed trace's `mainOfTable` row; `execRow` is a
genuine ∀-binder; no `False.elim` or contradictory-hypothesis pair appears.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.EquivCore.Promises
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)
open Interaction

-- The M-extension row-computing defs are reducible/semireducible; structure-field
-- elaboration would otherwise whnf-reduce the full per-row ArithMul/ArithDiv
-- computation (a runaway). `seal` blocks that locally without touching the
-- committed construction proofs (which keep the defs as-is in their oleans).
seal mulwArow mulhuArow divuArow divuwArow remuArow remuwArow

set_option maxHeartbeats 8000000

/-- All-zero `Valid_Binary` — pure data, never consumed by any dispatcher arm
    (the RTYPE/ITYPE/W binary `OpEnvelope` arms carry it as an unused field).
    Building it with `0` lanes is non-vacuous: it imposes no constraint and
    makes no hypothesis contradictory. -/
noncomputable def zeroValidBinary : ZiskFv.Airs.Binary.Valid_Binary FGL FGL := by
  constructor <;> exact fun _ => 0

/-- `EnvNoKnownDefectFor sel` is the defect-exclusion fact for *every* `OpEnvelope`
    in the family carved out by the selector `sel`: every such env is outside all
    known-defect regions.  An OpEnvelope-route `stepStrong_<op>` proof instantiates
    this with the specific env it constructs (`sel` selecting exactly that arm's
    `OpEnvelope` constructor), feeding the result to
    `zisk_riscv_compliant_program_bus` instead of re-proving `NoKnownDefect`.

    For the 22 current OpEnvelope-route arms the selected constructor is never a
    defect constructor, so this is TRIVIALLY satisfiable (proved by `cases`/`simp`
    on the defect predicates) — the threaded hypothesis is non-vacuous.  For the
    yet-to-be-added signed-M / FENCE defect arms the analogous selector picks a
    constructor for which `NoKnownDefect` is NOT unconditionally true, so the
    obligation genuinely requires caller-supplied defect-exclusion data — which is
    exactly the plumbing this binder provides. -/
def EnvNoKnownDefectFor
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r : ℕ}
    (sel : OpEnvelope state m r → Prop) : Prop :=
  ∀ env : OpEnvelope state m r, sel env → Defects.NoKnownDefect env

/-- The defect-constructor selector for an OpEnvelope-route arm is non-defect: every
    `OpEnvelope` it selects is `NoKnownDefect`.  This is the trivial discharge used
    to satisfy the threaded `StepNoKnownDefect` obligation for the 22 current
    non-defect arms (non-vacuous: the selected env exists and the fact is TRUE). -/
theorem envNoKnownDefectFor_of_nondefect
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r : ℕ}
    (sel : OpEnvelope state m r → Prop)
    (h : ∀ env, sel env →
      ¬ Defects.MaliciousSignedMulWitnessShape env ∧
      ¬ Defects.ArithDivDynamicWitnessShape env ∧
      Defects.FenceKnownGoodShape env) :
    EnvNoKnownDefectFor sel := by
  intro env hsel id
  obtain ⟨h1, h2, h3⟩ := h env hsel
  cases id with
  | arithMulSignedWitnessSoundness => exact h1
  | arithDivDynamicWitnessSoundness => exact h2
  | fenceIncomplete => simpa [Defects.Blocks] using h3

/-- Irreducible per-row residuals for the `sub` archetype — the binders of
    `construction_sub_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sub
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sub_input : PureSpec.SubInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SUB
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok sub_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sub_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sub_input.PC
  h_input_rd : sub_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
  h_rd_idx :
    sub_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `and` archetype — the binders of
    `construction_and_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_and
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  and_input : PureSpec.AndInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_AND
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok and_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok and_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some and_input.PC
  h_input_rd : and_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_and_pure and_input).nextPC
  h_rd_idx :
    and_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `or` archetype — the binders of
    `construction_or_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_or
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  or_input : PureSpec.OrInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_OR
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok or_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok or_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some or_input.PC
  h_input_rd : or_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_or_pure or_input).nextPC
  h_rd_idx :
    or_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `xor` archetype — the binders of
    `construction_xor_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_xor
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  xor_input : PureSpec.XorInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_XOR
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok xor_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok xor_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some xor_input.PC
  h_input_rd : xor_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC
  h_rd_idx :
    xor_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `slt` archetype — the binders of
    `construction_slt_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_slt
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  slt_input : PureSpec.SltInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok slt_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok slt_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some slt_input.PC
  h_input_rd : slt_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC
  h_rd_idx :
    slt_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sltu` archetype — the binders of
    `construction_sltu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sltu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sltu_input : PureSpec.SltuInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok sltu_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sltu_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sltu_input.PC
  h_input_rd : sltu_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC
  h_rd_idx :
    sltu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `andi` archetype — the binders of
    `construction_andi_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_andi
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  andi_input : PureSpec.AndiInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_AND
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok andi_input.r1_val (binding.stateAt i)
  h_input_imm : andi_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some andi_input.PC
  h_input_rd : andi_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_andi_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
    i.val andi_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
  h_rd_idx :
    andi_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `ori` archetype — the binders of
    `construction_ori_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_ori
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  ori_input : PureSpec.OriInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_OR
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok ori_input.r1_val (binding.stateAt i)
  h_input_imm : ori_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some ori_input.PC
  h_input_rd : ori_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_ori_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
    i.val ori_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
  h_rd_idx :
    ori_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `xori` archetype — the binders of
    `construction_xori_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_xori
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  xori_input : PureSpec.XoriInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_XOR
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok xori_input.r1_val (binding.stateAt i)
  h_input_imm : xori_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some xori_input.PC
  h_input_rd : xori_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_xori_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
    i.val xori_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
  h_rd_idx :
    xori_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `slti` archetype — the binders of
    `construction_slti_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_slti
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  slti_input : PureSpec.SltiInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok slti_input.r1_val (binding.stateAt i)
  h_input_imm : slti_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some slti_input.PC
  h_input_rd : slti_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_slti_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
    i.val slti_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
  h_rd_idx :
    slti_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sltiu` archetype — the binders of
    `construction_sltiu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sltiu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sltiu_input : PureSpec.SltiuInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok sltiu_input.r1_val (binding.stateAt i)
  h_input_imm : sltiu_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sltiu_input.PC
  h_input_rd : sltiu_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_sltiu_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
    i.val sltiu_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
  h_rd_idx :
    sltiu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sll` archetype — the binders of
    `construction_sll_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sll
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sll_input : PureSpec.SllInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok sll_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sll_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sll_input.PC
  h_input_rd : sll_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
  h_rd_idx :
    sll_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `srl` archetype — the binders of
    `construction_srl_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_srl
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  srl_input : PureSpec.SrlInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok srl_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok srl_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srl_input.PC
  h_input_rd : srl_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
  h_rd_idx :
    srl_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sra` archetype — the binders of
    `construction_sra_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sra
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sra_input : PureSpec.SraInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok sra_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sra_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sra_input.PC
  h_input_rd : sra_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
  h_rd_idx :
    sra_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `slli` archetype — the binders of
    `construction_slli_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_slli
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  slli_input : PureSpec.SlliInput
  r1 : regidx
  rd : regidx
  shamt : BitVec 6
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok slli_input.r1_val (binding.stateAt i)
  h_input_shamt : slli_input.shamt = shamt
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some slli_input.PC
  h_input_rd : slli_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      shamt_b_lo shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
  h_rd_idx :
    slli_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `srli` archetype — the binders of
    `construction_srli_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_srli
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  srli_input : PureSpec.SrliInput
  r1 : regidx
  rd : regidx
  shamt : BitVec 6
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok srli_input.r1_val (binding.stateAt i)
  h_input_shamt : srli_input.shamt = shamt
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srli_input.PC
  h_input_rd : srli_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      shamt_b_lo shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
  h_rd_idx :
    srli_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `srai` archetype — the binders of
    `construction_srai_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_srai
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  srai_input : PureSpec.SraiInput
  r1 : regidx
  rd : regidx
  shamt : BitVec 6
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok srai_input.r1_val (binding.stateAt i)
  h_input_shamt : srai_input.shamt = shamt
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srai_input.PC
  h_input_rd : srai_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      shamt_b_lo shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
  h_rd_idx :
    srai_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sllw` archetype — the binders of
    `construction_sllw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sllw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sllw_input : PureSpec.SllwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok sllw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sllw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sllw_input.PC
  h_input_rd : sllw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC
  h_rd_idx :
    sllw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `srlw` archetype — the binders of
    `construction_srlw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_srlw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  srlw_input : PureSpec.SrlwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok srlw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok srlw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srlw_input.PC
  h_input_rd : srlw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC
  h_rd_idx :
    srlw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sraw` archetype — the binders of
    `construction_sraw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sraw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sraw_input : PureSpec.SrawInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok sraw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok sraw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sraw_input.PC
  h_input_rd : sraw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC
  h_rd_idx :
    sraw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `slliw` archetype — the binders of
    `construction_slliw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_slliw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  slliw_input : PureSpec.SlliwInput
  r1 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok slliw_input.r1_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some slliw_input.PC
  h_input_rd : slliw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      shamt_w_b_lo slliw_input.shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
  h_rd_idx :
    slliw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `srliw` archetype — the binders of
    `construction_srliw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_srliw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  srliw_input : PureSpec.SrliwInput
  r1 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok srliw_input.r1_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srliw_input.PC
  h_input_rd : srliw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      shamt_w_b_lo srliw_input.shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
  h_rd_idx :
    srliw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `sraiw` archetype — the binders of
    `construction_sraiw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sraiw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sraiw_input : PureSpec.SraiwInput
  r1 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok sraiw_input.r1_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sraiw_input.PC
  h_input_rd : sraiw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      shamt_w_b_lo sraiw_input.shamt
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC
  h_rd_idx :
    sraiw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `add` archetype — the binders of
    `construction_add_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_add
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  add_input : PureSpec.AddInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok add_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok add_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some add_input.PC
  h_input_rd : add_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_add_pure add_input).nextPC
  h_rd_idx :
    add_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `addi` archetype — the binders of
    `construction_addi_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_addi
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  addi_input : PureSpec.AddiInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok addi_input.r1_val (binding.stateAt i)
  h_input_imm : addi_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some addi_input.PC
  h_input_rd : addi_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_addi_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
    i.val addi_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
  h_rd_idx :
    addi_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `subw` archetype — the binders of
    `construction_subw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_subw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  subw_input : PureSpec.SubwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SUB_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok subw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok subw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some subw_input.PC
  h_input_rd : subw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
  h_rd_idx :
    subw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `addw` archetype — the binders of
    `construction_addw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_addw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  addw_input : PureSpec.AddwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok addw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok addw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some addw_input.PC
  h_input_rd : addw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r2))
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
  h_rd_idx :
    addw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `addiw` archetype — the binders of
    `construction_addiw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_addiw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  addiw_input : PureSpec.AddiwInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok addiw_input.r1_val (binding.stateAt i)
  h_input_imm : addiw_input.imm = imm
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some addiw_input.PC
  h_input_rd : addiw_input.rd = regidx_to_fin rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
          (regidx_to_fin r1))
  h_addiw_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
    i.val addiw_input.imm
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
  h_rd_idx :
    addiw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr

/-- Irreducible per-row residuals for the `lui` archetype — the binders of
    `construction_lui_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lui
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  lui_input : PureSpec.LuiInput
  imm : BitVec 20
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_input_imm : lui_input.imm = imm
  h_input_rd : lui_input.rd = regidx_to_fin rd
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some lui_input.PC
  h_imm_lo_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val).val
      = (imm ++ (0 : BitVec 12)).toNat
  h_imm_hi_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_LUI_pure lui_input).nextPC
  h_rd_idx :
    lui_input.rd =
      Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr

/-- Irreducible per-row residuals for the `auipc` archetype — the binders of
    `construction_auipc_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_auipc
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  auipc_input : PureSpec.AuipcInput
  imm : BitVec 20
  rd : regidx
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_FLAG
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 1
  h_input_imm : auipc_input.imm = imm
  h_input_rd : auipc_input.rd = regidx_to_fin rd
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some auipc_input.PC
  h_offset_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset2
        i.val).val
      = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).pc i.val).val
      = auipc_input.PC.toNat
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_AUIPC_pure auipc_input).nextPC
  h_rd_idx :
    auipc_input.rd =
      Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr
  h_no_wrap : auipc_input.PC.toNat
    + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
      < GL_prime
  h_pc_offset_lt_2_32 :
    (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
      < 4294967296

/-- Irreducible per-row residuals for the `mulw` archetype — the binders of
    `construction_mulw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_mulw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  mulw_input : PureSpec.MulwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W
  h_main_active :
    (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program binding.mainTable).store_pc i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok mulw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok mulw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some mulw_input.PC
  h_input_rd : mulw_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_MULW_pure mulw_input).nextPC
  h_rd_idx :
    mulw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  h_a23 :
    ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).a_2 0).val = 0
      ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).a_3 0).val = 0
  h_b23 :
    ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).b_2 0).val = 0
      ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).b_3 0).val = 0
  h_sext_choice :
    ((((byteAt (busSub trace binding i execRow).e2 4).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 0)
        ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).c_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).c_1 0).val * 65536
              < 2147483648)
      ∨ (((byteAt (busSub trace binding i execRow).e2 4).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 255)
        ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).c_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).c_1 0).val * 65536
              ≥ 2147483648))
  h_rs1_value :
    (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
      = (((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).a_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).a_1 0).val * 65536 : ℤ)
          - ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).na 0).val * (2:ℤ)^32
  h_rs2_value :
    (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
      = (((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).b_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).b_1 0).val * 65536 : ℤ)
          - ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).nb 0).val * (2:ℤ)^32

/-- Irreducible per-row residuals for the `mulhu` archetype — the binders of
    `construction_mulhu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_mulhu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  mulhu_input : PureSpec.MulhuInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH
  h_main_active :
    (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program binding.mainTable).store_pc i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok mulhu_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok mulhu_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some mulhu_input.PC
  h_input_rd : mulhu_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
  h_rd_idx :
    mulhu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2
  h_rs1_value : mulhu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_0 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_1 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_2 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).a_3 0).val
  h_rs2_value : mulhu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_0 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_1 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_2 0).val
        ((vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)).b_3 0).val

/-- Irreducible per-row residuals for the `divu` archetype — the binders of
    `construction_divu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_divu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  divu_input : PureSpec.DivuInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU
  h_main_active :
    (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program binding.mainTable).store_pc i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok divu_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok divu_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some divu_input.PC
  h_input_rd : divu_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
  h_rd_idx :
    divu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2
  remainder_bound :
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (divuArow trace binding i h_main_active h_main_op)) 0
  h_rs1_value : divu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((divuArow trace binding i h_main_active h_main_op).chunks.c_0).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.c_1).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.c_2).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.c_3).val
  h_rs2_value : divu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((divuArow trace binding i h_main_active h_main_op).chunks.b_0).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.b_1).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.b_2).val
        ((divuArow trace binding i h_main_active h_main_op).chunks.b_3).val

/-- Irreducible per-row residuals for the `divuw` archetype — the binders of
    `construction_divuw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_divuw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  divuw_input : PureSpec.DivuwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W
  h_main_active :
    (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program binding.mainTable).store_pc i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok divuw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok divuw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some divuw_input.PC
  h_input_rd : divuw_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
  h_rd_idx :
    divuw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2
  remainder_bound :
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (divuwArow trace binding i h_main_active h_main_op)) 0
  h_b23 :
    ((divuwArow trace binding i h_main_active h_main_op).chunks.b_2).val = 0
      ∧ ((divuwArow trace binding i h_main_active h_main_op).chunks.b_3).val = 0
  h_c23 :
    ((divuwArow trace binding i h_main_active h_main_op).chunks.c_2).val = 0
      ∧ ((divuwArow trace binding i h_main_active h_main_op).chunks.c_3).val = 0
  h_sext_choice :
    ((((byteAt (busSub trace binding i execRow).e2 4).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 0)
        ∧ ((divuwArow trace binding i h_main_active h_main_op).chunks.a_0).val
            + ((divuwArow trace binding i h_main_active h_main_op).chunks.a_1).val * 65536
              < 2147483648)
      ∨ (((byteAt (busSub trace binding i execRow).e2 4).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 255)
        ∧ ((divuwArow trace binding i h_main_active h_main_op).chunks.a_0).val
            + ((divuwArow trace binding i h_main_active h_main_op).chunks.a_1).val * 65536
              ≥ 2147483648))
  h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
    = ((divuwArow trace binding i h_main_active h_main_op).chunks.c_0).val
        + ((divuwArow trace binding i h_main_active h_main_op).chunks.c_1).val * 65536
  h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
    = ((divuwArow trace binding i h_main_active h_main_op).chunks.b_0).val
        + ((divuwArow trace binding i h_main_active h_main_op).chunks.b_1).val * 65536

/-- Irreducible per-row residuals for the `remu` archetype — the binders of
    `construction_remu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_remu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  remu_input : PureSpec.RemuInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU
  h_main_active :
    (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program binding.mainTable).store_pc i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok remu_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok remu_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some remu_input.PC
  h_input_rd : remu_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
  h_rd_idx :
    remu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2
  remainder_bound :
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (remuArow trace binding i h_main_active h_main_op)) 0
  h_rs1_value : remu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((remuArow trace binding i h_main_active h_main_op).chunks.c_0).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.c_1).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.c_2).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.c_3).val
  h_rs2_value : remu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((remuArow trace binding i h_main_active h_main_op).chunks.b_0).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.b_1).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.b_2).val
        ((remuArow trace binding i h_main_active h_main_op).chunks.b_3).val

/-- Irreducible per-row residuals for the `remuw` archetype — the binders of
    `construction_remuw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_remuw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  remuw_input : PureSpec.RemuwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  h_main_op :
    (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W
  h_main_active :
    (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program binding.mainTable).store_pc i.val = 0
  h_input_r1 :
    read_xreg (regidx_to_fin r1) (binding.stateAt i)
      = EStateM.Result.ok remuw_input.r1_val (binding.stateAt i)
  h_input_r2 :
    read_xreg (regidx_to_fin r2) (binding.stateAt i)
      = EStateM.Result.ok remuw_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some remuw_input.PC
  h_input_rd : remuw_input.rd = regidx_to_fin rd
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : (busSub trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
  h_rd_idx :
    remuw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2
  remainder_bound :
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (remuwArow trace binding i h_main_active h_main_op)) 0
  h_b23 :
    ((remuwArow trace binding i h_main_active h_main_op).chunks.b_2).val = 0
      ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.b_3).val = 0
  h_c23 :
    ((remuwArow trace binding i h_main_active h_main_op).chunks.c_2).val = 0
      ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.c_3).val = 0
  h_sext_choice :
    ((((byteAt (busSub trace binding i execRow).e2 4).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 0
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 0)
        ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.d_0).val
            + ((remuwArow trace binding i h_main_active h_main_op).chunks.d_1).val * 65536
              < 2147483648)
      ∨ (((byteAt (busSub trace binding i execRow).e2 4).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 255
          ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 255)
        ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.d_0).val
            + ((remuwArow trace binding i h_main_active h_main_op).chunks.d_1).val * 65536
              ≥ 2147483648))
  h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
    = ((remuwArow trace binding i h_main_active h_main_op).chunks.c_0).val
        + ((remuwArow trace binding i h_main_active h_main_op).chunks.c_1).val * 65536
  h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
    = ((remuwArow trace binding i h_main_active h_main_op).chunks.b_0).val
        + ((remuwArow trace binding i h_main_active h_main_op).chunks.b_1).val * 65536

/-- Irreducible per-row residuals for the `sb` archetype — the binders of
    `construction_sb_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sb
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sb_input : PureSpec.SbInput
  regs : ZiskFv.Compliance.ModeRegsFull
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_main_ind_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
      i.val = 1
  h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input (binding.stateAt i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo sb_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi sb_input.r2_val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busSt trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STOREB_pure sb_input).nextPC
  h_m1 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 1]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 1 : BitVec 8)
  h_m2 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 2]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 2 : BitVec 8)
  h_m3 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 3]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 3 : BitVec 8)
  h_m4 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 4 : BitVec 8)
  h_m5 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 5 : BitVec 8)
  h_m6 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 6 : BitVec 8)
  h_m7 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 7 : BitVec 8)

/-- Irreducible per-row residuals for the `sh` archetype — the binders of
    `construction_sh_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sh
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sh_input : PureSpec.ShInput
  regs : ZiskFv.Compliance.ModeRegsFull
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_main_ind_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
      i.val = 2
  h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input (binding.stateAt i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo sh_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi sh_input.r2_val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busSt trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STOREH_pure sh_input).nextPC
  h_m2 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 2]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 2 : BitVec 8)
  h_m3 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 3]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 3 : BitVec 8)
  h_m4 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 4 : BitVec 8)
  h_m5 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 5 : BitVec 8)
  h_m6 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 6 : BitVec 8)
  h_m7 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 7 : BitVec 8)

/-- Irreducible per-row residuals for the `sw` archetype — the binders of
    `construction_sw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sw_input : PureSpec.SwInput
  regs : ZiskFv.Compliance.ModeRegsFull
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_main_ind_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
      i.val = 4
  h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input (binding.stateAt i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo sw_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi sw_input.r2_val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busSt trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STOREW_pure sw_input).nextPC
  h_m4 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 4 : BitVec 8)
  h_m5 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 5 : BitVec 8)
  h_m6 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 6 : BitVec 8)
  h_m7 : (binding.stateAt i).mem[(busSt trace binding i execRow).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i execRow).e2 7 : BitVec 8)

/-- Irreducible per-row residuals for the `sd` archetype — the binders of
    `construction_sd_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_sd
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  sd_input : PureSpec.SdInput
  regs : ZiskFv.Compliance.ModeRegsFull
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input (binding.stateAt i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo sd_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi sd_input.r2_val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busSt trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STORED_pure sd_input).nextPC

/-- Irreducible per-row residuals for the `ld` archetype — the binders of
    `construction_ld_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_ld
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  ld_input : PureSpec.LdInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_opcode_assumptions : PureSpec.ld_state_assumptions ld_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      ld_input.r1_val.toNat + (BitVec.signExtend 64 ld_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      ld_input.rd = 0
  h_addr2_idx :
    ld_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADD_pure ld_input).nextPC
  h_memory_timeline :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_mem_match :
    ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lbu` archetype — the binders of
    `construction_lbu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lbu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  lbu_input : PureSpec.LbuInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  execRow : List (Interaction.ExecutionBusEntry FGL)
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
    i.val (busLd trace binding i execRow).e1
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
      i.val = (1 : FGL)
  h_opcode_assumptions : PureSpec.lbu_state_assumptions lbu_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lbu_input.r1_val.toNat + (BitVec.signExtend 64 lbu_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lbu_input.rd = 0
  h_addr2_idx :
    lbu_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADBU_pure lbu_input).nextPC
  h_memory_timeline :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_mem_match :
    ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lhu` archetype — the binders of
    `construction_lhu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lhu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  lhu_input : PureSpec.LhuInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  execRow : List (Interaction.ExecutionBusEntry FGL)
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
    i.val (busLd trace binding i execRow).e1
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
      i.val = (2 : FGL)
  h_opcode_assumptions : PureSpec.lhu_state_assumptions lhu_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lhu_input.r1_val.toNat + (BitVec.signExtend 64 lhu_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lhu_input.rd = 0
  h_addr2_idx :
    lhu_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADHU_pure lhu_input).nextPC
  h_memory_timeline :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_mem_match :
    ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lwu` archetype — the binders of
    `construction_lwu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lwu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  lwu_input : PureSpec.LwuInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  execRow : List (Interaction.ExecutionBusEntry FGL)
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
    i.val (busLd trace binding i execRow).e1
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).ind_width
      i.val = (4 : FGL)
  h_opcode_assumptions : PureSpec.lwu_state_assumptions lwu_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lwu_input.r1_val.toNat + (BitVec.signExtend 64 lwu_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lwu_input.rd = 0
  h_addr2_idx :
    lwu_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADWU_pure lwu_input).nextPC
  h_memory_timeline :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_mem_match :
    ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lb` archetype — the binders of
    `construction_lb_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lb
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  lb_input : PureSpec.LbInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary : ℕ
  offset : ℕ
  env : Environment FGL
  h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SIGNEXTEND_B
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_opcode_assumptions : PureSpec.lb_state_assumptions lb_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lb_input.r1_val.toNat + (BitVec.signExtend 64 lb_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lb_input.rd = 0
  h_addr2_idx :
    lb_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADB_pure lb_input).nextPC
  h_memory_timeline :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_mem_match :
    ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lh` archetype — the binders of
    `construction_lh_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lh
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  lh_input : PureSpec.LhInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary : ℕ
  offset : ℕ
  env : Environment FGL
  h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SIGNEXTEND_H
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_opcode_assumptions : PureSpec.lh_state_assumptions lh_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lh_input.r1_val.toNat + (BitVec.signExtend 64 lh_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lh_input.rd = 0
  h_addr2_idx :
    lh_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADH_pure lh_input).nextPC
  h_memory_timeline :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_mem_match :
    ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `lw` archetype — the binders of
    `construction_lw_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_lw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  lw_input : PureSpec.LwInput
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary : ℕ
  offset : ℕ
  env : Environment FGL
  h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_SIGNEXTEND_W
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_opcode_assumptions : PureSpec.lw_state_assumptions lw_input (binding.stateAt i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      lw_input.r1_val.toNat + (BitVec.signExtend 64 lw_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      lw_input.rd = 0
  h_addr2_idx :
    lw_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding.stateAt i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_exec_len : (busLd trace binding i execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i execRow).exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADW_pure lw_input).nextPC
  h_memory_timeline :
    ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence (binding.stateAt i)
      (busLd trace binding i execRow).e1
  h_mem_match :
    ZiskFv.Airs.MemoryBus.matches_memory_payload (busLd trace binding i execRow).e1
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage (ZiskFv.AirsClean.Mem.rowAt mem r_mem)) 1 2)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

/-- Irreducible per-row residuals for the `beq` archetype — the binders of
    `construction_beq_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_beq
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  beq_input : PureSpec.BeqInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BEQ `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_EQ
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_jmp_offset2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset2
      i.val = 4
  h_input_imm : beq_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding.stateAt i)
    = EStateM.Result.ok beq_input.r1_val (binding.stateAt i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding.stateAt i)
    = EStateM.Result.ok beq_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some beq_input.PC
  h_input_misa : (binding.stateAt i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BEQ_pure beq_input).nextPC
  h_not_throws : (PureSpec.execute_BEQ_pure beq_input).throws = false
  h_success : (PureSpec.execute_BEQ_pure beq_input).success = true

/-- Irreducible per-row residuals for the `bne` archetype — the binders of
    `construction_bne_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_bne
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  bne_input : PureSpec.BneInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BNE `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_EQ
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_jmp_offset1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset1
      i.val = 4
  h_input_imm : bne_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding.stateAt i)
    = EStateM.Result.ok bne_input.r1_val (binding.stateAt i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding.stateAt i)
    = EStateM.Result.ok bne_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some bne_input.PC
  h_input_misa : (binding.stateAt i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BNE_pure bne_input).nextPC
  h_not_throws : (PureSpec.execute_BNE_pure bne_input).throws = false
  h_success : (PureSpec.execute_BNE_pure bne_input).success = true

/-- Irreducible per-row residuals for the `blt` archetype — the binders of
    `construction_blt_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_blt
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  blt_input : PureSpec.BltInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BLT `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_jmp_offset2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset2
      i.val = 4
  h_input_imm : blt_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding.stateAt i)
    = EStateM.Result.ok blt_input.r1_val (binding.stateAt i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding.stateAt i)
    = EStateM.Result.ok blt_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some blt_input.PC
  h_input_misa : (binding.stateAt i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BLT_pure blt_input).nextPC
  h_not_throws : (PureSpec.execute_BLT_pure blt_input).throws = false
  h_success : (PureSpec.execute_BLT_pure blt_input).success = true

/-- Irreducible per-row residuals for the `bge` archetype — the binders of
    `construction_bge_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_bge
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  bge_input : PureSpec.BgeInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BGE `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_jmp_offset1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset1
      i.val = 4
  h_input_imm : bge_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding.stateAt i)
    = EStateM.Result.ok bge_input.r1_val (binding.stateAt i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding.stateAt i)
    = EStateM.Result.ok bge_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some bge_input.PC
  h_input_misa : (binding.stateAt i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BGE_pure bge_input).nextPC
  h_not_throws : (PureSpec.execute_BGE_pure bge_input).throws = false
  h_success : (PureSpec.execute_BGE_pure bge_input).success = true

/-- Irreducible per-row residuals for the `bltu` archetype — the binders of
    `construction_bltu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_bltu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  bltu_input : PureSpec.BltuInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BLTU `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_jmp_offset2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset2
      i.val = 4
  h_input_imm : bltu_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding.stateAt i)
    = EStateM.Result.ok bltu_input.r1_val (binding.stateAt i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding.stateAt i)
    = EStateM.Result.ok bltu_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some bltu_input.PC
  h_input_misa : (binding.stateAt i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BLTU_pure bltu_input).nextPC
  h_not_throws : (PureSpec.execute_BLTU_pure bltu_input).throws = false
  h_success : (PureSpec.execute_BLTU_pure bltu_input).success = true

/-- Irreducible per-row residuals for the `bgeu` archetype — the binders of
    `construction_bgeu_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_bgeu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  bgeu_input : PureSpec.BgeuInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  -- Decode pins (genuine trace residuals consumed by the BGEU `aeneasBridgeTrust`).
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 0
  h_jmp_offset1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset1
      i.val = 4
  h_input_imm : bgeu_input.imm = imm
  h_input_r1 : read_xreg (regidx_to_fin r1) (binding.stateAt i)
    = EStateM.Result.ok bgeu_input.r1_val (binding.stateAt i)
  h_input_r2 : read_xreg (regidx_to_fin r2) (binding.stateAt i)
    = EStateM.Result.ok bgeu_input.r2_val (binding.stateAt i)
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some bgeu_input.PC
  h_input_misa : (binding.stateAt i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_exec_len : exec_row.length = 2
  h_e0_mult : exec_row[0]!.multiplicity = -1
  h_e1_mult : exec_row[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = (PureSpec.execute_BGEU_pure bgeu_input).nextPC
  h_not_throws : (PureSpec.execute_BGEU_pure bgeu_input).throws = false
  h_success : (PureSpec.execute_BGEU_pure bgeu_input).success = true

/-- Irreducible per-row residuals for the `jal` archetype — the binders of
    `construction_jal_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_jal
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  jal_input : PureSpec.JalInput
  imm : BitVec 21
  rd : regidx
  misa_val : RegisterType Register.misa
  nextPC_val : BitVec 64
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_FLAG
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 0
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 1
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset2
      i.val = 4
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).pc i.val).val
      = jal_input.PC.toNat
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = nextPC_val
  h_input_rd : jal_input.rd = regidx_to_fin rd
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some jal_input.PC
  h_input_misa : (binding.stateAt i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_success : (PureSpec.execute_JAL_pure jal_input).success = true
  h_nextPC_option : (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val
  h_rd_idx : jal_input.rd = Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr
  h_input_imm : jal_input.imm = imm
  h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false
  h_pc_bound : jal_input.PC.toNat < GL_prime - 4
  h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296

/-- Irreducible per-row residuals for the `jalr` archetype — the binders of
    `construction_jalr_sound` after `(trace) (binding) (i)`, verbatim. -/
structure RowData_jalr
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  jalr_input : PureSpec.JalrInput
  imm : BitVec 12
  rs1 : regidx
  rd : regidx
  misa_val : RegisterType Register.misa
  mseccfg : RegisterType Register.mseccfg
  nextPC_val : BitVec 64
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
      i.val = ZiskFv.Trusted.OP_AND
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
      i.val = 1
  h_flag :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).flag
      i.val = 0
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
      i.val = 1
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = nextPC_val
  h_input_rd : jalr_input.rd = regidx_to_fin rd
  h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some jalr_input.PC
  h_input_misa : (binding.stateAt i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_success : (PureSpec.execute_JALR_pure jalr_input).success = true
  h_nextPC_option : (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val
  h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr
  h_input_imm : jalr_input.imm = imm
  h_input_rs1 : read_xreg (regidx_to_fin rs1) (binding.stateAt i)
    = EStateM.Result.ok jalr_input.rs1_val (binding.stateAt i)
  h_cur_privilege : Sail.readReg Register.cur_privilege (binding.stateAt i)
    = EStateM.Result.ok Privilege.Machine (binding.stateAt i)
  h_mseccfg : Sail.readReg Register.mseccfg (binding.stateAt i)
    = EStateM.Result.ok mseccfg (binding.stateAt i)
  h_link_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).pc i.val
      + (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset2
          i.val).val
      = (jalr_input.PC + 4#64).toNat
  h_pc_bound : jalr_input.PC.toNat < GL_prime - 4
  h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296

/-- Per-row construction data: one arm per sound construction archetype (55).
    Each arm carries a single `RowData_<op>` payload (its irreducible residuals).
    The 8 defect/decode-gap opcodes (7 signed-M + FENCE) have NO arm. -/
inductive RowConstructionData
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  | sub (d : RowData_sub trace binding i) : RowConstructionData trace binding i
  | and (d : RowData_and trace binding i) : RowConstructionData trace binding i
  | or (d : RowData_or trace binding i) : RowConstructionData trace binding i
  | xor (d : RowData_xor trace binding i) : RowConstructionData trace binding i
  | slt (d : RowData_slt trace binding i) : RowConstructionData trace binding i
  | sltu (d : RowData_sltu trace binding i) : RowConstructionData trace binding i
  | andi (d : RowData_andi trace binding i) : RowConstructionData trace binding i
  | ori (d : RowData_ori trace binding i) : RowConstructionData trace binding i
  | xori (d : RowData_xori trace binding i) : RowConstructionData trace binding i
  | slti (d : RowData_slti trace binding i) : RowConstructionData trace binding i
  | sltiu (d : RowData_sltiu trace binding i) : RowConstructionData trace binding i
  | sll (d : RowData_sll trace binding i) : RowConstructionData trace binding i
  | srl (d : RowData_srl trace binding i) : RowConstructionData trace binding i
  | sra (d : RowData_sra trace binding i) : RowConstructionData trace binding i
  | slli (d : RowData_slli trace binding i) : RowConstructionData trace binding i
  | srli (d : RowData_srli trace binding i) : RowConstructionData trace binding i
  | srai (d : RowData_srai trace binding i) : RowConstructionData trace binding i
  | sllw (d : RowData_sllw trace binding i) : RowConstructionData trace binding i
  | srlw (d : RowData_srlw trace binding i) : RowConstructionData trace binding i
  | sraw (d : RowData_sraw trace binding i) : RowConstructionData trace binding i
  | slliw (d : RowData_slliw trace binding i) : RowConstructionData trace binding i
  | srliw (d : RowData_srliw trace binding i) : RowConstructionData trace binding i
  | sraiw (d : RowData_sraiw trace binding i) : RowConstructionData trace binding i
  | add (d : RowData_add trace binding i) : RowConstructionData trace binding i
  | addi (d : RowData_addi trace binding i) : RowConstructionData trace binding i
  | subw (d : RowData_subw trace binding i) : RowConstructionData trace binding i
  | addw (d : RowData_addw trace binding i) : RowConstructionData trace binding i
  | addiw (d : RowData_addiw trace binding i) : RowConstructionData trace binding i
  | lui (d : RowData_lui trace binding i) : RowConstructionData trace binding i
  | auipc (d : RowData_auipc trace binding i) : RowConstructionData trace binding i
  | mulw (d : RowData_mulw trace binding i) : RowConstructionData trace binding i
  | mulhu (d : RowData_mulhu trace binding i) : RowConstructionData trace binding i
  | divu (d : RowData_divu trace binding i) : RowConstructionData trace binding i
  | divuw (d : RowData_divuw trace binding i) : RowConstructionData trace binding i
  | remu (d : RowData_remu trace binding i) : RowConstructionData trace binding i
  | remuw (d : RowData_remuw trace binding i) : RowConstructionData trace binding i
  | sb (d : RowData_sb trace binding i) : RowConstructionData trace binding i
  | sh (d : RowData_sh trace binding i) : RowConstructionData trace binding i
  | sw (d : RowData_sw trace binding i) : RowConstructionData trace binding i
  | sd (d : RowData_sd trace binding i) : RowConstructionData trace binding i
  | ld (d : RowData_ld trace binding i) : RowConstructionData trace binding i
  | lbu (d : RowData_lbu trace binding i) : RowConstructionData trace binding i
  | lhu (d : RowData_lhu trace binding i) : RowConstructionData trace binding i
  | lwu (d : RowData_lwu trace binding i) : RowConstructionData trace binding i
  | lb (d : RowData_lb trace binding i) : RowConstructionData trace binding i
  | lh (d : RowData_lh trace binding i) : RowConstructionData trace binding i
  | lw (d : RowData_lw trace binding i) : RowConstructionData trace binding i
  | beq (d : RowData_beq trace binding i) : RowConstructionData trace binding i
  | bne (d : RowData_bne trace binding i) : RowConstructionData trace binding i
  | blt (d : RowData_blt trace binding i) : RowConstructionData trace binding i
  | bge (d : RowData_bge trace binding i) : RowConstructionData trace binding i
  | bltu (d : RowData_bltu trace binding i) : RowConstructionData trace binding i
  | bgeu (d : RowData_bgeu trace binding i) : RowConstructionData trace binding i
  | jal (d : RowData_jal trace binding i) : RowConstructionData trace binding i
  | jalr (d : RowData_jalr trace binding i) : RowConstructionData trace binding i

/-- The canonical per-step compliance conclusion for one row, keyed on trace
    data. Dispatches on the row archetype to the matching
    `construction_<op>_sound` conclusion (the `bus_effect`-form). -/
def StepCompliance
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    RowConstructionData trace binding i → Prop
  | .sub d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SUB))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .and d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.AND))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .or d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.OR))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .xor d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.XOR))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .slt d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLT))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sltu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLTU))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .andi d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ANDI))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .ori d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ORI))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .xori d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.XORI))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .slti d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTI))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sltiu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTIU))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sll d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLL)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .srl d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRL)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sra d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRA)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .slli d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SLLI)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .srli d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRLI)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .srai d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRAI)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sllw d =>
      execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SLLW)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .srlw d =>
      execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SRLW)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sraw d =>
      execute_instruction (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SRAW)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .slliw d =>
      execute_instruction
      (instruction.SHIFTIWOP (d.slliw_input.shamt, d.r1, d.rd, sopw.SLLIW)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .srliw d =>
      execute_instruction
      (instruction.SHIFTIWOP (d.srliw_input.shamt, d.r1, d.rd, sopw.SRLIW)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sraiw d =>
      execute_instruction
      (instruction.SHIFTIWOP (d.sraiw_input.shamt, d.r1, d.rd, sopw.SRAIW)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .add d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.ADD))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .addi d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ADDI))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .subw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SUBW))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .addw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.ADDW))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .addiw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (d.imm, d.r1, d.rd))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .lui d =>
      execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.LUI)) (binding.stateAt i)
      = (bus_effect d.execRow [eRdLui trace binding i] (binding.stateAt i)).2
  | .auipc d =>
      execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.AUIPC)) (binding.stateAt i)
      = (bus_effect d.execRow [eRdLui trace binding i] (binding.stateAt i)).2
  | .mulw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (d.r2, d.r1, d.rd))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .mulhu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Unsigned
             signed_rs2 := .Unsigned }))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .divu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .divuw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .remu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .remuw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i d.execRow).exec_row
          [ (busSub trace binding i d.execRow).e0
          , (busSub trace binding i d.execRow).e1
          , (busSub trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sb d =>
      execute_instruction (instruction.STORE (
        d.sb_input.imm,
        regidx.Regidx d.sb_input.r2,
        regidx.Regidx d.sb_input.r1,
        1
      )) (binding.stateAt i)
        = (bus_effect (busSt trace binding i d.execRow).exec_row
            [ (busSt trace binding i d.execRow).e0
            , (busSt trace binding i d.execRow).e1
            , (busSt trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sh d =>
      execute_instruction (instruction.STORE (
        d.sh_input.imm,
        regidx.Regidx d.sh_input.r2,
        regidx.Regidx d.sh_input.r1,
        2
      )) (binding.stateAt i)
        = (bus_effect (busSt trace binding i d.execRow).exec_row
            [ (busSt trace binding i d.execRow).e0
            , (busSt trace binding i d.execRow).e1
            , (busSt trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sw d =>
      execute_instruction (instruction.STORE (
        d.sw_input.imm,
        regidx.Regidx d.sw_input.r2,
        regidx.Regidx d.sw_input.r1,
        4
      )) (binding.stateAt i)
        = (bus_effect (busSt trace binding i d.execRow).exec_row
            [ (busSt trace binding i d.execRow).e0
            , (busSt trace binding i d.execRow).e1
            , (busSt trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .sd d =>
      execute_instruction (instruction.STORE (
        d.sd_input.imm,
        regidx.Regidx d.sd_input.r2,
        regidx.Regidx d.sd_input.r1,
        8
      )) (binding.stateAt i)
        = (bus_effect (busSt trace binding i d.execRow).exec_row
            [ (busSt trace binding i d.execRow).e0
            , (busSt trace binding i d.execRow).e1
            , (busSt trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .ld d =>
      execute_instruction (instruction.LOAD (
        d.ld_input.imm,
        regidx.Regidx d.ld_input.r1,
        regidx.Regidx d.ld_input.rd,
        false,
        8
      )) (binding.stateAt i)
        = (bus_effect (busLd trace binding i d.execRow).exec_row
            [ (busLd trace binding i d.execRow).e0
            , (busLd trace binding i d.execRow).e1
            , (busLd trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .lbu d =>
      execute_instruction (instruction.LOAD (
        d.lbu_input.imm,
        regidx.Regidx d.lbu_input.r1,
        regidx.Regidx d.lbu_input.rd,
        true,
        1
      )) (binding.stateAt i)
        = (bus_effect (busLd trace binding i d.execRow).exec_row
            [ (busLd trace binding i d.execRow).e0
            , (busLd trace binding i d.execRow).e1
            , (busLd trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .lhu d =>
      execute_instruction (instruction.LOAD (
        d.lhu_input.imm,
        regidx.Regidx d.lhu_input.r1,
        regidx.Regidx d.lhu_input.rd,
        true,
        2
      )) (binding.stateAt i)
        = (bus_effect (busLd trace binding i d.execRow).exec_row
            [ (busLd trace binding i d.execRow).e0
            , (busLd trace binding i d.execRow).e1
            , (busLd trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .lwu d =>
      execute_instruction (instruction.LOAD (
        d.lwu_input.imm,
        regidx.Regidx d.lwu_input.r1,
        regidx.Regidx d.lwu_input.rd,
        true,
        4
      )) (binding.stateAt i)
        = (bus_effect (busLd trace binding i d.execRow).exec_row
            [ (busLd trace binding i d.execRow).e0
            , (busLd trace binding i d.execRow).e1
            , (busLd trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .lb d =>
      execute_instruction (instruction.LOAD (
        d.lb_input.imm,
        regidx.Regidx d.lb_input.r1,
        regidx.Regidx d.lb_input.rd,
        false,
        1
      )) (binding.stateAt i)
        = (bus_effect (busLd trace binding i d.execRow).exec_row
            [ (busLd trace binding i d.execRow).e0
            , (busLd trace binding i d.execRow).e1
            , (busLd trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .lh d =>
      execute_instruction (instruction.LOAD (
        d.lh_input.imm,
        regidx.Regidx d.lh_input.r1,
        regidx.Regidx d.lh_input.rd,
        false,
        2
      )) (binding.stateAt i)
        = (bus_effect (busLd trace binding i d.execRow).exec_row
            [ (busLd trace binding i d.execRow).e0
            , (busLd trace binding i d.execRow).e1
            , (busLd trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .lw d =>
      execute_instruction (instruction.LOAD (
        d.lw_input.imm,
        regidx.Regidx d.lw_input.r1,
        regidx.Regidx d.lw_input.rd,
        false,
        4
      )) (binding.stateAt i)
        = (bus_effect (busLd trace binding i d.execRow).exec_row
            [ (busLd trace binding i d.execRow).e0
            , (busLd trace binding i d.execRow).e1
            , (busLd trace binding i d.execRow).e2 ] (binding.stateAt i)).2
  | .beq d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BEQ)) (binding.stateAt i)
      = (bus_effect d.exec_row [] (binding.stateAt i)).2
  | .bne d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BNE)) (binding.stateAt i)
      = (bus_effect d.exec_row [] (binding.stateAt i)).2
  | .blt d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLT)) (binding.stateAt i)
      = (bus_effect d.exec_row [] (binding.stateAt i)).2
  | .bge d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGE)) (binding.stateAt i)
      = (bus_effect d.exec_row [] (binding.stateAt i)).2
  | .bltu d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLTU)) (binding.stateAt i)
      = (bus_effect d.exec_row [] (binding.stateAt i)).2
  | .bgeu d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGEU)) (binding.stateAt i)
      = (bus_effect d.exec_row [] (binding.stateAt i)).2
  | .jal d =>
      execute_instruction (instruction.JAL (d.imm, d.rd)) (binding.stateAt i)
      = (bus_effect d.execRow [eRdLui trace binding i] (binding.stateAt i)).2
  | .jalr d =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (d.imm, d.rs1, d.rd))) (binding.stateAt i)
      = (bus_effect d.execRow [eRdLui trace binding i] (binding.stateAt i)).2

/-- Per-row dispatch: each archetype's residual bundle discharges its
    `StepCompliance` via the matching `construction_<op>_sound`. -/
theorem stepCompliance_of_rowData
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowConstructionData trace binding i) :
    StepCompliance trace binding i d := by
  cases d with
  | sub d =>
      exact construction_sub_sound trace binding i d.sub_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | and d =>
      exact construction_and_sound trace binding i d.and_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | or d =>
      exact construction_or_sound trace binding i d.or_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | xor d =>
      exact construction_xor_sound trace binding i d.xor_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | slt d =>
      exact construction_slt_sound trace binding i d.slt_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | sltu d =>
      exact construction_sltu_sound trace binding i d.sltu_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | andi d =>
      exact construction_andi_sound trace binding i d.andi_input d.r1 d.rd d.imm d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_imm d.h_input_pc
        d.h_input_rd d.h_a_lo_t d.h_a_hi_t d.h_andi_subset d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | ori d =>
      exact construction_ori_sound trace binding i d.ori_input d.r1 d.rd d.imm d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_imm d.h_input_pc
        d.h_input_rd d.h_a_lo_t d.h_a_hi_t d.h_ori_subset d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | xori d =>
      exact construction_xori_sound trace binding i d.xori_input d.r1 d.rd d.imm d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_imm d.h_input_pc
        d.h_input_rd d.h_a_lo_t d.h_a_hi_t d.h_xori_subset d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | slti d =>
      exact construction_slti_sound trace binding i d.slti_input d.r1 d.rd d.imm d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_imm d.h_input_pc
        d.h_input_rd d.h_a_lo_t d.h_a_hi_t d.h_slti_subset d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | sltiu d =>
      exact construction_sltiu_sound trace binding i d.sltiu_input d.r1 d.rd d.imm d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_imm d.h_input_pc
        d.h_input_rd d.h_a_lo_t d.h_a_hi_t d.h_sltiu_subset d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | sll d =>
      exact construction_sll_sound trace binding i d.sll_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | srl d =>
      exact construction_srl_sound trace binding i d.srl_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | sra d =>
      exact construction_sra_sound trace binding i d.sra_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | slli d =>
      exact construction_slli_sound trace binding i d.slli_input d.r1 d.rd d.shamt d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_shamt d.h_input_pc
        d.h_input_rd d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | srli d =>
      exact construction_srli_sound trace binding i d.srli_input d.r1 d.rd d.shamt d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_shamt d.h_input_pc
        d.h_input_rd d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | srai d =>
      exact construction_srai_sound trace binding i d.srai_input d.r1 d.rd d.shamt d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_shamt d.h_input_pc
        d.h_input_rd d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | sllw d =>
      exact construction_sllw_sound trace binding i d.sllw_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | srlw d =>
      exact construction_srlw_sound trace binding i d.srlw_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | sraw d =>
      exact construction_sraw_sound trace binding i d.sraw_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | slliw d =>
      exact construction_slliw_sound trace binding i d.slliw_input d.r1 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_pc d.h_input_rd d.h_a_lo_t
        d.h_a_hi_t d.h_b_lo_t d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
        d.h_rd_idx
  | srliw d =>
      exact construction_srliw_sound trace binding i d.srliw_input d.r1 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_pc d.h_input_rd d.h_a_lo_t
        d.h_a_hi_t d.h_b_lo_t d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
        d.h_rd_idx
  | sraiw d =>
      exact construction_sraiw_sound trace binding i d.sraiw_input d.r1 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_pc d.h_input_rd d.h_a_lo_t
        d.h_a_hi_t d.h_b_lo_t d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
        d.h_rd_idx
  | add d =>
      exact construction_add_sound trace binding i d.add_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | addi d =>
      exact construction_addi_sound trace binding i d.addi_input d.r1 d.rd d.imm d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_set_pc d.h_input_r1 d.h_input_imm d.h_input_pc
        d.h_input_rd d.h_a_lo_t d.h_a_hi_t d.h_addi_subset d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | subw d =>
      exact construction_subw_sound trace binding i d.subw_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | addw d =>
      exact construction_addw_sound trace binding i d.addw_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | addiw d =>
      exact construction_addiw_sound trace binding i d.addiw_input d.r1 d.rd d.imm d.h_main_op
        d.h_main_active d.h_m32 d.h_store_pc d.h_input_r1 d.h_input_imm d.h_input_pc
        d.h_input_rd d.h_a_lo_t d.h_a_hi_t d.h_addiw_subset d.execRow d.h_exec_len d.h_e0_mult
        d.h_e1_mult d.h_nextPC_matches d.h_rd_idx
  | lui d =>
      exact construction_lui_sound trace binding i d.lui_input d.imm d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_set_pc d.h_store_pc d.h_input_imm d.h_input_rd d.h_input_pc
        d.h_imm_lo_nat d.h_imm_hi_nat d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult
        d.h_nextPC_matches d.h_rd_idx
  | auipc d =>
      exact construction_auipc_sound trace binding i d.auipc_input d.imm d.rd d.h_main_op
        d.h_main_active d.h_m32 d.h_set_pc d.h_store_pc d.h_input_imm d.h_input_rd d.h_input_pc
        d.h_offset_bridge d.h_pc_bridge d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult
        d.h_nextPC_matches d.h_rd_idx d.h_no_wrap d.h_pc_offset_lt_2_32
  | mulw d =>
      exact construction_mulw_sound trace binding i d.mulw_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.h_a23
        d.h_b23 d.h_sext_choice d.h_rs1_value d.h_rs2_value
  | mulhu d =>
      exact construction_mulhu_sound trace binding i d.mulhu_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.bounds
        d.h_rs1_value d.h_rs2_value
  | divu d =>
      exact construction_divu_sound trace binding i d.divu_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.bounds
        d.remainder_bound d.h_rs1_value d.h_rs2_value
  | divuw d =>
      exact construction_divuw_sound trace binding i d.divuw_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.bounds
        d.remainder_bound d.h_b23 d.h_c23 d.h_sext_choice d.h_rs1_value d.h_rs2_value
  | remu d =>
      exact construction_remu_sound trace binding i d.remu_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.bounds
        d.remainder_bound d.h_rs1_value d.h_rs2_value
  | remuw d =>
      exact construction_remuw_sound trace binding i d.remuw_input d.r1 d.r2 d.rd d.h_main_op
        d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
        d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.bounds
        d.remainder_bound d.h_b23 d.h_c23 d.h_sext_choice d.h_rs1_value d.h_rs2_value
  | sb d =>
      exact construction_sb_sound trace binding i d.sb_input d.regs d.h_main_active d.h_main_op
        d.h_store_pc d.h_main_ind_width d.h_opcode_assumptions d.h_addr2 d.h_b0_value
        d.h_b1_value d.execRow d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult
        d.h_nextPC_matches d.h_m1 d.h_m2 d.h_m3 d.h_m4 d.h_m5 d.h_m6 d.h_m7
  | sh d =>
      exact construction_sh_sound trace binding i d.sh_input d.regs d.h_main_active d.h_main_op
        d.h_store_pc d.h_main_ind_width d.h_opcode_assumptions d.h_addr2 d.h_b0_value
        d.h_b1_value d.execRow d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult
        d.h_nextPC_matches d.h_m2 d.h_m3 d.h_m4 d.h_m5 d.h_m6 d.h_m7
  | sw d =>
      exact construction_sw_sound trace binding i d.sw_input d.regs d.h_main_active d.h_main_op
        d.h_store_pc d.h_main_ind_width d.h_opcode_assumptions d.h_addr2 d.h_b0_value
        d.h_b1_value d.execRow d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult
        d.h_nextPC_matches d.h_m4 d.h_m5 d.h_m6 d.h_m7
  | sd d =>
      exact construction_sd_sound trace binding i d.sd_input d.regs d.h_main_active d.h_main_op
        d.h_store_pc d.h_opcode_assumptions d.h_addr2 d.h_b0_value d.h_b1_value d.execRow
        d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
  | ld d =>
      exact construction_ld_sound trace binding i d.ld_input d.regs d.mem d.r_mem
        d.h_main_active d.h_main_op d.h_store_pc d.h_opcode_assumptions d.h_addr1
        d.h_addr2_zero_iff d.h_addr2_idx d.execRow d.h_risc_v_assumptions d.h_exec_len
        d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_memory_timeline d.h_mem_match d.h_mem_sel
        d.h_mem_wr
  | lbu d =>
      exact construction_lbu_sound trace binding i d.lbu_input d.regs d.mem d.r_mem d.execRow
        d.align d.h_main_active d.h_main_op d.h_store_pc d.h_width d.h_opcode_assumptions
        d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.h_risc_v_assumptions d.h_exec_len
        d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_memory_timeline d.h_mem_match d.h_mem_sel
        d.h_mem_wr
  | lhu d =>
      exact construction_lhu_sound trace binding i d.lhu_input d.regs d.mem d.r_mem d.execRow
        d.align d.h_main_active d.h_main_op d.h_store_pc d.h_width d.h_opcode_assumptions
        d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.h_risc_v_assumptions d.h_exec_len
        d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_memory_timeline d.h_mem_match d.h_mem_sel
        d.h_mem_wr
  | lwu d =>
      exact construction_lwu_sound trace binding i d.lwu_input d.regs d.mem d.r_mem d.execRow
        d.align d.h_main_active d.h_main_op d.h_store_pc d.h_width d.h_opcode_assumptions
        d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.h_risc_v_assumptions d.h_exec_len
        d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_memory_timeline d.h_mem_match d.h_mem_sel
        d.h_mem_wr
  | lb d =>
      exact construction_lb_sound trace binding i d.lb_input d.regs d.mem d.r_mem d.v d.r_binary
        d.offset d.env d.h_static d.h_match d.h_main_active d.h_main_op d.h_store_pc
        d.h_opcode_assumptions d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.execRow
        d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
        d.h_memory_timeline d.h_mem_match d.h_mem_sel d.h_mem_wr
  | lh d =>
      exact construction_lh_sound trace binding i d.lh_input d.regs d.mem d.r_mem d.v d.r_binary
        d.offset d.env d.h_static d.h_match d.h_main_active d.h_main_op d.h_store_pc
        d.h_opcode_assumptions d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.execRow
        d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
        d.h_memory_timeline d.h_mem_match d.h_mem_sel d.h_mem_wr
  | lw d =>
      exact construction_lw_sound trace binding i d.lw_input d.regs d.mem d.r_mem d.v d.r_binary
        d.offset d.env d.h_static d.h_match d.h_main_active d.h_main_op d.h_store_pc
        d.h_opcode_assumptions d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.execRow
        d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
        d.h_memory_timeline d.h_mem_match d.h_mem_sel d.h_mem_wr
  | beq d =>
      exact construction_beq_sound trace binding i d.beq_input d.imm d.r1 d.r2 d.misa_val
        d.exec_row d.h_input_imm d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_misa
        d.h_misa_c d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_not_throws
        d.h_success
  | bne d =>
      exact construction_bne_sound trace binding i d.bne_input d.imm d.r1 d.r2 d.misa_val
        d.exec_row d.h_input_imm d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_misa
        d.h_misa_c d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_not_throws
        d.h_success
  | blt d =>
      exact construction_blt_sound trace binding i d.blt_input d.imm d.r1 d.r2 d.misa_val
        d.exec_row d.h_input_imm d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_misa
        d.h_misa_c d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_not_throws
        d.h_success
  | bge d =>
      exact construction_bge_sound trace binding i d.bge_input d.imm d.r1 d.r2 d.misa_val
        d.exec_row d.h_input_imm d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_misa
        d.h_misa_c d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_not_throws
        d.h_success
  | bltu d =>
      exact construction_bltu_sound trace binding i d.bltu_input d.imm d.r1 d.r2 d.misa_val
        d.exec_row d.h_input_imm d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_misa
        d.h_misa_c d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_not_throws
        d.h_success
  | bgeu d =>
      exact construction_bgeu_sound trace binding i d.bgeu_input d.imm d.r1 d.r2 d.misa_val
        d.exec_row d.h_input_imm d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_misa
        d.h_misa_c d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_not_throws
        d.h_success
  | jal d =>
      exact construction_jal_sound trace binding i d.jal_input d.imm d.rd d.misa_val
        d.nextPC_val d.h_main_op d.h_main_active d.h_m32 d.h_set_pc d.h_store_pc d.h_jmp2
        d.h_pc_bridge d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
        d.h_input_rd d.h_input_pc d.h_input_misa d.h_misa_c d.h_success d.h_nextPC_option
        d.h_rd_idx d.h_input_imm d.h_not_throws d.h_pc_bound d.h_pc_offset_lt_2_32
  | jalr d =>
      exact construction_jalr_sound trace binding i d.jalr_input d.imm d.rs1 d.rd d.misa_val
        d.mseccfg d.nextPC_val d.h_main_op d.h_main_active d.h_flag d.h_m32 d.h_set_pc
        d.h_store_pc d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
        d.h_input_rd d.h_input_pc d.h_input_misa d.h_misa_c d.h_success d.h_nextPC_option
        d.h_rd_idx d.h_input_imm d.h_input_rs1 d.h_cur_privilege d.h_mseccfg d.h_link_bridge
        d.h_pc_bound d.h_pc_offset_lt_2_32

/-- **Target P5 theorem (#61 closure over the 55 sound constructions).**

    From an accepted full-ensemble trace, a program binding, and a per-row
    classification (`rowData : ∀ i, RowConstructionData …` packaging each row's
    genuinely-irreducible residuals), EVERY row satisfies the canonical per-step
    compliance conclusion — with NO caller-supplied `OpEnvelope`. The envelope
    for each row is constructed inside via `stepCompliance_of_rowData`.

    COVERAGE: the `∀ i, RowConstructionData trace binding i` premise IS the
    explicit coverage obligation — a witness per row that the row is one of the
    55 classifiable, non-defect RV64IM opcodes. The 8 defect/decode-gap ops (7
    signed-M + FENCE) have no `RowConstructionData` arm and are out of scope;
    they are covered solely by the global theorem's ∀-env `NoKnownDefect` /
    decode-gap exclusion. -/
theorem zisk_compliant_of_accepted_trace
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (rowData : ∀ i : Fin trace.length, RowConstructionData trace binding i) :
    ∀ i : Fin trace.length, StepCompliance trace binding i (rowData i) :=
  fun i => stepCompliance_of_rowData trace binding i (rowData i)

/-! ## Strengthened export: env-constructed channel-balance form

The theorems below are STRICTLY STRONGER than the corresponding `bus_effect`-form
`StepCompliance` arms above.  For each strengthened arm they prove the EXACT
conclusion of the OLD global theorem `zisk_riscv_compliant_program_bus` — the
channel-balance `state_effect_via_channels` form — but with the `OpEnvelope`
**constructed from the accepted trace** (rather than supplied as a parameter).
The envelope per row is assembled by re-running the same provider-match /
input-assembly derivations `construction_<op>_sound` uses internally; the three
global-theorem hypotheses are discharged in place:
`aeneasBridgeTrust` from the derived row-binding facts, `memoryTimelineConstruction`
trivially (non-load arms), and `NoKnownDefect` trivially (the strengthened arms
are all non-defect opcodes).  Hence anything the old theorem yields for these
arms, the strengthened theorem yields from the trace.

Non-vacuity: each envelope is the real `OpEnvelope.<op>` over the committed
trace's `mainOfTable` row; `execRow` remains a genuine ∀-binder inside the
`RowData_<op>`; `NoKnownDefect` is a TRUE fact (not a contradictory hypothesis);
no `False.elim` or contradictory pair is used.
-/

/-- Strengthened `sub` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.sub` arm
    from accepted-trace data (reusing `construction_sub_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.sub`. -/
theorem stepStrong_sub
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_sub trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .sub .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SUB))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_sub_from_binding
      trace binding i d.h_main_active d.h_main_op
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SUB :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.sub_input.r1_val d.sub_input.r2_val d.sub_input.rd d.sub_input.PC
      (PureSpec.execute_RTYPE_sub_pure d.sub_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_SUB : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_SUB, ZiskFv.Trusted.OP_SUB] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_SUB (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_SUB])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.sub_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.sub_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.sub_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.sub_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sub d.sub_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1

/-- Strengthened `and` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.and` arm
    from accepted-trace data (reusing `construction_and_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.and`. -/
theorem stepStrong_and
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_and trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .and .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.AND))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_AND :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.and_input.r1_val d.and_input.r2_val d.and_input.rd d.and_input.PC
      (PureSpec.execute_RTYPE_and_pure d.and_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_AND : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND, ZiskFv.Trusted.OP_AND] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_AND (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_AND])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_AND h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_AND :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.and_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.and_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.and_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.and_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.and d.and_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1

/-- Strengthened `or` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.or` arm
    from accepted-trace data (reusing `construction_or_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.or`. -/
theorem stepStrong_or
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_or trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .or .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.OR))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i d.h_main_active (Or.inr (Or.inl d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_OR :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.or_input.r1_val d.or_input.r2_val d.or_input.rd d.or_input.PC
      (PureSpec.execute_RTYPE_or_pure d.or_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_OR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_OR, ZiskFv.Trusted.OP_OR] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_OR (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_OR])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_OR h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_OR :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.or_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.or_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.or_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.or_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.or d.or_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1

/-- Strengthened `xor` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.xor` arm
    from accepted-trace data (reusing `construction_xor_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.xor`. -/
theorem stepStrong_xor
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_xor trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .xor .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.XOR))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i d.h_main_active (Or.inr (Or.inr d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_XOR :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.xor_input.r1_val d.xor_input.r2_val d.xor_input.rd d.xor_input.PC
      (PureSpec.execute_RTYPE_xor_pure d.xor_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  -- XOR's table op is 16, NOT `< 16`, so it takes the op=16 mode-pin route
  -- (`static_table_logic_mode_pins_of_emit` + `byte_chain_discharge_logic_of_static_row`),
  -- exactly as `construction_xor_sound` does internally.
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  obtain ⟨h_row_spec, h_static⟩ := h_component_spec
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_XOR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_XOR, ZiskFv.Trusted.OP_XOR] using
      d.h_main_op
  obtain ⟨_, h_bop_row, h_bop_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      providerInput h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_XOR
      (.inr (.inr rfl)) h_emit
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_XOR :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      providerInput h_facts ZiskFv.Airs.Tables.BinaryTable.OP_XOR h_bop_row h_bop_or_sext
  have h_input_r1_row :
      d.xor_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.xor_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.xor_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.xor_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.xor d.xor_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1

/-- Strengthened `slt` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.slt` arm
    from accepted-trace data (reusing `construction_slt_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.slt`. -/
theorem stepStrong_slt
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_slt trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .slt .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLT))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_compare_from_binding
      trace binding i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_LT :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.slt_input.r1_val d.slt_input.r2_val d.slt_input.rd d.slt_input.PC
      (PureSpec.execute_RTYPE_slt_pure d.slt_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LT h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.slt_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.slt_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.slt_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.slt_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.slt d.slt_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1

/-- Strengthened `sltu` step: the channel-balance conclusion (the OLD global
    theorem's per-arm output) proven by CONSTRUCTING the `OpEnvelope.sltu` arm
    from accepted-trace data (reusing `construction_sltu_sound`'s internal
    derivations) and invoking `zisk_riscv_compliant_program_bus`. Dominates the
    `bus_effect`-form `StepCompliance.sltu`. -/
theorem stepStrong_sltu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_sltu trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .sltu .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLTU))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_compare_from_binding
      trace binding i d.h_main_active (Or.inr d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_LTU :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.sltu_input.r1_val d.sltu_input.r2_val d.sltu_input.rd d.sltu_input.PC
      (PureSpec.execute_RTYPE_sltu_pure d.sltu_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU, ZiskFv.Trusted.OP_LTU] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LTU :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.sltu_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.sltu_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_r2_row :
      d.sltu_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin d.r2) d.sltu_input.r2_val
        h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sltu d.sltu_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_r2_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.1


/-- Strengthened `andi` step: channel-balance conclusion via constructed
    `OpEnvelope.andi` + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.andi`. -/
theorem stepStrong_andi
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_andi trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .andi .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ANDI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_AND :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.andi_input.r1_val d.andi_input.imm d.andi_input.rd d.andi_input.PC
      (PureSpec.execute_ITYPE_andi_pure d.andi_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_AND : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND, ZiskFv.Trusted.OP_AND] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_AND (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_AND])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_AND h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_AND :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.andi_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.andi_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_imm_row :
      BitVec.signExtend 64 d.andi_input.imm
        = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m providerInput i.val d.andi_input.imm h_matches h_m32_zero h_match
        d.h_andi_subset
  let env : OpEnvelope state m i.val :=
    OpEnvelope.andi d.andi_input d.r1 d.rd d.imm zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_imm_row d.h_andi_subset h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_imm_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.1

/-- Strengthened `ori` step: channel-balance conclusion via constructed
    `OpEnvelope.ori` + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.ori`. -/
theorem stepStrong_ori
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_ori trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .ori .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ORI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i d.h_main_active (Or.inr (Or.inl d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_OR :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.ori_input.r1_val d.ori_input.imm d.ori_input.rd d.ori_input.PC
      (PureSpec.execute_ITYPE_ori_pure d.ori_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_OR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_OR, ZiskFv.Trusted.OP_OR] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_OR (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_OR])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_OR h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_OR :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.ori_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.ori_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_imm_row :
      BitVec.signExtend 64 d.ori_input.imm
        = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m providerInput i.val d.ori_input.imm h_matches h_m32_zero h_match
        d.h_ori_subset
  let env : OpEnvelope state m i.val :=
    OpEnvelope.ori d.ori_input d.r1 d.rd d.imm zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_imm_row d.h_ori_subset h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_imm_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.1

/-- Strengthened `xori` step: channel-balance conclusion via constructed
    `OpEnvelope.xori` + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.xori`. -/
theorem stepStrong_xori
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_xori trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .xori .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.XORI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i d.h_main_active (Or.inr (Or.inr d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_XOR :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.xori_input.r1_val d.xori_input.imm d.xori_input.rd d.xori_input.PC
      (PureSpec.execute_ITYPE_xori_pure d.xori_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  obtain ⟨h_row_spec, h_static⟩ := h_component_spec
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_XOR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_XOR, ZiskFv.Trusted.OP_XOR] using
      d.h_main_op
  obtain ⟨_, h_bop_row, h_bop_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      providerInput h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_XOR
      (.inr (.inr rfl)) h_emit
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_XOR :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      providerInput h_facts ZiskFv.Airs.Tables.BinaryTable.OP_XOR h_bop_row h_bop_or_sext
  have h_input_r1_row :
      d.xori_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.xori_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have h_input_imm_row :
      BitVec.signExtend 64 d.xori_input.imm
        = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m providerInput i.val d.xori_input.imm h_matches h_m32_zero h_match
        d.h_xori_subset
  let env : OpEnvelope state m i.val :=
    OpEnvelope.xori d.xori_input d.r1 d.rd d.imm zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_imm_row d.h_xori_subset h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_input_imm_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.1

/-- Strengthened `slti` step: channel-balance conclusion via constructed
    `OpEnvelope.slti` + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.slti`. -/
theorem stepStrong_slti
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_slti trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .slti .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_compare_from_binding
      trace binding i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_LT :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.slti_input.r1_val d.slti_input.imm d.slti_input.rd d.slti_input.PC
      (PureSpec.execute_ITYPE_slti_pure d.slti_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LT h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.slti_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.slti_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  let env : OpEnvelope state m i.val :=
    OpEnvelope.slti d.slti_input d.r1 d.rd d.imm zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_m32_zero h_input_r1_row d.h_slti_subset h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_m32_zero, h_input_r1_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.1

/-- Strengthened `sltiu` step: channel-balance conclusion via constructed
    `OpEnvelope.sltiu` + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.sltiu`. -/
theorem stepStrong_sltiu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_sltiu trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .sltiu .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTIU))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_compare_from_binding
      trace binding i d.h_main_active (Or.inr d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_LTU :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.sltiu_input.r1_val d.sltiu_input.imm d.sltiu_input.rd d.sltiu_input.PC
      (PureSpec.execute_ITYPE_sltiu_pure d.sltiu_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU, ZiskFv.Trusted.OP_LTU] using
      d.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LTU :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      d.sltiu_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin d.r1) d.sltiu_input.r1_val
        h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sltiu d.sltiu_input d.r1 d.rd d.imm zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_m32_zero h_input_r1_row d.h_sltiu_subset h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_m32_zero, h_input_r1_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.1



/-- Strengthened `sll` step: channel-balance via constructed `OpEnvelope.sll`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.sll`. -/
theorem stepStrong_sll
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_sll trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .sll .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLL))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.sll_input.r1_val d.sll_input.r2_val d.sll_input.rd d.sll_input.PC
      (PureSpec.execute_RTYPE_sll_pure d.sll_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inl (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.sll_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_0_shift_pin_row_of_facts m _ i.val (regidx_to_fin d.r2) d.sll_input.r2_val
      h_m32_zero d.h_b_lo_t d.h_b_hi_t d.h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sll d.sll_input d.r1 d.r2 d.rd providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1

/-- Strengthened `srl` step: channel-balance via constructed `OpEnvelope.srl`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.srl`. -/
theorem stepStrong_srl
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_srl trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .srl .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRL))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i d.h_main_active (Or.inr (Or.inl d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.srl_input.r1_val d.srl_input.r2_val d.srl_input.rd d.srl_input.PC
      (PureSpec.execute_RTYPE_srl_pure d.srl_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      ((fun h => Or.inr (Or.inl h)) (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.srl_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_0_shift_pin_row_of_facts m _ i.val (regidx_to_fin d.r2) d.srl_input.r2_val
      h_m32_zero d.h_b_lo_t d.h_b_hi_t d.h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.srl d.srl_input d.r1 d.r2 d.rd providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1

/-- Strengthened `sra` step: channel-balance via constructed `OpEnvelope.sra`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.sra`. -/
theorem stepStrong_sra
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_sra trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .sra .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRA))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i d.h_main_active (Or.inr (Or.inr (Or.inl d.h_main_op)))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.sra_input.r1_val d.sra_input.r2_val d.sra_input.rd d.sra_input.PC
      (PureSpec.execute_RTYPE_sra_pure d.sra_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      ((fun h => Or.inr (Or.inr (Or.inl h))) (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.sra_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_0_shift_pin_row_of_facts m _ i.val (regidx_to_fin d.r2) d.sra_input.r2_val
      h_m32_zero d.h_b_lo_t d.h_b_hi_t d.h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sra d.sra_input d.r1 d.r2 d.rd providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1

/-- Strengthened `slli` step: channel-balance via constructed `OpEnvelope.slli`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.slli`. -/
theorem stepStrong_slli
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_slli trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .slli .. => True | _ => False)) :
    execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SLLI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
      state d.slli_input.r1_val d.slli_input.shamt d.slli_input.rd d.slli_input.PC
      (PureSpec.execute_SHIFTIOP_slli_pure d.slli_input).nextPC
      d.r1 d.rd d.shamt bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_shamt_eq := d.h_input_shamt,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inl (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.slli_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :
      d.slli_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)) := by
    rw [d.h_input_shamt]
    exact shift_imm_shift_pin_row_of_facts m _ i.val d.shamt
      d.h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.slli d.slli_input d.r1 d.rd d.shamt providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1

/-- Strengthened `srli` step: channel-balance via constructed `OpEnvelope.srli`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.srli`. -/
theorem stepStrong_srli
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_srli trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .srli .. => True | _ => False)) :
    execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRLI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i d.h_main_active (Or.inr (Or.inl d.h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
      state d.srli_input.r1_val d.srli_input.shamt d.srli_input.rd d.srli_input.PC
      (PureSpec.execute_SHIFTIOP_srli_pure d.srli_input).nextPC
      d.r1 d.rd d.shamt bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_shamt_eq := d.h_input_shamt,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      ((fun h => Or.inr (Or.inl h)) (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.srli_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :
      d.srli_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)) := by
    rw [d.h_input_shamt]
    exact shift_imm_shift_pin_row_of_facts m _ i.val d.shamt
      d.h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.srli d.srli_input d.r1 d.rd d.shamt providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1

/-- Strengthened `srai` step: channel-balance via constructed `OpEnvelope.srai`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.srai`. -/
theorem stepStrong_srai
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_srai trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .srai .. => True | _ => False)) :
    execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRAI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i d.h_main_active (Or.inr (Or.inr (Or.inl d.h_main_op)))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
      state d.srai_input.r1_val d.srai_input.shamt d.srai_input.rd d.srai_input.PC
      (PureSpec.execute_SHIFTIOP_srai_pure d.srai_input).nextPC
      d.r1 d.rd d.shamt bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_shamt_eq := d.h_input_shamt,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      ((fun h => Or.inr (Or.inr (Or.inl h))) (by rw [shift_op_pin_eq_of_match m _ i.val h_match, d.h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin d.r1) d.srai_input.r1_val
      h_m32_zero d.h_a_lo_t d.h_a_hi_t d.h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :
      d.srai_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)) := by
    rw [d.h_input_shamt]
    exact shift_imm_shift_pin_row_of_facts m _ i.val d.shamt
      d.h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  let env : OpEnvelope state m i.val :=
    OpEnvelope.srai d.srai_input d.r1 d.rd d.shamt providerTable providerRow bus
      promises pins h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_row, h_shift_pin_row⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.1



/-- Strengthened `subw` step: channel-balance via constructed `OpEnvelope.subw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.subw`. -/
theorem stepStrong_subw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_subw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .subw .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SUBW))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_w_from_binding
      trace binding i d.h_main_active (Or.inr d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SUB_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := d.h_m32
  have ha0 : (providerInput.aBytes.free_in_a_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.1
  have ha1 : (providerInput.aBytes.free_in_a_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.1
  have ha2 : (providerInput.aBytes.free_in_a_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.1
  have ha3 : (providerInput.aBytes.free_in_a_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.1
  have h_input_r1_extract :
      (Sail.BitVec.extractLsb d.subw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowA32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a32_row
        m providerInput i.val (regidx_to_fin d.r1) d.subw_input.r1_val
        ha0 ha1 ha2 ha3 h_m32_one d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have hb0 : (providerInput.bBytes.free_in_b_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.2.1
  have hb1 : (providerInput.bBytes.free_in_b_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.2.1
  have hb2 : (providerInput.bBytes.free_in_b_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.2.1
  have hb3 : (providerInput.bBytes.free_in_b_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.2.1
  have h_input_r2_extract :
      (Sail.BitVec.extractLsb d.subw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowB32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b32_row
        m providerInput i.val (regidx_to_fin d.r2) d.subw_input.r2_val
        hb0 hb1 hb2 hb3 h_m32_one d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.subw_input.r1_val d.subw_input.r2_val d.subw_input.rd d.subw_input.PC
      (PureSpec.execute_RTYPE_subw_pure d.subw_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.subw d.subw_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_extract h_input_r2_extract h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_extract, h_input_r2_extract⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.1

/-- Strengthened `addw` step: channel-balance via constructed `OpEnvelope.addw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.addw`. -/
theorem stepStrong_addw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_addw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .addw .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.ADDW))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_w_from_binding
      trace binding i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := d.h_m32
  have ha0 : (providerInput.aBytes.free_in_a_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.1
  have ha1 : (providerInput.aBytes.free_in_a_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.1
  have ha2 : (providerInput.aBytes.free_in_a_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.1
  have ha3 : (providerInput.aBytes.free_in_a_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.1
  have h_input_r1_extract :
      (Sail.BitVec.extractLsb d.addw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowA32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a32_row
        m providerInput i.val (regidx_to_fin d.r1) d.addw_input.r1_val
        ha0 ha1 ha2 ha3 h_m32_one d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  have hb0 : (providerInput.bBytes.free_in_b_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.2.1
  have hb1 : (providerInput.bBytes.free_in_b_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.2.1
  have hb2 : (providerInput.bBytes.free_in_b_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.2.1
  have hb3 : (providerInput.bBytes.free_in_b_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.2.1
  have h_input_r2_extract :
      (Sail.BitVec.extractLsb d.addw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowB32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b32_row
        m providerInput i.val (regidx_to_fin d.r2) d.addw_input.r2_val
        hb0 hb1 hb2 hb3 h_m32_one d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.addw_input.r1_val d.addw_input.r2_val d.addw_input.rd d.addw_input.PC
      (PureSpec.execute_RTYPE_addw_pure d.addw_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.addw d.addw_input d.r1 d.r2 d.rd zeroValidBinary bus pins
      providerTable providerRow h_component h_table_spec h_provider_row h_match
      h_input_r1_extract h_input_r2_extract h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := by
    show _ ∧ _
    exact ⟨h_input_r1_extract, h_input_r2_extract⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.1

/-- Strengthened `addiw` step: channel-balance via constructed `OpEnvelope.addiw`
    + `zisk_riscv_compliant_program_bus`. Dominates `StepCompliance.addiw`. -/
theorem stepStrong_addiw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_addiw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .addiw .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (d.imm, d.r1, d.rd))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_w_from_binding
      trace binding i d.h_main_active (Or.inl d.h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD_W :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := d.h_m32
  have ha0 : (providerInput.aBytes.free_in_a_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.1
  have ha1 : (providerInput.aBytes.free_in_a_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.1
  have ha2 : (providerInput.aBytes.free_in_a_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.1
  have ha3 : (providerInput.aBytes.free_in_a_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.1
  have h_input_r1_extract :
      (Sail.BitVec.extractLsb d.addiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowA32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a32_row
        m providerInput i.val (regidx_to_fin d.r1) d.addiw_input.r1_val
        ha0 ha1 ha2 ha3 h_m32_one d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.addiw_input.r1_val d.addiw_input.imm d.addiw_input.rd d.addiw_input.PC
      (PureSpec.execute_ITYPE_addiw_pure d.addiw_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.addiw d.addiw_input d.r1 d.rd d.imm zeroValidBinary bus pins
      d.h_addiw_subset providerTable providerRow h_component h_table_spec h_provider_row
      h_match h_input_r1_extract h_lane_rd promises
  have h_bridge : env.aeneasBridgeTrust := h_input_r1_extract
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.1



/-- Strengthened `add` step: channel-balance via a constructed `OpEnvelope` arm
    (`add_via_binary` on the lookup provider, `add_via_binaryadd` on the
    BinaryAdd provider) + `zisk_riscv_compliant_program_bus`. Dominates
    `StepCompliance.add`. -/
theorem stepStrong_add
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_add trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val)
      (fun env => match env with
        | .add_via_binary .. => True | .add_via_binaryadd .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (d.r2, d.r1, d.rd, rop.ADD))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨h_add_subset, h_disj⟩ :=
    exists_add_provider_row_matches_from_binding
      trace binding i d.h_main_active d.h_main_op
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.add_input.r1_val d.add_input.r2_val d.add_input.rd d.add_input.PC
      (PureSpec.execute_RTYPE_add_pure d.add_input).nextPC
      d.r1 d.r2 d.rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_r2_eq := d.h_input_r2,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  rcases h_disj with h_lookup | h_binaryadd
  · obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_lookup
    let providerInput :=
      ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
        (providerTable.environment providerRow)
    obtain ⟨h_core, h_facts⟩ :=
      ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
        h_component h_table_spec h_provider_row
    have h_static :
        ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
      ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
        h_component h_table_spec h_provider_row
    have h_emit :
        providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
          (ZiskFv.Airs.Tables.BinaryTable.OP_ADD : FGL) := by
      have h_match_op := h_match
      simp only [ZiskFv.Airs.OperationBus.matches_entry,
        ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
      have h_op_match :
          m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD, ZiskFv.Trusted.OP_ADD] using
        d.h_main_op
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_ADD (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_ADD])
        h_core h_emit
    have h_out :=
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
        providerInput h_facts
        ZiskFv.Airs.Tables.BinaryTable.OP_ADD h_core h_row_m32 h_bop
    have h_matches :
        ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
          providerInput ZiskFv.Airs.Tables.BinaryTable.OP_ADD :=
      allByteMatchesOfStaticOut64_local h_out
    have h_input_r1_row :
        d.add_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
        ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
          m providerInput i.val (regidx_to_fin d.r1) d.add_input.r1_val
          h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
    have h_input_r2_row :
        d.add_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
        ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
          m providerInput i.val (regidx_to_fin d.r2) d.add_input.r2_val
          h_matches h_m32_zero d.h_b_lo_t d.h_b_hi_t h_match d.h_input_r2
    let env : OpEnvelope state m i.val :=
      OpEnvelope.add_via_binary d.add_input d.r1 d.r2 d.rd bus pins
        providerTable providerRow h_component h_table_spec h_provider_row h_match
        h_input_r1_row h_input_r2_row h_lane_rd promises
    have h_bridge : env.aeneasBridgeTrust := by
      show _ ∧ _
      exact ⟨h_input_r1_row, h_input_r2_row⟩
    have h_mem : env.memoryTimelineConstructionEvidence := by trivial
    have h_known : Defects.NoKnownDefect env :=
      h_known_arm env trivial
    exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.1
  · obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_binaryadd
    let env : OpEnvelope state m i.val :=
      OpEnvelope.add_via_binaryadd d.add_input d.r1 d.r2 d.rd bus pins
        providerTable providerRow h_component h_table_spec h_provider_row h_match
        h_add_subset d.h_a_lo_t d.h_a_hi_t d.h_b_lo_t d.h_b_hi_t h_m32_zero
        h_lane_rd promises
    have h_bridge : env.aeneasBridgeTrust := by
      show _ ∧ _ ∧ _ ∧ _ ∧ _
      exact ⟨d.h_a_lo_t, d.h_a_hi_t, d.h_b_lo_t, d.h_b_hi_t, h_m32_zero⟩
    have h_mem : env.memoryTimelineConstructionEvidence := by trivial
    have h_known : Defects.NoKnownDefect env :=
      h_known_arm env trivial
    exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.1

/-- Strengthened `addi` step: channel-balance via a constructed `OpEnvelope` arm
    (`addi_via_binary` / `addi_via_binaryadd`) + `zisk_riscv_compliant_program_bus`.
    Dominates `StepCompliance.addi`. -/
theorem stepStrong_addi
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_addi trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val)
      (fun env => match env with
        | .addi_via_binary .. => True | .addi_via_binaryadd .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ADDI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i d.execRow
  obtain ⟨h_add_subset, h_disj⟩ :=
    exists_add_provider_row_matches_from_binding
      trace binding i d.h_main_active d.h_main_op
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state d.addi_input.r1_val d.addi_input.imm d.addi_input.rd d.addi_input.PC
      (PureSpec.execute_ITYPE_addi_pure d.addi_input).nextPC
      d.r1 d.rd d.imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := d.h_input_r1,
      input_imm_eq := d.h_input_imm,
      input_rd_eq := d.h_input_rd,
      input_pc_eq := d.h_input_pc,
      exec_len := d.h_exec_len,
      e0_mult := d.h_e0_mult,
      e1_mult := d.h_e1_mult,
      nextPC_matches := d.h_nextPC_matches,
      m0_mult := by rfl,
      m0_as := by rfl,
      m1_mult := by rfl,
      m1_as := by rfl,
      m2_mult := by rfl,
      m2_as := by rfl,
      rd_idx := d.h_rd_idx }
  have h_m32_zero : m.m32 i.val = 0 := d.h_m32
  have h_set_pc_zero : m.set_pc i.val = 0 := d.h_set_pc
  rcases h_disj with h_lookup | h_binaryadd
  · obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_lookup
    let providerInput :=
      ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
        (providerTable.environment providerRow)
    obtain ⟨h_core, h_facts⟩ :=
      ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
        h_component h_table_spec h_provider_row
    have h_static :
        ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
      ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
        h_component h_table_spec h_provider_row
    have h_emit :
        providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
          (ZiskFv.Airs.Tables.BinaryTable.OP_ADD : FGL) := by
      have h_match_op := h_match
      simp only [ZiskFv.Airs.OperationBus.matches_entry,
        ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
      have h_op_match :
          m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD, ZiskFv.Trusted.OP_ADD] using
        d.h_main_op
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_ADD (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_ADD])
        h_core h_emit
    have h_out :=
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
        providerInput h_facts
        ZiskFv.Airs.Tables.BinaryTable.OP_ADD h_core h_row_m32 h_bop
    have h_matches :
        ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
          providerInput ZiskFv.Airs.Tables.BinaryTable.OP_ADD :=
      allByteMatchesOfStaticOut64_local h_out
    have h_input_r1_row :
        d.addi_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
        ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
          m providerInput i.val (regidx_to_fin d.r1) d.addi_input.r1_val
          h_matches h_m32_zero d.h_a_lo_t d.h_a_hi_t h_match d.h_input_r1
    have h_input_imm_row :
        BitVec.signExtend 64 d.addi_input.imm
          = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
        ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
          m providerInput i.val d.addi_input.imm h_matches h_m32_zero h_match
          d.h_addi_subset
    let env : OpEnvelope state m i.val :=
      OpEnvelope.addi_via_binary d.addi_input d.r1 d.rd d.imm bus pins
        providerTable providerRow h_component h_table_spec h_provider_row h_match
        d.h_addi_subset h_input_r1_row h_input_imm_row h_lane_rd promises
    have h_bridge : env.aeneasBridgeTrust := by
      show _ ∧ _
      exact ⟨h_input_r1_row, h_input_imm_row⟩
    have h_mem : env.memoryTimelineConstructionEvidence := by trivial
    have h_known : Defects.NoKnownDefect env :=
      h_known_arm env trivial
    exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.1
  · obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_binaryadd
    let env : OpEnvelope state m i.val :=
      OpEnvelope.addi_via_binaryadd d.addi_input d.r1 d.rd d.imm bus pins
        providerTable providerRow h_component h_table_spec h_provider_row h_match
        h_add_subset d.h_addi_subset d.h_a_lo_t d.h_a_hi_t h_m32_zero h_set_pc_zero
        h_lane_rd promises
    have h_bridge : env.aeneasBridgeTrust := by
      show _ ∧ _ ∧ _ ∧ _
      exact ⟨d.h_a_lo_t, d.h_a_hi_t, h_m32_zero, h_set_pc_zero⟩
    have h_mem : env.memoryTimelineConstructionEvidence := by trivial
    have h_known : Defects.NoKnownDefect env :=
      h_known_arm env trivial
    exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.1


/-! ## Strengthened control-flow + U-type arms (branches, JAL/JALR, LUI/AUIPC)

These arms reach the same channel-balance conclusion as the 22 above, but via a
DIRECT lift rather than an explicit `OpEnvelope`/global-theorem invocation: the
matching `construction_<op>_sound` already proves the `bus_effect`-form per-step
conclusion over the real trace row, and `state_effect_via_channels` is `@[reducible]`-
defeq to `bus_effect.2`.  Hence `rw [state_effect_via_channels_eq_bus_effect_2]`
followed by the construction theorem yields the EXACT channel-balance proposition
the OLD global theorem produces for these arms (for branches this IS the
`Equivalence.<B>.equiv_<B>` the global dispatcher `zisk_riscv_compliant_program_bus_branch`
itself dispatches to; for LUI/AUIPC/JAL/JALR it is the channel-balance lift of the
same concrete `eRdLui` rd-write entry the `bus_effect`-form arm uses).

Non-vacuity: `execRow` (and `exec_row` for branches) remains a genuine ∀-binder
inside each `RowData_<op>`; no `False.elim`, no contradictory binder; the
conclusion is over the real `mainOfTable` row.  These are strictly stronger than
the corresponding `bus_effect`-form arms (channel-balance form, same data). -/

/-- Strengthened `beq` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.beq` from the trace's `RowData_beq` (the same
    `BranchInstrOperands` + `BranchPromises` `construction_beq_sound` builds) and
    invoke `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_branch`
    conjunct.  `aeneasBridgeTrust` is flat decode pins carried as `RowData_beq`
    residuals; `NoKnownDefect` comes from the threaded `h_known_arm`. -/
theorem stepStrong_beq
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_beq trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .beq .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BEQ)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.beq_input.imm d.beq_input.r1_val d.beq_input.r2_val d.beq_input.PC
      ops.misa_val
      (PureSpec.execute_BEQ_pure d.beq_input).nextPC
      (PureSpec.execute_BEQ_pure d.beq_input).throws
      (PureSpec.execute_BEQ_pure d.beq_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.beq d.beq_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bne` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bne
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_bne trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .bne .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BNE)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.bne_input.imm d.bne_input.r1_val d.bne_input.r2_val d.bne_input.PC
      ops.misa_val
      (PureSpec.execute_BNE_pure d.bne_input).nextPC
      (PureSpec.execute_BNE_pure d.bne_input).throws
      (PureSpec.execute_BNE_pure d.bne_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bne d.bne_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset1⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `blt` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_blt
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_blt trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .blt .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLT)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.blt_input.imm d.blt_input.r1_val d.blt_input.r2_val d.blt_input.PC
      ops.misa_val
      (PureSpec.execute_BLT_pure d.blt_input).nextPC
      (PureSpec.execute_BLT_pure d.blt_input).throws
      (PureSpec.execute_BLT_pure d.blt_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.blt d.blt_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bge` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bge
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_bge trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .bge .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGE)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.bge_input.imm d.bge_input.r1_val d.bge_input.r2_val d.bge_input.PC
      ops.misa_val
      (PureSpec.execute_BGE_pure d.bge_input).nextPC
      (PureSpec.execute_BGE_pure d.bge_input).throws
      (PureSpec.execute_BGE_pure d.bge_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bge d.bge_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset1⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bltu` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bltu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_bltu trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .bltu .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLTU)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.bltu_input.imm d.bltu_input.r1_val d.bltu_input.r2_val d.bltu_input.PC
      ops.misa_val
      (PureSpec.execute_BLTU_pure d.bltu_input).nextPC
      (PureSpec.execute_BLTU_pure d.bltu_input).throws
      (PureSpec.execute_BLTU_pure d.bltu_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bltu d.bltu_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bgeu` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bgeu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_bgeu trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .bgeu .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGEU)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.bgeu_input.imm d.bgeu_input.r1_val d.bgeu_input.r2_val d.bgeu_input.PC
      ops.misa_val
      (PureSpec.execute_BGEU_pure d.bgeu_input).nextPC
      (PureSpec.execute_BGEU_pure d.bgeu_input).throws
      (PureSpec.execute_BGEU_pure d.bgeu_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bgeu d.bgeu_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset1⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `lui` step (channel-balance form). -/
theorem stepStrong_lui
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_lui trace binding i) :
    execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.LUI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_lui_sound trace binding i d.lui_input d.imm d.rd d.h_main_op
    d.h_main_active d.h_m32 d.h_set_pc d.h_store_pc d.h_input_imm d.h_input_rd
    d.h_input_pc d.h_imm_lo_nat d.h_imm_hi_nat d.execRow d.h_exec_len d.h_e0_mult
    d.h_e1_mult d.h_nextPC_matches d.h_rd_idx

/-- Strengthened `auipc` step (channel-balance form). -/
theorem stepStrong_auipc
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_auipc trace binding i) :
    execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.AUIPC)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_auipc_sound trace binding i d.auipc_input d.imm d.rd d.h_main_op
    d.h_main_active d.h_m32 d.h_set_pc d.h_store_pc d.h_input_imm d.h_input_rd
    d.h_input_pc d.h_offset_bridge d.h_pc_bridge d.execRow d.h_exec_len d.h_e0_mult
    d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.h_no_wrap d.h_pc_offset_lt_2_32

/-- Strengthened `jal` step (channel-balance form). -/
theorem stepStrong_jal
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_jal trace binding i) :
    execute_instruction (instruction.JAL (d.imm, d.rd)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_jal_sound trace binding i d.jal_input d.imm d.rd d.misa_val
    d.nextPC_val d.h_main_op d.h_main_active d.h_m32 d.h_set_pc d.h_store_pc d.h_jmp2
    d.h_pc_bridge d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
    d.h_input_rd d.h_input_pc d.h_input_misa d.h_misa_c d.h_success d.h_nextPC_option
    d.h_rd_idx d.h_input_imm d.h_not_throws d.h_pc_bound d.h_pc_offset_lt_2_32

/-- Strengthened `jalr` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.jalr` from the trace's `RowData_jalr` (mirroring
    `construction_jalr_sound`'s internal `next_pc` / `e_rd` / `store_pc_mem` /
    `pins` / `h_jalr_subset` / `promises` derivations) and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_remaining`
    conjunct.  The threaded `h_known_arm : EnvNoKnownDefectFor …` discharges
    `NoKnownDefect`.  JALR's `aeneasBridgeTrust` is flat decode pins already in
    `RowData_jalr` (no `MainRowProvenance`). -/
theorem stepStrong_jalr
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_jalr trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .jalr .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.JALR (d.imm, d.rs1, d.rd))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let e_rd := eRdLui trace binding i
  -- (a) Main per-row Spec ⇒ the JALR Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨_h_c0, _h_b0, _h_c1, _h_b1, _h_set_flag, _h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  -- (a) the handshake is definitional: pick `next_pc` as its RHS.
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_jalr_subset :
      ZiskFv.Airs.Main.flag_boolean m i.val
      ∧ ZiskFv.Airs.Main.is_external_op_boolean m i.val
      ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m i.val
      ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_handshake⟩
  -- (a) `StorePcMemoryWitness` from the real Clean Main `c` message row.
  have h_row_core :
      (mainRowWithRomLui trace binding i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace binding i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_AND :=
    ⟨d.h_main_active, d.h_main_op⟩
  let promises : ZiskFv.EquivCore.Promises.JumpPromises
      state d.jalr_input.PC d.jalr_input.rd d.misa_val
      (PureSpec.execute_JALR_pure d.jalr_input).success
      (PureSpec.execute_JALR_pure d.jalr_input).nextPC
      d.rd d.execRow e_rd d.nextPC_val :=
    { input_rd_eq := d.h_input_rd
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      rd_mult := by rfl
      rd_as := by rfl
      success := d.h_success
      nextPC_option := d.h_nextPC_option
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.jalr d.jalr_input d.imm d.rs1 d.rd d.misa_val d.mseccfg d.execRow e_rd
      d.nextPC_val next_pc store_pc_mem pins d.h_flag d.h_m32 d.h_set_pc d.h_store_pc
      h_jalr_subset promises d.h_input_imm d.h_input_rs1 d.h_cur_privilege d.h_mseccfg
      d.h_link_bridge d.h_pc_bound d.h_pc_offset_lt_2_32
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_flag, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_link_bridge⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-! ## Strengthened store arms (SB/SH/SW/SD, channel-balance form)

Same direct-lift route as the control-flow arms: `construction_<op>_sound` proves
the `bus_effect`-form per-step conclusion (3-entry memory list `[e0, e1, e2]` over
the real `busSt` row), and `state_effect_via_channels` is `@[reducible]`-defeq to
`bus_effect.2`.  The previously-reported whnf BLOWUP was specific to the
`OpEnvelope`/`zisk_riscv_compliant_program_bus` route (the `Eq.mpr` cast over the
`MainRowWithRom` motive); this route never constructs that envelope, so the kernel
never whnf's the cast.  Non-vacuous: `execRow` is a genuine ∀-binder; the memory
list is the real 3-entry store emission. -/

/-- Strengthened `sb` step (channel-balance form). -/
theorem stepStrong_sb
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_sb trace binding i) :
    execute_instruction (instruction.STORE
        (d.sb_input.imm, regidx.Regidx d.sb_input.r2, regidx.Regidx d.sb_input.r1, 1))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [ (busSt trace binding i d.execRow).e0
           , (busSt trace binding i d.execRow).e1
           , (busSt trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_sb_sound trace binding i d.sb_input d.regs d.h_main_active d.h_main_op
    d.h_store_pc d.h_main_ind_width d.h_opcode_assumptions d.h_addr2 d.h_b0_value d.h_b1_value
    d.execRow d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
    d.h_m1 d.h_m2 d.h_m3 d.h_m4 d.h_m5 d.h_m6 d.h_m7

/-- Strengthened `sh` step (channel-balance form). -/
theorem stepStrong_sh
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_sh trace binding i) :
    execute_instruction (instruction.STORE
        (d.sh_input.imm, regidx.Regidx d.sh_input.r2, regidx.Regidx d.sh_input.r1, 2))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [ (busSt trace binding i d.execRow).e0
           , (busSt trace binding i d.execRow).e1
           , (busSt trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_sh_sound trace binding i d.sh_input d.regs d.h_main_active d.h_main_op
    d.h_store_pc d.h_main_ind_width d.h_opcode_assumptions d.h_addr2 d.h_b0_value d.h_b1_value
    d.execRow d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
    d.h_m2 d.h_m3 d.h_m4 d.h_m5 d.h_m6 d.h_m7

/-- Strengthened `sw` step (channel-balance form). -/
theorem stepStrong_sw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_sw trace binding i) :
    execute_instruction (instruction.STORE
        (d.sw_input.imm, regidx.Regidx d.sw_input.r2, regidx.Regidx d.sw_input.r1, 4))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [ (busSt trace binding i d.execRow).e0
           , (busSt trace binding i d.execRow).e1
           , (busSt trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_sw_sound trace binding i d.sw_input d.regs d.h_main_active d.h_main_op
    d.h_store_pc d.h_main_ind_width d.h_opcode_assumptions d.h_addr2 d.h_b0_value d.h_b1_value
    d.execRow d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
    d.h_m4 d.h_m5 d.h_m6 d.h_m7

/-- Strengthened `sd` step (channel-balance form). -/
theorem stepStrong_sd
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_sd trace binding i) :
    execute_instruction (instruction.STORE
        (d.sd_input.imm, regidx.Regidx d.sd_input.r2, regidx.Regidx d.sd_input.r1, 8))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [ (busSt trace binding i d.execRow).e0
           , (busSt trace binding i d.execRow).e1
           , (busSt trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_sd_sound trace binding i d.sd_input d.regs d.h_main_active d.h_main_op
    d.h_store_pc d.h_opcode_assumptions d.h_addr2 d.h_b0_value d.h_b1_value
    d.execRow d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches

/-! ## Strengthened load arms (LB/LH/LW/LD/LBU/LHU/LWU, channel-balance form)

Same direct-lift route.  The hint's obstacle — the `OpEnvelope` load arm needing
`Var`/`Environment`-level interaction-evaluation provenance (`h_mainEval`/
`h_providerEval`/`h_msg`) that the witness-based load constructions bypass via
`matches_memory_entry_refl` — was specific to the `OpEnvelope`/global-theorem
route.  The direct-lift route never builds an `OpEnvelope`; it lifts
`construction_<op>_sound`'s `bus_effect`-form conclusion (3-entry memory list
`[e0, e1, e2]` over `busLd`) to the channel-balance form via the `rfl`-bridge
`state_effect_via_channels_eq_bus_effect_2`, so the eval-provenance is never
needed.  The #76 residuals (`h_memory_timeline`, `h_mem_match`, …) and the
signed-load `h_static`/`h_match` BinaryExtension provider linkage are carried
verbatim as `RowData_<op>` binders (they live inside each construction, NOT in any
`OpEnvelope` field).  Non-vacuous: `execRow` is a genuine ∀-binder; the memory
list is the real 3-entry `busLd` emission; the Mem-AIR / BinaryExtension provider
records are real `Valid_Mem`/`Valid_BinaryExtension` rows. -/

/-- Strengthened `ld` step (channel-balance form). -/
theorem stepStrong_ld
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_ld trace binding i) :
    execute_instruction (instruction.LOAD
        (d.ld_input.imm, regidx.Regidx d.ld_input.r1, regidx.Regidx d.ld_input.rd, false, 8))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [ (busLd trace binding i d.execRow).e0
           , (busLd trace binding i d.execRow).e1
           , (busLd trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_ld_sound trace binding i d.ld_input d.regs d.mem d.r_mem
    d.h_main_active d.h_main_op d.h_store_pc d.h_opcode_assumptions d.h_addr1
    d.h_addr2_zero_iff d.h_addr2_idx d.execRow d.h_risc_v_assumptions d.h_exec_len
    d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_memory_timeline d.h_mem_match
    d.h_mem_sel d.h_mem_wr

/-- Strengthened `lbu` step (channel-balance form). -/
theorem stepStrong_lbu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_lbu trace binding i) :
    execute_instruction (instruction.LOAD
        (d.lbu_input.imm, regidx.Regidx d.lbu_input.r1, regidx.Regidx d.lbu_input.rd, true, 1))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [ (busLd trace binding i d.execRow).e0
           , (busLd trace binding i d.execRow).e1
           , (busLd trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_lbu_sound trace binding i d.lbu_input d.regs d.mem d.r_mem d.execRow
    d.align d.h_main_active d.h_main_op d.h_store_pc d.h_width d.h_opcode_assumptions
    d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.h_risc_v_assumptions d.h_exec_len
    d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_memory_timeline d.h_mem_match
    d.h_mem_sel d.h_mem_wr

/-- Strengthened `lhu` step (channel-balance form). -/
theorem stepStrong_lhu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_lhu trace binding i) :
    execute_instruction (instruction.LOAD
        (d.lhu_input.imm, regidx.Regidx d.lhu_input.r1, regidx.Regidx d.lhu_input.rd, true, 2))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [ (busLd trace binding i d.execRow).e0
           , (busLd trace binding i d.execRow).e1
           , (busLd trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_lhu_sound trace binding i d.lhu_input d.regs d.mem d.r_mem d.execRow
    d.align d.h_main_active d.h_main_op d.h_store_pc d.h_width d.h_opcode_assumptions
    d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.h_risc_v_assumptions d.h_exec_len
    d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_memory_timeline d.h_mem_match
    d.h_mem_sel d.h_mem_wr

/-- Strengthened `lwu` step (channel-balance form). -/
theorem stepStrong_lwu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_lwu trace binding i) :
    execute_instruction (instruction.LOAD
        (d.lwu_input.imm, regidx.Regidx d.lwu_input.r1, regidx.Regidx d.lwu_input.rd, true, 4))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [ (busLd trace binding i d.execRow).e0
           , (busLd trace binding i d.execRow).e1
           , (busLd trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_lwu_sound trace binding i d.lwu_input d.regs d.mem d.r_mem d.execRow
    d.align d.h_main_active d.h_main_op d.h_store_pc d.h_width d.h_opcode_assumptions
    d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.h_risc_v_assumptions d.h_exec_len
    d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_memory_timeline d.h_mem_match
    d.h_mem_sel d.h_mem_wr

/-- Strengthened `lb` step (channel-balance form). -/
theorem stepStrong_lb
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_lb trace binding i) :
    execute_instruction (instruction.LOAD
        (d.lb_input.imm, regidx.Regidx d.lb_input.r1, regidx.Regidx d.lb_input.rd, false, 1))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [ (busLd trace binding i d.execRow).e0
           , (busLd trace binding i d.execRow).e1
           , (busLd trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_lb_sound trace binding i d.lb_input d.regs d.mem d.r_mem d.v d.r_binary
    d.offset d.env d.h_static d.h_match d.h_main_active d.h_main_op d.h_store_pc
    d.h_opcode_assumptions d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.execRow
    d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
    d.h_memory_timeline d.h_mem_match d.h_mem_sel d.h_mem_wr

/-- Strengthened `lh` step (channel-balance form). -/
theorem stepStrong_lh
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_lh trace binding i) :
    execute_instruction (instruction.LOAD
        (d.lh_input.imm, regidx.Regidx d.lh_input.r1, regidx.Regidx d.lh_input.rd, false, 2))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [ (busLd trace binding i d.execRow).e0
           , (busLd trace binding i d.execRow).e1
           , (busLd trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_lh_sound trace binding i d.lh_input d.regs d.mem d.r_mem d.v d.r_binary
    d.offset d.env d.h_static d.h_match d.h_main_active d.h_main_op d.h_store_pc
    d.h_opcode_assumptions d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.execRow
    d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
    d.h_memory_timeline d.h_mem_match d.h_mem_sel d.h_mem_wr

/-- Strengthened `lw` step (channel-balance form). -/
theorem stepStrong_lw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_lw trace binding i) :
    execute_instruction (instruction.LOAD
        (d.lw_input.imm, regidx.Regidx d.lw_input.r1, regidx.Regidx d.lw_input.rd, false, 4))
        (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [ (busLd trace binding i d.execRow).e0
           , (busLd trace binding i d.execRow).e1
           , (busLd trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_lw_sound trace binding i d.lw_input d.regs d.mem d.r_mem d.v d.r_binary
    d.offset d.env d.h_static d.h_match d.h_main_active d.h_main_op d.h_store_pc
    d.h_opcode_assumptions d.h_addr1 d.h_addr2_zero_iff d.h_addr2_idx d.execRow
    d.h_risc_v_assumptions d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches
    d.h_memory_timeline d.h_mem_match d.h_mem_sel d.h_mem_wr

/-! ## Strengthened M-ext-unsigned arms (MULW/MULHU/DIVU/DIVUW/REMU/REMUW)

Same DIRECT-LIFT route as the control-flow / store / load arms — NOT the
`OpEnvelope`/`zisk_riscv_compliant_program_bus` route.  Each
`construction_<op>_sound` already proves the `bus_effect`-form per-step
conclusion (2-entry exec row + `[e0, e1, e2]` over the real `busSub` row) using
the FAITHFUL loose Arith carry bound (`<983041`).  `state_effect_via_channels`
is `@[reducible]`-defeq to `bus_effect.2`, so
`rw [state_effect_via_channels_eq_bus_effect_2]` + the construction theorem
yields the channel-balance proposition WITHOUT ever invoking the canonical
`equiv_<op>` (whose tight `<131072` carry bound is row-locally suspect /
unconstructible for real 4×4 carries).  This lift therefore NEVER touches that
tight bound: it is the channel-balance lift of the same loose-bound construction
already exported in `bus_effect` form by `RowConstructionData` / `StepCompliance`.

Non-vacuity: `execRow` remains a genuine `∀`-binder inside each
`RowData_<op>`; no `False.elim`, no contradictory binder; the conclusion is over
the real `busSub` row.  These are strictly stronger than the corresponding
`bus_effect`-form M-ext arms (channel-balance form, same data). -/

/-- Strengthened `mulw` step (channel-balance form). -/
theorem stepStrong_mulw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_mulw trace binding i) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.MULW (d.r2, d.r1, d.rd))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_mulw_sound trace binding i d.mulw_input d.r1 d.r2 d.rd d.h_main_op
    d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
    d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.h_a23
    d.h_b23 d.h_sext_choice d.h_rs1_value d.h_rs2_value

/-- Strengthened `mulhu` step (channel-balance form). -/
theorem stepStrong_mulhu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_mulhu trace binding i) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Unsigned
             signed_rs2 := .Unsigned }))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_mulhu_sound trace binding i d.mulhu_input d.r1 d.r2 d.rd d.h_main_op
    d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
    d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.bounds
    d.h_rs1_value d.h_rs2_value

/-- Strengthened `divu` step (channel-balance form). -/
theorem stepStrong_divu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_divu trace binding i) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_divu_sound trace binding i d.divu_input d.r1 d.r2 d.rd d.h_main_op
    d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
    d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.bounds
    d.remainder_bound d.h_rs1_value d.h_rs2_value

/-- Strengthened `divuw` step (channel-balance form). -/
theorem stepStrong_divuw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_divuw trace binding i) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_divuw_sound trace binding i d.divuw_input d.r1 d.r2 d.rd d.h_main_op
    d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
    d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.bounds
    d.remainder_bound d.h_b23 d.h_c23 d.h_sext_choice d.h_rs1_value d.h_rs2_value

/-- Strengthened `remu` step (channel-balance form). -/
theorem stepStrong_remu
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_remu trace binding i) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_remu_sound trace binding i d.remu_input d.r1 d.r2 d.rd d.h_main_op
    d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
    d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.bounds
    d.remainder_bound d.h_rs1_value d.h_rs2_value

/-- Strengthened `remuw` step (channel-balance form). -/
theorem stepStrong_remuw
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : RowData_remuw trace binding i) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [ (busSub trace binding i d.execRow).e0
           , (busSub trace binding i d.execRow).e1
           , (busSub trace binding i d.execRow).e2 ]⟩ (binding.stateAt i) := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact construction_remuw_sound trace binding i d.remuw_input d.r1 d.r2 d.rd d.h_main_op
    d.h_main_active d.h_store_pc d.h_input_r1 d.h_input_r2 d.h_input_pc d.h_input_rd
    d.execRow d.h_exec_len d.h_e0_mult d.h_e1_mult d.h_nextPC_matches d.h_rd_idx d.bounds
    d.remainder_bound d.h_b23 d.h_c23 d.h_sext_choice d.h_rs1_value d.h_rs2_value

/-! ## Strong sum + dispatcher + top-level strengthened export -/

/-- A per-row classification restricted to the arms strengthened to the
    channel-balance / env-constructed form.  Covers all 49 non-defect-gated
    constructible arms (the 22 op-bus ALU arms via the env-constructed route; the
    27 control-flow / U-type / store / load / M-ext-unsigned arms via the
    direct-lift route).  The remaining 6 arms (signed M-ext minus the unsigned
    overlap, plus FENCE) are defect/gap-gated — they have NO sound construction
    and therefore NO arm here. -/
inductive StrongRowConstructionData
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) where
  | sub (d : RowData_sub trace binding i) : StrongRowConstructionData trace binding i
  | and (d : RowData_and trace binding i) : StrongRowConstructionData trace binding i
  | or (d : RowData_or trace binding i) : StrongRowConstructionData trace binding i
  | xor (d : RowData_xor trace binding i) : StrongRowConstructionData trace binding i
  | slt (d : RowData_slt trace binding i) : StrongRowConstructionData trace binding i
  | sltu (d : RowData_sltu trace binding i) : StrongRowConstructionData trace binding i
  | andi (d : RowData_andi trace binding i) : StrongRowConstructionData trace binding i
  | ori (d : RowData_ori trace binding i) : StrongRowConstructionData trace binding i
  | xori (d : RowData_xori trace binding i) : StrongRowConstructionData trace binding i
  | slti (d : RowData_slti trace binding i) : StrongRowConstructionData trace binding i
  | sltiu (d : RowData_sltiu trace binding i) : StrongRowConstructionData trace binding i
  | sll (d : RowData_sll trace binding i) : StrongRowConstructionData trace binding i
  | srl (d : RowData_srl trace binding i) : StrongRowConstructionData trace binding i
  | sra (d : RowData_sra trace binding i) : StrongRowConstructionData trace binding i
  | slli (d : RowData_slli trace binding i) : StrongRowConstructionData trace binding i
  | srli (d : RowData_srli trace binding i) : StrongRowConstructionData trace binding i
  | srai (d : RowData_srai trace binding i) : StrongRowConstructionData trace binding i
  | add (d : RowData_add trace binding i) : StrongRowConstructionData trace binding i
  | addi (d : RowData_addi trace binding i) : StrongRowConstructionData trace binding i
  | subw (d : RowData_subw trace binding i) : StrongRowConstructionData trace binding i
  | addw (d : RowData_addw trace binding i) : StrongRowConstructionData trace binding i
  | addiw (d : RowData_addiw trace binding i) : StrongRowConstructionData trace binding i
  | mulw (d : RowData_mulw trace binding i) : StrongRowConstructionData trace binding i
  | mulhu (d : RowData_mulhu trace binding i) : StrongRowConstructionData trace binding i
  | divu (d : RowData_divu trace binding i) : StrongRowConstructionData trace binding i
  | divuw (d : RowData_divuw trace binding i) : StrongRowConstructionData trace binding i
  | remu (d : RowData_remu trace binding i) : StrongRowConstructionData trace binding i
  | remuw (d : RowData_remuw trace binding i) : StrongRowConstructionData trace binding i
  | beq (d : RowData_beq trace binding i) : StrongRowConstructionData trace binding i
  | bne (d : RowData_bne trace binding i) : StrongRowConstructionData trace binding i
  | blt (d : RowData_blt trace binding i) : StrongRowConstructionData trace binding i
  | bge (d : RowData_bge trace binding i) : StrongRowConstructionData trace binding i
  | bltu (d : RowData_bltu trace binding i) : StrongRowConstructionData trace binding i
  | bgeu (d : RowData_bgeu trace binding i) : StrongRowConstructionData trace binding i
  | lui (d : RowData_lui trace binding i) : StrongRowConstructionData trace binding i
  | auipc (d : RowData_auipc trace binding i) : StrongRowConstructionData trace binding i
  | jal (d : RowData_jal trace binding i) : StrongRowConstructionData trace binding i
  | jalr (d : RowData_jalr trace binding i) : StrongRowConstructionData trace binding i
  | sb (d : RowData_sb trace binding i) : StrongRowConstructionData trace binding i
  | sh (d : RowData_sh trace binding i) : StrongRowConstructionData trace binding i
  | sw (d : RowData_sw trace binding i) : StrongRowConstructionData trace binding i
  | sd (d : RowData_sd trace binding i) : StrongRowConstructionData trace binding i
  | ld (d : RowData_ld trace binding i) : StrongRowConstructionData trace binding i
  | lbu (d : RowData_lbu trace binding i) : StrongRowConstructionData trace binding i
  | lhu (d : RowData_lhu trace binding i) : StrongRowConstructionData trace binding i
  | lwu (d : RowData_lwu trace binding i) : StrongRowConstructionData trace binding i
  | lb (d : RowData_lb trace binding i) : StrongRowConstructionData trace binding i
  | lh (d : RowData_lh trace binding i) : StrongRowConstructionData trace binding i
  | lw (d : RowData_lw trace binding i) : StrongRowConstructionData trace binding i

/-- Per-row defect-exclusion obligation supplied to (and threaded into) the
    strengthened trace-level export.  For each OpEnvelope-route arm it is the
    `EnvNoKnownDefectFor` fact restricted to that arm's `OpEnvelope` constructor;
    for the direct-lift arms (which never invoke `zisk_riscv_compliant_program_bus`)
    it is `True`.  See `EnvNoKnownDefectFor` for the non-vacuity / generalization
    rationale. -/
def StepNoKnownDefect
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    StrongRowConstructionData trace binding i → Prop
  | .sub _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .sub .. => True | _ => False)
  | .and _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .and .. => True | _ => False)
  | .or _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .or .. => True | _ => False)
  | .xor _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .xor .. => True | _ => False)
  | .slt _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .slt .. => True | _ => False)
  | .sltu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .sltu .. => True | _ => False)
  | .andi _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .andi .. => True | _ => False)
  | .ori _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .ori .. => True | _ => False)
  | .xori _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .xori .. => True | _ => False)
  | .slti _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .slti .. => True | _ => False)
  | .sltiu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .sltiu .. => True | _ => False)
  | .sll _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .sll .. => True | _ => False)
  | .srl _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .srl .. => True | _ => False)
  | .sra _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .sra .. => True | _ => False)
  | .slli _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .slli .. => True | _ => False)
  | .srli _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .srli .. => True | _ => False)
  | .srai _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .srai .. => True | _ => False)
  | .add _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val)
      (fun env => match env with | .add_via_binary .. => True | .add_via_binaryadd .. => True | _ => False)
  | .addi _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val)
      (fun env => match env with | .addi_via_binary .. => True | .addi_via_binaryadd .. => True | _ => False)
  | .subw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .subw .. => True | _ => False)
  | .addw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .addw .. => True | _ => False)
  | .addiw _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .addiw .. => True | _ => False)
  | .jalr _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .jalr .. => True | _ => False)
  | .beq _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .beq .. => True | _ => False)
  | .bne _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .bne .. => True | _ => False)
  | .blt _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .blt .. => True | _ => False)
  | .bge _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .bge .. => True | _ => False)
  | .bltu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .bltu .. => True | _ => False)
  | .bgeu _ => EnvNoKnownDefectFor
      (state := binding.stateAt i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      (r := i.val) (fun env => match env with | .bgeu .. => True | _ => False)
  | _ => True

/-- The strengthened per-step conclusion: the channel-balance
    (`state_effect_via_channels`) form — the OLD global theorem's per-arm
    conclusion — keyed on the row archetype. -/
def StepComplianceStrong
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    StrongRowConstructionData trace binding i → Prop
  | .sub d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SUB))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .and d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.AND))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .or d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.OR))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .xor d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.XOR))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .slt d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLT))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sltu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLTU))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .andi d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ANDI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .ori d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ORI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .xori d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.XORI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .slti d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sltiu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.SLTIU))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sll d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SLL)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .srl d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRL)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sra d =>
      execute_instruction (instruction.RTYPE (d.r2, d.r1, d.rd, rop.SRA)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .slli d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SLLI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .srli d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRLI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .srai d =>
      execute_instruction (instruction.SHIFTIOP (d.shamt, d.r1, d.rd, sop.SRAI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .add d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (d.r2, d.r1, d.rd, rop.ADD))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .addi d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (d.imm, d.r1, d.rd, iop.ADDI))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .subw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.SUBW))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .addw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPEW (d.r2, d.r1, d.rd, ropw.ADDW))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .addiw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ADDIW (d.imm, d.r1, d.rd))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .mulw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.MULW (d.r2, d.r1, d.rd))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .mulhu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.r2, d.r1, d.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Unsigned
             signed_rs2 := .Unsigned }))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .divu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .divuw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .remu d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .remuw d =>
      (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (d.r2, d.r1, d.rd, true))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace binding i d.execRow).exec_row,
           [(busSub trace binding i d.execRow).e0, (busSub trace binding i d.execRow).e1,
            (busSub trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .beq d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BEQ)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .bne d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BNE)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .blt d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLT)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .bge d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGE)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .bltu d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLTU)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .bgeu d =>
      execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGEU)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding.stateAt i)
  | .lui d =>
      execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.LUI)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i)
  | .auipc d =>
      execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.AUIPC)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i)
  | .jal d =>
      execute_instruction (instruction.JAL (d.imm, d.rd)) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i)
  | .jalr d =>
      (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (d.imm, d.rs1, d.rd))) (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding.stateAt i)
  | .sb d =>
      execute_instruction (instruction.STORE
          (d.sb_input.imm, regidx.Regidx d.sb_input.r2, regidx.Regidx d.sb_input.r1, 1))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [(busSt trace binding i d.execRow).e0, (busSt trace binding i d.execRow).e1,
            (busSt trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sh d =>
      execute_instruction (instruction.STORE
          (d.sh_input.imm, regidx.Regidx d.sh_input.r2, regidx.Regidx d.sh_input.r1, 2))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [(busSt trace binding i d.execRow).e0, (busSt trace binding i d.execRow).e1,
            (busSt trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sw d =>
      execute_instruction (instruction.STORE
          (d.sw_input.imm, regidx.Regidx d.sw_input.r2, regidx.Regidx d.sw_input.r1, 4))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [(busSt trace binding i d.execRow).e0, (busSt trace binding i d.execRow).e1,
            (busSt trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .sd d =>
      execute_instruction (instruction.STORE
          (d.sd_input.imm, regidx.Regidx d.sd_input.r2, regidx.Regidx d.sd_input.r1, 8))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [(busSt trace binding i d.execRow).e0, (busSt trace binding i d.execRow).e1,
            (busSt trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .ld d =>
      execute_instruction (instruction.LOAD
          (d.ld_input.imm, regidx.Regidx d.ld_input.r1, regidx.Regidx d.ld_input.rd, false, 8))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lbu d =>
      execute_instruction (instruction.LOAD
          (d.lbu_input.imm, regidx.Regidx d.lbu_input.r1, regidx.Regidx d.lbu_input.rd, true, 1))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lhu d =>
      execute_instruction (instruction.LOAD
          (d.lhu_input.imm, regidx.Regidx d.lhu_input.r1, regidx.Regidx d.lhu_input.rd, true, 2))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lwu d =>
      execute_instruction (instruction.LOAD
          (d.lwu_input.imm, regidx.Regidx d.lwu_input.r1, regidx.Regidx d.lwu_input.rd, true, 4))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lb d =>
      execute_instruction (instruction.LOAD
          (d.lb_input.imm, regidx.Regidx d.lb_input.r1, regidx.Regidx d.lb_input.rd, false, 1))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lh d =>
      execute_instruction (instruction.LOAD
          (d.lh_input.imm, regidx.Regidx d.lh_input.r1, regidx.Regidx d.lh_input.rd, false, 2))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)
  | .lw d =>
      execute_instruction (instruction.LOAD
          (d.lw_input.imm, regidx.Regidx d.lw_input.r1, regidx.Regidx d.lw_input.rd, false, 4))
          (binding.stateAt i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace binding i d.execRow).exec_row,
           [(busLd trace binding i d.execRow).e0, (busLd trace binding i d.execRow).e1,
            (busLd trace binding i d.execRow).e2]⟩ (binding.stateAt i)

/-- Per-row dispatch to the matching strengthened step theorem.

    The `h_known` parameter carries the per-row defect-exclusion obligation
    (`StepNoKnownDefect`).  For the 22 OpEnvelope-route arms it is the
    `EnvNoKnownDefectFor` fact for that arm's constructor; the dispatcher hands it
    straight to the corresponding `stepStrong_<op>`, which feeds it to
    `zisk_riscv_compliant_program_bus`.  For the direct-lift arms (which never call
    the old theorem) the obligation is `True` and is ignored. -/
theorem stepComplianceStrong_of_rowData
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (d : StrongRowConstructionData trace binding i)
    (h_known : StepNoKnownDefect trace binding i d) :
    StepComplianceStrong trace binding i d := by
  cases d with
  | sub d => exact stepStrong_sub trace binding i d h_known
  | and d => exact stepStrong_and trace binding i d h_known
  | or d => exact stepStrong_or trace binding i d h_known
  | xor d => exact stepStrong_xor trace binding i d h_known
  | slt d => exact stepStrong_slt trace binding i d h_known
  | sltu d => exact stepStrong_sltu trace binding i d h_known
  | andi d => exact stepStrong_andi trace binding i d h_known
  | ori d => exact stepStrong_ori trace binding i d h_known
  | xori d => exact stepStrong_xori trace binding i d h_known
  | slti d => exact stepStrong_slti trace binding i d h_known
  | sltiu d => exact stepStrong_sltiu trace binding i d h_known
  | sll d => exact stepStrong_sll trace binding i d h_known
  | srl d => exact stepStrong_srl trace binding i d h_known
  | sra d => exact stepStrong_sra trace binding i d h_known
  | slli d => exact stepStrong_slli trace binding i d h_known
  | srli d => exact stepStrong_srli trace binding i d h_known
  | srai d => exact stepStrong_srai trace binding i d h_known
  | add d => exact stepStrong_add trace binding i d h_known
  | addi d => exact stepStrong_addi trace binding i d h_known
  | subw d => exact stepStrong_subw trace binding i d h_known
  | addw d => exact stepStrong_addw trace binding i d h_known
  | addiw d => exact stepStrong_addiw trace binding i d h_known
  | mulw d => exact stepStrong_mulw trace binding i d
  | mulhu d => exact stepStrong_mulhu trace binding i d
  | divu d => exact stepStrong_divu trace binding i d
  | divuw d => exact stepStrong_divuw trace binding i d
  | remu d => exact stepStrong_remu trace binding i d
  | remuw d => exact stepStrong_remuw trace binding i d
  | beq d => exact stepStrong_beq trace binding i d h_known
  | bne d => exact stepStrong_bne trace binding i d h_known
  | blt d => exact stepStrong_blt trace binding i d h_known
  | bge d => exact stepStrong_bge trace binding i d h_known
  | bltu d => exact stepStrong_bltu trace binding i d h_known
  | bgeu d => exact stepStrong_bgeu trace binding i d h_known
  | lui d => exact stepStrong_lui trace binding i d
  | auipc d => exact stepStrong_auipc trace binding i d
  | jal d => exact stepStrong_jal trace binding i d
  | jalr d => exact stepStrong_jalr trace binding i d h_known
  | sb d => exact stepStrong_sb trace binding i d
  | sh d => exact stepStrong_sh trace binding i d
  | sw d => exact stepStrong_sw trace binding i d
  | sd d => exact stepStrong_sd trace binding i d
  | ld d => exact stepStrong_ld trace binding i d
  | lbu d => exact stepStrong_lbu trace binding i d
  | lhu d => exact stepStrong_lhu trace binding i d
  | lwu d => exact stepStrong_lwu trace binding i d
  | lb d => exact stepStrong_lb trace binding i d
  | lh d => exact stepStrong_lh trace binding i d
  | lw d => exact stepStrong_lw trace binding i d

/-- **Strengthened trace-level export (#61, channel-balance form).**

    From an accepted full-ensemble trace, a program binding, and a per-row
    classification into the 49 strengthened archetypes, EVERY row satisfies the
    canonical channel-balance per-step conclusion (`= state_effect_via_channels …`)
    — the SAME conclusion the OLD global theorem `zisk_riscv_compliant_program_bus`
    produces.  For the 22 op-bus ALU arms the `OpEnvelope` is CONSTRUCTED from the
    trace inside each `stepStrong_<op>` (no caller-supplied envelope); for the 27
    control-flow + U-type + store + load + M-ext-unsigned arms the conclusion is
    the channel-balance lift of each `construction_<op>_sound` over the real trace
    row.  The 6 M-ext-unsigned arms (MULW/MULHU/DIVU/DIVUW/REMU/REMUW) lift the
    FAITHFUL loose-bound (`<983041`) construction, NEVER the canonical equiv's
    tight (`<131072`) carry bound, so they are non-vacuous and sound.  This is
    strictly stronger
    than the `bus_effect`-form `zisk_compliant_of_accepted_trace`: every
    conclusion it yields is `state_effect_via_channels …`, defeq-implying the
    `bus_effect`-form, over the committed trace.

    ## Threaded defect-exclusion hypothesis (`h_known_bugs`)

    The `h_known_bugs` premise is the per-row defect-exclusion obligation
    (`StepNoKnownDefect`).  It is threaded — via `stepComplianceStrong_of_rowData`
    — to each OpEnvelope-route `stepStrong_<op>`, which feeds it to the old global
    theorem `zisk_riscv_compliant_program_bus` in place of an internally-proved
    `NoKnownDefect`.  For every one of the current (non-defect) arms the obligation
    is `EnvNoKnownDefectFor` on a non-defect constructor (or `True` for the
    direct-lift arms), so it is TRIVIALLY satisfiable — see
    `envNoKnownDefectFor_of_nondefect` — and this theorem is therefore NOT vacuous.
    The hypothesis is the plumbing that lets the signed-M / FENCE defect ops be
    added on the OpEnvelope route later: their `StepNoKnownDefect` obligation is the
    genuine `NoKnownDefect` of a defect-region envelope, which is NOT
    unconditionally true and must be supplied (or excluded) by the caller. -/
theorem zisk_compliant_of_accepted_trace_strong
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (rowData : ∀ i : Fin trace.length, StrongRowConstructionData trace binding i)
    (h_known_bugs : ∀ i : Fin trace.length, StepNoKnownDefect trace binding i (rowData i)) :
    ∀ i : Fin trace.length, StepComplianceStrong trace binding i (rowData i) :=
  fun i => stepComplianceStrong_of_rowData trace binding i (rowData i) (h_known_bugs i)


end ZiskFv.Compliance
