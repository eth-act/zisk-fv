import ZiskFv.Compliance.TraceLevelExport.BootSegmentMemorySeed
import ZiskFv.Compliance.TraceLevelExport.SegmentPcSeed

/-!
# `SailRetireChain` — #330 Phase 7

`SegmentPcSeed.succ` says "the Sail PC at step `j + 1` is the next-PC mux the Main row at `j`
computes". That is an equation between a ZisK column and a Sail register, assumed once per executed
step. It exists only because `SailTrace` is a bare `Fin n → SailState`
(`ZiskFv/Compliance/SailTrace.lean`) with no chaining: nothing else says the Sail states form an
execution.

This module replaces it with a premise that mentions **no ZisK column**: the Sail trace advances by
retiring its own step. `succ` then follows, by strong induction on the step index, from `boot` plus
the per-step soundness result the export already proves.

## The three pieces

1. `nextPC_of_busEffect_ok` — whenever the channel-routed post-state succeeds, its `nextPC` register
   is exactly `BitVec.ofNat 64 (execRows[1]!.pc).val`. Uniform: it needs the execution bus's shape
   (length `2`, multiplicities `-1` / `1`) and nothing about the memory bus, the opcode, or the row.
2. `execRowOf_producer_pc_eq_nextPcMux` (proved in `SegmentPcSeed.lean`) — that producer entry
   **is** `nextPcMux ziskTrace i`.
3. `SailRetireChain` — the Sail-internal law: the state at `j + 1` has as its `PC` whatever the step
   at `j` retired into `nextPC`.

Composing them: `StepSound j` equates the Sail action with the channel effect, (1) reads `nextPC`
off it, (2) identifies it with the mux, (3) hands it to the next step's `PC`, and
`mainOfTable_pc_succ_eq_nextPcMux` puts it back on the `pc` column. That is `succ j`.

## Why this is a strength reduction and not another repackaging

`SegmentPcSeed.succ` and `SegmentPcSeed.boot` are inter-derivable with the old per-row
`h_pc_bridge` bundle (`pcSeed_of_inputsAgree`), which is why Phase 5/6 was labelled a restructuring
in `trust/trusted-base.md`. `SailRetireChain` is different in kind: it is a statement about the Sail
trace alone. Nothing in it mentions `mainOfTable`, `nextPcMux`, or any committed column, so it
cannot encode an assumed cross-machine agreement. The cross-machine content that `succ` carried is
*derived* here, from `StepSound` — a theorem — instead of assumed.

The converse does not hold: `SailRetireChain` cannot be recovered from `succ`, because `succ` says
nothing about whether the Sail step retires at all.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

variable {numInstructions : ℕ}

/-- The tail of `bus_effect`, abstracted over the memory pass. `bus_effect` finishes by matching on
    the memory fold's result and, on success, writing the producer entry's `pc` into `nextPC`. This
    lemma reads that write back off the final state without ever inspecting the fold: on the error
    branch the hypothesis is already contradictory. -/
private lemma nextPC_of_writeReg_match
    (pm : Prop × EStateM.Result (Sail.Error exception)
      (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult)
    (v : RegisterType Register.nextPC)
    (result : ExecutionResult)
    (post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h : (match pm.2 with
          | .ok _ st =>
              (pm.1, EStateM.Result.map (fun _ ↦ ExecutionResult.Retire_Success ())
                       (Sail.writeReg Register.nextPC v st))
          | _ => pm).2 = .ok result post) :
    post.regs.get? Register.nextPC = some v := by
  obtain ⟨cond, res⟩ := pm
  cases res with
  | error e s => simp at h
  | ok a s =>
      simp only [Sail.writeReg, PreSail.writeReg, modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet, EStateM.Result.map] at h
      cases h
      simp

/-- **Uniform next-PC projection.** If the channel-routed post-state of a well-shaped execution bus
    succeeds, its `nextPC` register holds the producer entry's `pc`.

    The only hypotheses are the execution bus's own shape — which `Pilot.execRowOf` and
    `Pilot.execRowAt` satisfy by construction, both being two-element literals with multiplicities
    `-1` and `1`. Nothing about the memory bus is needed: `h_ok` already rules out the error branch
    that a malformed memory entry would produce, so the fold is never inspected.

    This is what makes the retire chain a single lemma rather than 63 per-arm ones. -/
theorem nextPC_of_busEffect_ok
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (memRows : List (Interaction.MemoryBusEntry FGL))
    (state post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (result : ExecutionResult)
    (h_len : execRows.length = 2)
    (h_e0 : execRows[0]!.multiplicity = -1)
    (h_e1 : execRows[1]!.multiplicity = 1)
    (h_ok : (bus_effect execRows memRows state).2 = .ok result post) :
    post.regs.get? Register.nextPC
      = some (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRows[1]!.pc).val)) := by
  unfold bus_effect at h_ok
  simp only [h_len, h_e0, h_e1, and_self, if_true] at h_ok
  exact nextPC_of_writeReg_match _ _ _ _ h_ok

/-- **The channel effect never faults, for an empty memory bus.** `bus_effect`'s only error exits
    are a malformed execution bus and a memory entry whose multiplicity or address space is outside
    `{-1, 0, 1}` / `{1, 2}`. With no memory entries the second cannot fire. -/
private lemma busEffect_ok_nil
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_len : execRows.length = 2)
    (h_e0 : execRows[0]!.multiplicity = -1)
    (h_e1 : execRows[1]!.multiplicity = 1) :
    ∃ result post, (bus_effect execRows [] state).2 = .ok result post := by
  unfold bus_effect
  simp only [h_len, h_e0, h_e1, and_self, if_true, List.foldl_nil]
  exact ⟨_, _, rfl⟩

/-- The single-write memory bus (`lui` / `auipc` / `jal` / `jalr`): one register write. -/
private lemma busEffect_ok_one
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (e0 : Interaction.MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_len : execRows.length = 2)
    (h_e0 : execRows[0]!.multiplicity = -1)
    (h_e1 : execRows[1]!.multiplicity = 1)
    (h_m0 : e0.multiplicity = 1) (h_a0 : e0.as = 1) :
    ∃ result post, (bus_effect execRows [e0] state).2 = .ok result post := by
  have h_one_ne : ((1 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_one_val : ((1 : FGL) : ℕ) = 1 := rfl
  unfold bus_effect
  simp only [h_len, h_e0, h_e1, and_self, if_true, List.foldl_cons, List.foldl_nil,
    h_m0, h_a0, h_one_ne, h_one_val, if_false, if_true]
  simp only [write_xreg, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map]
  by_cases hz : Transpiler.wrap_to_regidx e0.ptr = 0
  · simp only [dif_pos hz]
    exact ⟨_, _, rfl⟩
  · simp only [dif_neg hz]
    exact ⟨_, _, rfl⟩

/-- The three-entry memory bus (`busSub` / `busSt` / `busLd`): two reads then one write, each with a
    literal address space of `1` (register) or `2` (memory). -/
private lemma busEffect_ok_three
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (h_len : execRows.length = 2)
    (h_e0 : execRows[0]!.multiplicity = -1)
    (h_e1 : execRows[1]!.multiplicity = 1)
    (h_m0 : e0.multiplicity = -1) (h_a0 : e0.as = 1 ∨ e0.as = 2)
    (h_m1 : e1.multiplicity = -1) (h_a1 : e1.as = 1 ∨ e1.as = 2)
    (h_m2 : e2.multiplicity = 1) (h_a2 : e2.as = 1 ∨ e2.as = 2) :
    ∃ result post, (bus_effect execRows [e0, e1, e2] state).2 = .ok result post := by
  have h_one_ne : ((1 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_one_val : ((1 : FGL) : ℕ) = 1 := rfl
  have h_two_val : ((2 : FGL) : ℕ) = 2 := rfl
  have h_two_one : ((2 : ℕ) = 1) = False := by simp
  unfold bus_effect
  rcases h_a0 with h_a0 | h_a0 <;> rcases h_a1 with h_a1 | h_a1 <;>
    rcases h_a2 with h_a2 | h_a2 <;>
    simp only [h_len, h_e0, h_e1, and_self, if_true, List.foldl_cons, List.foldl_nil,
      h_m0, h_m1, h_m2, h_a0, h_a1, h_a2, h_one_ne, h_one_val, h_two_val, h_two_one,
      if_false, if_true, write_xreg, Sail.writeReg, PreSail.writeReg, modify,
      modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.Result.map]
  all_goals
    first
      | exact ⟨_, _, rfl⟩
      | (by_cases hz : Transpiler.wrap_to_regidx e2.ptr = 0
         · simp only [dif_pos hz]
           exact ⟨_, _, rfl⟩
         · simp only [dif_neg hz]
           exact ⟨_, _, rfl⟩)

/-- **The architectural instruction a ZisK step executes.** One arm per `ZiskStep` constructor,
    reading the instruction expression straight off the corresponding arm of `StepSound`. It exists
    so the Sail side of a step can be named without mentioning any committed column, which is what
    makes `SailRetireChain` below a statement about the Sail trace alone. -/
noncomputable def sailInstructionOf
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → instruction
  | .sub c => instruction.RTYPE (c.r2, c.r1, c.rd, rop.SUB)
  | .and c => instruction.RTYPE (c.r2, c.r1, c.rd, rop.AND)
  | .or c => instruction.RTYPE (c.r2, c.r1, c.rd, rop.OR)
  | .xor c => instruction.RTYPE (c.r2, c.r1, c.rd, rop.XOR)
  | .slt c => instruction.RTYPE (c.r2, c.r1, c.rd, rop.SLT)
  | .sltu c => instruction.RTYPE (c.r2, c.r1, c.rd, rop.SLTU)
  | .andi c => instruction.ITYPE (c.imm, c.r1, c.rd, iop.ANDI)
  | .ori c => instruction.ITYPE (c.imm, c.r1, c.rd, iop.ORI)
  | .xori c => instruction.ITYPE (c.imm, c.r1, c.rd, iop.XORI)
  | .slti c => instruction.ITYPE (c.imm, c.r1, c.rd, iop.SLTI)
  | .sltiu c => instruction.ITYPE (c.imm, c.r1, c.rd, iop.SLTIU)
  | .sll c => instruction.RTYPE (c.r2, c.r1, c.rd, rop.SLL)
  | .srl c => instruction.RTYPE (c.r2, c.r1, c.rd, rop.SRL)
  | .sra c => instruction.RTYPE (c.r2, c.r1, c.rd, rop.SRA)
  | .slli c => instruction.SHIFTIOP (c.shamt, c.r1, c.rd, sop.SLLI)
  | .srli c => instruction.SHIFTIOP (c.shamt, c.r1, c.rd, sop.SRLI)
  | .srai c => instruction.SHIFTIOP (c.shamt, c.r1, c.rd, sop.SRAI)
  | .add c => instruction.RTYPE (c.r2, c.r1, c.rd, rop.ADD)
  | .addi c => instruction.ITYPE (c.imm, c.r1, c.rd, iop.ADDI)
  | .subw c => instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SUBW)
  | .addw c => instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.ADDW)
  | .addiw c => instruction.ADDIW (c.imm, c.r1, c.rd)
  | .sllw c => instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SLLW)
  | .srlw c => instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SRLW)
  | .sraw c => instruction.RTYPEW (c.r2, c.r1, c.rd, ropw.SRAW)
  | .slliw c => instruction.SHIFTIWOP (c.slliw_input.shamt, c.r1, c.rd, sopw.SLLIW)
  | .srliw c => instruction.SHIFTIWOP (c.srliw_input.shamt, c.r1, c.rd, sopw.SRLIW)
  | .sraiw c => instruction.SHIFTIWOP (c.sraiw_input.shamt, c.r1, c.rd, sopw.SRAIW)
  | .mul c => instruction.MUL
      (c.r2, c.r1, c.rd,
       { result_part := VectorHalf.Low
         signed_rs1 := c.srs1
         signed_rs2 := c.srs2 })
  | .mulh c => instruction.MUL
      (c.r2, c.r1, c.rd,
       { result_part := VectorHalf.High
         signed_rs1 := .Signed
         signed_rs2 := .Signed })
  | .mulhsu c => instruction.MUL
      (c.r2, c.r1, c.rd,
       { result_part := VectorHalf.High
         signed_rs1 := .Signed
         signed_rs2 := .Unsigned })
  | .div c => instruction.DIV (c.r2, c.r1, c.rd, false)
  | .rem c => instruction.REM (c.r2, c.r1, c.rd, false)
  | .divw c => instruction.DIVW (c.r2, c.r1, c.rd, false)
  | .remw c => instruction.REMW (c.r2, c.r1, c.rd, false)
  | .mulw c => instruction.MULW (c.r2, c.r1, c.rd)
  | .mulhu c => instruction.MUL
      (c.r2, c.r1, c.rd,
       { result_part := VectorHalf.High
         signed_rs1 := .Unsigned
         signed_rs2 := .Unsigned })
  | .divu c => instruction.DIV (c.r2, c.r1, c.rd, true)
  | .divuw c => instruction.DIVW (c.r2, c.r1, c.rd, true)
  | .remu c => instruction.REM (c.r2, c.r1, c.rd, true)
  | .remuw c => instruction.REMW (c.r2, c.r1, c.rd, true)
  | .beq c => instruction.BTYPE (c.imm, c.r2, c.r1, bop.BEQ)
  | .bne c => instruction.BTYPE (c.imm, c.r2, c.r1, bop.BNE)
  | .blt c => instruction.BTYPE (c.imm, c.r2, c.r1, bop.BLT)
  | .bge c => instruction.BTYPE (c.imm, c.r2, c.r1, bop.BGE)
  | .bltu c => instruction.BTYPE (c.imm, c.r2, c.r1, bop.BLTU)
  | .bgeu c => instruction.BTYPE (c.imm, c.r2, c.r1, bop.BGEU)
  | .lui c => instruction.UTYPE (c.imm, c.rd, uop.LUI)
  | .auipc c => instruction.UTYPE (c.imm, c.rd, uop.AUIPC)
  | .jal c => instruction.JAL (c.imm, c.rd)
  | .jalr c => instruction.JALR (c.imm, c.rs1, c.rd)
  | .sb c => instruction.STORE
      (c.sb_input.imm, regidx.Regidx c.sb_input.r2, regidx.Regidx c.sb_input.r1, 1)
  | .sh c => instruction.STORE
      (c.sh_input.imm, regidx.Regidx c.sh_input.r2, regidx.Regidx c.sh_input.r1, 2)
  | .sw c => instruction.STORE
      (c.sw_input.imm, regidx.Regidx c.sw_input.r2, regidx.Regidx c.sw_input.r1, 4)
  | .sd c => instruction.STORE
      (c.sd_input.imm, regidx.Regidx c.sd_input.r2, regidx.Regidx c.sd_input.r1, 8)
  | .ld c => instruction.LOAD
      (c.ld_input.imm, regidx.Regidx c.ld_input.r1, regidx.Regidx c.ld_input.rd, false, 8)
  | .lbu c => instruction.LOAD
      (c.lbu_input.imm, regidx.Regidx c.lbu_input.r1, regidx.Regidx c.lbu_input.rd, true, 1)
  | .lhu c => instruction.LOAD
      (c.lhu_input.imm, regidx.Regidx c.lhu_input.r1, regidx.Regidx c.lhu_input.rd, true, 2)
  | .lwu c => instruction.LOAD
      (c.lwu_input.imm, regidx.Regidx c.lwu_input.r1, regidx.Regidx c.lwu_input.rd, true, 4)
  | .lb c => instruction.LOAD
      (c.lb_input.imm, regidx.Regidx c.lb_input.r1, regidx.Regidx c.lb_input.rd, false, 1)
  | .lh c => instruction.LOAD
      (c.lh_input.imm, regidx.Regidx c.lh_input.r1, regidx.Regidx c.lh_input.rd, false, 2)
  | .lw c => instruction.LOAD
      (c.lw_input.imm, regidx.Regidx c.lw_input.r1, regidx.Regidx c.lw_input.rd, false, 4)
  | .fence c => instruction.FENCE (c.fm, c.fenceP, c.fenceS, c.rs, c.rd)

/-- The Sail action `StepSound` equates with the channel effect, applied to the step's Sail state.

    Every arm of `StepSound` has this left-hand side: 33 arms write it as `execute_instruction`, and
    the other 30 spell out the `do` block. `execute_instruction` (`SailSpec/Auxiliaries.lean`) *is*
    that block, so the two spellings are definitionally equal and `stepSound_iff` below closes by
    `rfl`. -/
@[reducible] noncomputable def sailStepResult
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (binding : SailTrace ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i) :
    EStateM.Result (Sail.Error exception)
      (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult :=
  execute_instruction (sailInstructionOf i zs) (binding i)

/-- **The channel-interaction output a step's `StepSound` arm compares against.** Again one arm per
    constructor, mirroring the right-hand sides of `StepSound` / `StepSoundWithoutDecode`. Naming it
    lets the next-PC projection run once instead of once per opcode. -/
noncomputable def stepChannelOutput
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) :
    (zs : ZiskStep ziskTrace i) → RowDecode ziskTrace i zs →
      ZiskFv.Channels.ChannelEnsembleOutput
  | .sub _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .and _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .or _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .xor _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .slt _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .sltu _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .andi _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .ori _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .xori _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .slti _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .sltiu _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .sll _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .srl _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .sra _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .slli _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .srli _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .srai _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .add _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .addi _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .subw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .addw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .addiw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .sllw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .srlw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .sraw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .slliw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .srliw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .sraiw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .mul _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .mulh _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .mulhsu _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .div _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .rem _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .divw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .remw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .mulw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .mulhu _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .divu _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .divuw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .remu _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .remuw _, _ =>
      ⟨(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSub ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .beq _, _ =>
      ⟨Pilot.execRowOf ziskTrace i, []⟩
  | .bne _, _ =>
      ⟨Pilot.execRowOf ziskTrace i, []⟩
  | .blt _, _ =>
      ⟨Pilot.execRowOf ziskTrace i, []⟩
  | .bge _, _ =>
      ⟨Pilot.execRowOf ziskTrace i, []⟩
  | .bltu _, _ =>
      ⟨Pilot.execRowOf ziskTrace i, []⟩
  | .bgeu _, _ =>
      ⟨Pilot.execRowOf ziskTrace i, []⟩
  | .lui _, _ =>
      ⟨Pilot.execRowOf ziskTrace i, [eRdLui ziskTrace i]⟩
  | .auipc _, _ =>
      ⟨Pilot.execRowOf ziskTrace i, [eRdLui ziskTrace i]⟩
  | .jal _, _ =>
      ⟨Pilot.execRowOf ziskTrace i, [eRdLui ziskTrace i]⟩
  | .jalr _, decode =>
      ⟨Pilot.execRowAt ziskTrace decode.rows.finish,
        [eRdAt ziskTrace decode.rows.finish]⟩
  | .sb _, _ =>
      ⟨(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .sh _, _ =>
      ⟨(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .sw _, _ =>
      ⟨(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .sd _, _ =>
      ⟨(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .ld _, _ =>
      ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .lbu _, _ =>
      ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .lhu _, _ =>
      ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .lwu _, _ =>
      ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .lb _, _ =>
      ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .lh _, _ =>
      ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .lw _, _ =>
      ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).exec_row,
      [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e0, (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
       (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]⟩
  | .fence _, _ =>
      ⟨Pilot.execRowOf ziskTrace i, []⟩

/-- **The Main row whose successor `pc` the step writes into Sail's `nextPC`.**

    For 62 of the 63 arms the execution bus is `Pilot.execRowOf ziskTrace i`, so the producer row is
    the step's own row `i`. JALR is the exception: its `StepSound` arm is indexed by the decode and
    uses `Pilot.execRowAt ziskTrace decode.rows.finish`, the *terminal* row of a possibly two-row
    unaligned lowering. -/
noncomputable def stepProducerRow
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) :
    (zs : ZiskStep ziskTrace i) → RowDecode ziskTrace i zs → ℕ
  | .sub _, _ => i.val
  | .and _, _ => i.val
  | .or _, _ => i.val
  | .xor _, _ => i.val
  | .slt _, _ => i.val
  | .sltu _, _ => i.val
  | .andi _, _ => i.val
  | .ori _, _ => i.val
  | .xori _, _ => i.val
  | .slti _, _ => i.val
  | .sltiu _, _ => i.val
  | .sll _, _ => i.val
  | .srl _, _ => i.val
  | .sra _, _ => i.val
  | .slli _, _ => i.val
  | .srli _, _ => i.val
  | .srai _, _ => i.val
  | .add _, _ => i.val
  | .addi _, _ => i.val
  | .subw _, _ => i.val
  | .addw _, _ => i.val
  | .addiw _, _ => i.val
  | .sllw _, _ => i.val
  | .srlw _, _ => i.val
  | .sraw _, _ => i.val
  | .slliw _, _ => i.val
  | .srliw _, _ => i.val
  | .sraiw _, _ => i.val
  | .mul _, _ => i.val
  | .mulh _, _ => i.val
  | .mulhsu _, _ => i.val
  | .div _, _ => i.val
  | .rem _, _ => i.val
  | .divw _, _ => i.val
  | .remw _, _ => i.val
  | .mulw _, _ => i.val
  | .mulhu _, _ => i.val
  | .divu _, _ => i.val
  | .divuw _, _ => i.val
  | .remu _, _ => i.val
  | .remuw _, _ => i.val
  | .beq _, _ => i.val
  | .bne _, _ => i.val
  | .blt _, _ => i.val
  | .bge _, _ => i.val
  | .bltu _, _ => i.val
  | .bgeu _, _ => i.val
  | .lui _, _ => i.val
  | .auipc _, _ => i.val
  | .jal _, _ => i.val
  | .jalr _, decode => decode.rows.finish.val
  | .sb _, _ => i.val
  | .sh _, _ => i.val
  | .sw _, _ => i.val
  | .sd _, _ => i.val
  | .ld _, _ => i.val
  | .lbu _, _ => i.val
  | .lhu _, _ => i.val
  | .lwu _, _ => i.val
  | .lb _, _ => i.val
  | .lh _, _ => i.val
  | .lw _, _ => i.val
  | .fence _, _ => i.val

/-- **`StepSound` in named form.** Both sides are the same proposition; this only replaces the
    63-arm `match` by the two named functions above, so that the next-PC projection can be applied
    once rather than re-derived per opcode. Every arm closes by `rfl`. -/
theorem stepSound_iff
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) :
    StepSound ziskTrace binding i zs rd ↔
      sailStepResult binding i zs
        = ZiskFv.Channels.state_effect_via_channels (stepChannelOutput i zs rd) (binding i) := by
  cases zs <;> rfl

/-- **Every arm's execution bus is the same two-entry literal**, at the step's producer row. This is
    where the 63 arms collapse: `busSub` / `busSt` / `busLd` all set `exec_row := execRow` and are
    applied to `Pilot.execRowOf ziskTrace i`, and JALR's `Pilot.execRowAt` has the same shape at its
    decode-selected row. -/
theorem stepChannelOutput_execRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) :
    (stepChannelOutput i zs rd).execRows
      = [ { multiplicity := -1
          , pc := (mainOfTable ziskTrace.program ziskTrace.mainTable).pc (stepProducerRow i zs rd)
          , timestamp := 1 }
        , { multiplicity := 1
          , pc :=
              (mainOfTable ziskTrace.program ziskTrace.mainTable).pc (stepProducerRow i zs rd + 1)
          , timestamp := 1 } ] := by
  cases zs <;> rfl

set_option maxHeartbeats 1000000 in
/-- **No arm's channel effect faults.** Every `stepChannelOutput` is one of five concrete bus
    shapes, and in each the memory entries carry *literal* multiplicities (`-1` / `1`) and address
    spaces (`1` register / `2` memory) — `MemBusMessage.toEntry` takes both as explicit arguments,
    and `busSub` / `busSt` / `busLd` / `eRdLui` / `eRdAt` pass numerals. So `bus_effect`'s
    "impossible under assumptions" error exits are unreachable here, and this is proved rather than
    assumed. That is what lets `SailRetireChain.retire` be a plain law with no existential. -/
theorem stepChannelOutput_busEffect_ok
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    ∃ result post,
      (bus_effect (stepChannelOutput i zs rd).execRows (stepChannelOutput i zs rd).memRows state).2
        = .ok result post := by
  have hx := stepChannelOutput_execRows i zs rd
  have h_len : (stepChannelOutput i zs rd).execRows.length = 2 := by rw [hx]; rfl
  have h_e0 : (stepChannelOutput i zs rd).execRows[0]!.multiplicity = -1 := by rw [hx]; rfl
  have h_e1 : (stepChannelOutput i zs rd).execRows[1]!.multiplicity = 1 := by rw [hx]; rfl
  cases zs <;>
    first
      | exact busEffect_ok_three _ _ _ _ _ h_len h_e0 h_e1
          rfl (Or.inl rfl) rfl (Or.inl rfl) rfl (Or.inl rfl)
      | exact busEffect_ok_nil _ _ h_len h_e0 h_e1
      | exact busEffect_ok_three _ _ _ _ _ h_len h_e0 h_e1
          rfl (Or.inl rfl) rfl (Or.inr rfl) rfl (Or.inl rfl)
      | exact busEffect_ok_three _ _ _ _ _ h_len h_e0 h_e1
          rfl (Or.inl rfl) rfl (Or.inl rfl) rfl (Or.inr rfl)
      | exact busEffect_ok_one _ _ _ h_len h_e0 h_e1 rfl rfl

/-- **The Sail trace is an execution.** The state at step `j + 1` takes its `PC` from what step `j`
    retired into `nextPC`.

    This is the premise that replaces `SegmentPcSeed.succ`. Read what it does *not* mention:
    `mainOfTable`, `nextPcMux`, the `pc` column, or any other committed ZisK datum. It relates two
    Sail states through Sail's own step function, so it cannot smuggle in an assumed cross-machine
    agreement. `SailTrace` is a bare `Fin n → SailState`, so without a premise of this shape nothing
    says the states form an execution at all — which is exactly why `succ` had to be assumed.

    It is a plain law, not an existential: `stepChannelOutput_busEffect_ok` proves the step's channel
    effect never faults, so the `.ok` hypothesis is discharged at the use site rather than assumed
    here. -/
structure SailRetireChain
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace ziskTrace.numInstructions)
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i) : Prop where
  retire : ∀ (j : ℕ) (h : j + 1 < ziskTrace.numInstructions)
      (result : ExecutionResult)
      (post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource),
    sailStepResult binding ⟨j, Nat.lt_of_succ_lt h⟩ (ziskStep ⟨j, Nat.lt_of_succ_lt h⟩)
        = .ok result post →
    (binding ⟨j + 1, h⟩).regs.get? Register.PC = post.regs.get? Register.nextPC

/-- **Each executed step's producer entry is its own row's successor `pc`.**

    For 62 of the 63 arms this is `rfl`: the execution bus is `Pilot.execRowOf ziskTrace i`. JALR is
    the exception. `JalrLoweringRows` pins `start.val = i.val` but allows a two-row unaligned
    lowering with `finish.val = start.val + 1`, and `StepSound`'s JALR arm is indexed by `finish`. So
    an unaligned JALR at step `j` writes `pc (j + 2)` into Sail's `nextPC`, while step `j + 1`'s PC
    bridge is stated at `pc (j + 1)`.

    **This condition was previously hidden inside the assumed `succ`.** The old premise asserted the
    Sail PC at `j + 1` directly, so a trace could satisfy it while the Sail step had in fact retired
    into a different `nextPC`; nothing checked the two agreed. Deriving `succ` instead of assuming it
    forces the placement question into the open, and this is where it lands: the executed-step index
    and the physical Main-row index must not have drifted apart at a step that has a successor.

    It is required only where `succ` was: at steps with a successor. A trace whose only unaligned
    JALR is its last step — the shape `jalrSpinRootSoundness` uses — discharges it vacuously. -/
def StepRowsAligned
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i)
    (rowDecodes : ∀ i : Fin ziskTrace.numInstructions, RowDecode ziskTrace i (ziskStep i)) : Prop :=
  ∀ (j : ℕ) (h : j + 1 < ziskTrace.numInstructions),
    stepProducerRow ⟨j, Nat.lt_of_succ_lt h⟩ (ziskStep ⟨j, Nat.lt_of_succ_lt h⟩)
      (rowDecodes ⟨j, Nat.lt_of_succ_lt h⟩) = j

/-- **The inductive step.** Per-step soundness at `j`, plus the retire law, gives PC agreement at
    `j + 1` — the fact `SegmentPcSeed.succ` used to assume.

    The chain is: `StepSound j` equates the Sail action with the channel effect; the channel effect
    succeeds (`stepChannelOutput_busEffect_ok`); its post-state's `nextPC` is the producer entry's
    `pc` (`nextPC_of_busEffect_ok`), which at an aligned step is the Main `pc` column at `j + 1`; and
    `retire` hands that to the Sail PC at `j + 1`. -/
theorem pcBridge_succ_of_stepSound
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {rowDecodes : ∀ i : Fin ziskTrace.numInstructions, RowDecode ziskTrace i (ziskStep i)}
    (chain : SailRetireChain ziskTrace binding ziskStep)
    (aligned : StepRowsAligned ziskTrace ziskStep rowDecodes)
    (j : ℕ) (h : j + 1 < ziskTrace.numInstructions)
    (h_step : StepSound ziskTrace binding ⟨j, Nat.lt_of_succ_lt h⟩
      (ziskStep ⟨j, Nat.lt_of_succ_lt h⟩) (rowDecodes ⟨j, Nat.lt_of_succ_lt h⟩)) :
    ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc (j + 1)).val
      = ((binding ⟨j + 1, h⟩).regs.get? Register.PC).elim 0 BitVec.toNat := by
  set jj : Fin ziskTrace.numInstructions := ⟨j, Nat.lt_of_succ_lt h⟩ with hjj
  obtain ⟨result, post, h_ok⟩ :=
    stepChannelOutput_busEffect_ok jj (ziskStep jj) (rowDecodes jj) (binding jj)
  have hx := stepChannelOutput_execRows jj (ziskStep jj) (rowDecodes jj)
  have h_len : (stepChannelOutput jj (ziskStep jj) (rowDecodes jj)).execRows.length = 2 := by
    rw [hx]; rfl
  have h_e0 :
      (stepChannelOutput jj (ziskStep jj) (rowDecodes jj)).execRows[0]!.multiplicity = -1 := by
    rw [hx]; rfl
  have h_e1 :
      (stepChannelOutput jj (ziskStep jj) (rowDecodes jj)).execRows[1]!.multiplicity = 1 := by
    rw [hx]; rfl
  have h_producer :
      (stepChannelOutput jj (ziskStep jj) (rowDecodes jj)).execRows[1]!.pc
        = (mainOfTable ziskTrace.program ziskTrace.mainTable).pc (j + 1) := by
    rw [hx, aligned j h]; rfl
  have h_eq : sailStepResult binding jj (ziskStep jj) = .ok result post := by
    rw [(stepSound_iff jj (ziskStep jj) (rowDecodes jj)).mp h_step]
    exact h_ok
  have h_next := nextPC_of_busEffect_ok _ _ _ _ _ h_len h_e0 h_e1 h_ok
  rw [chain.retire j h result post h_eq, h_next, h_producer]
  simp only [Option.elim]
  exact
    (Nat.mod_eq_of_lt
      (lt_trans ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc (j + 1)).isLt
        (by norm_num))).symm

/-- **The PC premise of `root_soundness`, after Phase 7.** One cross-machine equation, at row `0`,
    plus the Sail-internal retire law.

    Compare `SegmentPcSeed`, which this replaces: that carried `boot` **and** `succ`, and `succ`
    named the `pc` column at every step. Here the only statement relating a committed column to a
    Sail register is `boot`. Everything else about the PC is derived —
    `mainOfTable_pc_succ_eq_nextPcMux` from the circuit's own transition constraint,
    `nextPC_of_busEffect_ok` from `bus_effect`, and the step-to-step link from `retire`.

    `pcSeed_of_inputsAgree` proved `SegmentPcSeed` inter-derivable with the old per-row bundle, so
    Phase 5/6 was a restructuring. This is not: `retire` cannot be recovered from the per-row
    `h_pc_bridge` fields, because they say nothing about whether the Sail step retires. -/
structure SegmentPcChain
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace ziskTrace.numInstructions)
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i) : Prop
    extends SailRetireChain ziskTrace binding ziskStep where
  /-- Boot: the Sail PC at step `0` is the Main `pc` column at row `0`. The one cross-machine
      premise left on the PC arm. -/
  boot : ∀ (h : 0 < ziskTrace.numInstructions),
    ((mainOfTable ziskTrace.program ziskTrace.mainTable).pc 0).val
      = ((binding ⟨0, h⟩).regs.get? Register.PC).elim 0 BitVec.toNat

/-- **The old per-row bundle implies the retire law, at an aligned step.** Given the full
    `InputsAgree` a caller used to supply, plus the memory seed and defect exclusions it already
    supplies, `StepSound` follows at every row; reading `nextPC` off it and comparing with the next
    row's own `h_pc_bridge` gives `retire`.

    **This direction is why Phase 7 is not, by itself, a logical-strength reduction, and the
    docstrings must not claim one.** Together with `pcBridge_succ_of_stepSound` (which goes the other
    way) it shows the old bundle and `boot` + `retire` are inter-derivable *given*
    `StepRowsAligned` — the same situation `pcSeed_of_inputsAgree` established for Phase 5/6.

    What Phase 7 does change is where the assumption lives: the old bundle asserted cross-machine
    agreement at every executed row, while `boot` + `retire` assert it at row `0` only and otherwise
    speak about the Sail trace alone. And `StepRowsAligned`, which the old bundle silently did
    without, is now a visible premise.

    Its immediate job is the regression floor: the seven checked-in accepted-trace witnesses build
    their retire chain through here instead of proving Sail execution results by hand. -/
theorem sailRetireChain_of_inputsAgree
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (rowDecodes : ∀ i : Fin ziskTrace.numInstructions, RowDecode ziskTrace i (ziskStep i))
    (inputsAgree : ∀ i : Fin ziskTrace.numInstructions,
      InputsAgree ziskTrace binding i (ziskStep i))
    (bootSeed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (hAvoidKnownBugs : ∀ i : Fin ziskTrace.numInstructions,
      RowOutsideDefectRegion ziskTrace i (ziskStep i))
    (aligned : StepRowsAligned ziskTrace ziskStep rowDecodes) :
    SailRetireChain ziskTrace binding ziskStep where
  retire := by
    intro j h result post h_res
    have hj : j < ziskTrace.numInstructions := Nat.lt_of_succ_lt h
    have h_step := stepSound_of_evidence ziskTrace binding ⟨j, hj⟩ (ziskStep ⟨j, hj⟩)
      (rowDecodes ⟨j, hj⟩) (inputsAgree ⟨j, hj⟩)
      (memEvidence_of_bootSeed bootSeed ⟨j, hj⟩) (hAvoidKnownBugs ⟨j, hj⟩)
    have h_iff :=
      (stepSound_iff (binding := binding) ⟨j, hj⟩ (ziskStep ⟨j, hj⟩) (rowDecodes ⟨j, hj⟩)).mp h_step
    have h_ok :
        (bus_effect (stepChannelOutput ⟨j, hj⟩ (ziskStep ⟨j, hj⟩) (rowDecodes ⟨j, hj⟩)).execRows
          (stepChannelOutput ⟨j, hj⟩ (ziskStep ⟨j, hj⟩) (rowDecodes ⟨j, hj⟩)).memRows
          (binding ⟨j, hj⟩)).2 = .ok result post := by
      have h2 : ZiskFv.Channels.state_effect_via_channels
          (stepChannelOutput ⟨j, hj⟩ (ziskStep ⟨j, hj⟩) (rowDecodes ⟨j, hj⟩)) (binding ⟨j, hj⟩)
          = .ok result post := h_iff ▸ h_res
      exact h2
    have hx := stepChannelOutput_execRows ⟨j, hj⟩ (ziskStep ⟨j, hj⟩) (rowDecodes ⟨j, hj⟩)
    have h_len :
        (stepChannelOutput ⟨j, hj⟩ (ziskStep ⟨j, hj⟩) (rowDecodes ⟨j, hj⟩)).execRows.length = 2 := by
      rw [hx]; rfl
    have h_e0 :
        (stepChannelOutput ⟨j, hj⟩ (ziskStep ⟨j, hj⟩)
          (rowDecodes ⟨j, hj⟩)).execRows[0]!.multiplicity = -1 := by
      rw [hx]; rfl
    have h_e1 :
        (stepChannelOutput ⟨j, hj⟩ (ziskStep ⟨j, hj⟩)
          (rowDecodes ⟨j, hj⟩)).execRows[1]!.multiplicity = 1 := by
      rw [hx]; rfl
    have h_prod :
        (stepChannelOutput ⟨j, hj⟩ (ziskStep ⟨j, hj⟩) (rowDecodes ⟨j, hj⟩)).execRows[1]!.pc
          = (mainOfTable ziskTrace.program ziskTrace.mainTable).pc (j + 1) := by
      rw [hx, aligned j h]; rfl
    have h_next := nextPC_of_busEffect_ok _ _ _ _ _ h_len h_e0 h_e1 h_ok
    obtain ⟨v, hv⟩ :=
      pcNamed_of_inputsAgree ⟨j + 1, h⟩ (ziskStep ⟨j + 1, h⟩) (inputsAgree ⟨j + 1, h⟩)
    have h_ag :=
      pcAgreement_of_inputsAgree ⟨j + 1, h⟩ (ziskStep ⟨j + 1, h⟩) (inputsAgree ⟨j + 1, h⟩)
    simp only [hv, Option.elim] at h_ag
    rw [hv, h_next, h_prod, h_ag]
    exact congrArg some (BitVec.eq_of_toNat_eq (by simp)).symm

end ZiskFv.Compliance
