import ZiskFv.Equivalence.Compliance

/-!
# Compliance/Global.lean — Step 4.3 Phase 3 architectural validation

This file lands the **global compliance theorem skeleton** on top of
the 63 per-op `dispatch_<OP>` theorems in `Compliance.lean` (Phases 1
+ 2).

## The architectural finding (read this first)

The 63 dispatcher signatures are genuinely heterogeneous:

* They take different `PureSpec.<OP>Input` records (one per op).
* They take different sets of provider-AIR validators (LUI: none;
  ADD: BinaryAdd; LBU/LHU/LWU: Mem + MemAlignByte + MemAlignReadByte
  + MemAlign; etc).
* Their *bus shapes* differ: branches end with `bus_effect exec_row
  [] state`, LUI/AUIPC/JAL/JALR with `[e_rd]`, most arithmetic / mem
  with `[e0, e1, e2]`.
* Their LHS conclusion forms differ: `execute_instruction (instruction
  …) state` vs. `(do; writeReg Register.nextPC; execute …) state`,
  the latter arising whenever a Sail wrapper unfolds to a writeReg
  prefix.
* Some take `RISC_V_assumptions` with four register-typed inputs
  (`mstatus`, `pmaRegion`, `misa`, `mseccfg`); others take only
  `misa_val`; others take none.

Consequently, there is *no* single uniform predicate that captures
all 63 conclusions without case-splitting on the op-kind. The honest
shape of the global theorem is therefore:

```
inductive OpEnvelope … where
  | LUI  : <all dispatch_LUI inputs>  → OpEnvelope …
  | ADD  : <all dispatch_ADD inputs>  → OpEnvelope …
  | ...  -- 35 arms (one per `mainOpKind`); some arms further
         -- discriminate on the R-vs-I split (ADD covers ADD/ADDI).
```

Each arm bundles the per-dispatcher inputs, a `kind : mainOpKind`
projection identifies the op, and a `exec_eq : Prop` projection
states the dispatcher's conclusion. The global theorem then says:

```
theorem zisk_riscv_compliant_program_bus … :
  decode_main_row m r_main = some env.kind → env.exec_eq
```

The proof body is a 35-way `match env with | … => exact dispatch_<OP>
…`, i.e., pure routing. There is no new content — the trust footprint
is exactly the union of the 63 dispatchers' footprints, which is the
union of the 63 wrappers' footprints (147 axioms today).

## This file's deliverable

A **representative slice** of the global theorem covering 7
exemplar shapes:

* `BEQ` — Branch (no mem entries, no provider AIR).
* `FENCE` — ControlFlow no-mem.
* `LUI` — ControlFlow single-mem (`[e_rd]`).
* `ADD` — BinaryAdd shape (`[e0, e1, e2]`, R-type).
* `ADDI` — BinaryAdd shape with `do`-block LHS.
* `SUB` — Binary shape.
* `SB` — Memory store (`Valid_Main` only).

The full 63-arm `OpEnvelope` and its global dispatch is mechanical
follow-up — it scales linearly with no architectural surprises, and
the file's expected final size is ~1500–2000 LOC of pure plumbing.
The pattern here is verbatim-extensible: each remaining op needs
one constructor in `OpEnvelope`, one `kind` arm, one `exec_eq` arm,
and one `match` arm in the global theorem.

## Trust footprint

Zero new axioms. Everything in this file is structural assembly
over the existing dispatchers.
-/

namespace ZiskFv.Equivalence.Compliance.Global

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.Binary
open ZiskFv.Tactics.UTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.Equivalence.Compliance

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Decode side — `Option mainOpKind` (Design ii) -/

/-- **Decode the op-kind from a Main row.**

    Returns `none` iff `m.op r_main` is not one of the 35 in-scope
    Zisk OPs. The bridge from kind to a full Sail `instruction`
    happens at dispatch time, where the caller supplies operand
    witnesses (see `OpEnvelope` below).

    This is a `Prop`-valued helper: it returns `some k` iff
    `m.op r_main = k.toFGL`. The companion lemma
    `decode_main_row_correct` shows that under the RV64IM scope
    assumption decoding always succeeds. -/
noncomputable def decode_main_row (m : Valid_Main C FGL FGL) (r : ℕ) :
    Option mainOpKind :=
  open Classical in
  if h : ∃ k : mainOpKind, m.op r = k.toFGL then
    some h.choose
  else
    none

/-- `decode_main_row` succeeds for every RV64IM-in-scope row, and the
    decoded kind's `toFGL` matches `m.op r`.

    Direct from `main_op_in_RV64IM_scope`. -/
theorem decode_main_row_correct
    (m : Valid_Main C FGL FGL) (r : ℕ)
    (h_scope : main_op_in_RV64IM_scope m r) :
    ∃ k : mainOpKind, decode_main_row m r = some k ∧ m.op r = k.toFGL := by
  -- Enumerate the 35-way disjunction and produce the matching kind.
  have h_exists : ∃ k : mainOpKind, m.op r = k.toFGL := by
    rcases h_scope with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                       h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                       h | h | h | h | h
    · exact ⟨.FLAG, h⟩
    · exact ⟨.COPYB, h⟩
    · exact ⟨.LTU, h⟩
    · exact ⟨.LT, h⟩
    · exact ⟨.EQ, h⟩
    · exact ⟨.ADD, h⟩
    · exact ⟨.SUB, h⟩
    · exact ⟨.AND, h⟩
    · exact ⟨.OR, h⟩
    · exact ⟨.XOR, h⟩
    · exact ⟨.ADD_W, h⟩
    · exact ⟨.SUB_W, h⟩
    · exact ⟨.SLL, h⟩
    · exact ⟨.SRL, h⟩
    · exact ⟨.SRA, h⟩
    · exact ⟨.SLL_W, h⟩
    · exact ⟨.SRL_W, h⟩
    · exact ⟨.SRA_W, h⟩
    · exact ⟨.SIGNEXTEND_B, h⟩
    · exact ⟨.SIGNEXTEND_H, h⟩
    · exact ⟨.SIGNEXTEND_W, h⟩
    · exact ⟨.MULU, h⟩
    · exact ⟨.MULUH, h⟩
    · exact ⟨.MULSUH, h⟩
    · exact ⟨.MUL, h⟩
    · exact ⟨.MULH, h⟩
    · exact ⟨.MUL_W, h⟩
    · exact ⟨.DIVU, h⟩
    · exact ⟨.REMU, h⟩
    · exact ⟨.DIV, h⟩
    · exact ⟨.REM, h⟩
    · exact ⟨.DIVU_W, h⟩
    · exact ⟨.REMU_W, h⟩
    · exact ⟨.DIV_W, h⟩
    · exact ⟨.REM_W, h⟩
  refine ⟨h_exists.choose, ?_, h_exists.choose_spec⟩
  unfold decode_main_row
  exact dif_pos h_exists

/-! ## The `OpEnvelope` sum type

Bundles, per Zisk op-kind, the inputs the corresponding `dispatch_<OP>`
theorem requires beyond `(state, m, r_main)`. Each arm's signature is
verbatim from the dispatcher.

This file lands seven representative arms covering the bus-shape
variants. The remaining 28 arms are mechanical follow-up (one per
`mainOpKind`).

**Why a sum type?** Because the dispatcher signatures genuinely do
not unify (see the file-level docstring). A sum type is the honest
encoding; an existential over a record with all unioned fields would
be uniform but vacuous (every constructor sets most fields to `True`
/ junk values), which is worse than the case-split.
-/

set_option maxHeartbeats 1000000 in
/-- Per-op input bundle (representative slice).

    Each constructor's parameter list is exactly the corresponding
    `dispatch_<OP>` theorem's parameter list, minus the shared
    `(state, m, r_main)`. -/
inductive OpEnvelope
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) where
  -- ============================ BEQ (branch, no mem) ====================
  | beq
    (beq_input : PureSpec.BeqInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (beq_input.PC + BitVec.signExtend 64 beq_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BEQ_pure beq_input).nextPC) : OpEnvelope state m r_main
  -- ============================ BNE (branch, no mem) ====================
  | bne
    (bne_input : PureSpec.BneInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bne_input.PC + BitVec.signExtend 64 bne_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure bne_input).nextPC) : OpEnvelope state m r_main
  -- ============================ BLT (branch, no mem) ====================
  | blt
    (blt_input : PureSpec.BltInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (blt_input.PC + BitVec.signExtend 64 blt_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLT_pure blt_input).nextPC) : OpEnvelope state m r_main
  -- ============================ BGE (branch, no mem) ====================
  | bge
    (bge_input : PureSpec.BgeInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bge_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bge_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bge_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bge_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bge_input.PC + BitVec.signExtend 64 bge_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGE_pure bge_input).nextPC) : OpEnvelope state m r_main
  -- ============================ BLTU (branch, no mem) ===================
  | bltu
    (bltu_input : PureSpec.BltuInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bltu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bltu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLTU_pure bltu_input).nextPC) : OpEnvelope state m r_main
  -- ============================ BGEU (branch, no mem) ===================
  | bgeu
    (bgeu_input : PureSpec.BgeuInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bgeu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bgeu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bgeu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bgeu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bgeu_input.PC + BitVec.signExtend 64 bgeu_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGEU_pure bgeu_input).nextPC) : OpEnvelope state m r_main
  -- ============================ FENCE (no mem) ==========================
  | fence
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_fence : m.op r_main = OP_FLAG)
    (h_input_pc : state.regs.get? Register.PC = .some fence_input.PC)
    (h_input_priv :
      state.regs.get? Register.cur_privilege = .some Privilege.Machine)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_FENCE_pure fence_input).nextPC) : OpEnvelope state m r_main
  -- ============================ LUI (1 mem entry) =======================
  | lui
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20) (rd : regidx) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_lui : m.op r_main = OP_COPYB)
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    (h_input_imm : lui_input.imm = imm)
    (h_input_rd : lui_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some lui_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = lui_input.PC + 4#64)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_rd_idx : lui_input.rd = Transpiler.wrap_to_regidx e_rd.ptr) : OpEnvelope state m r_main
  -- ============================ AUIPC (1 mem entry) =====================
  | auipc
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20) (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_auipc : m.op r_main = OP_FLAG)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    (h_input_imm : auipc_input.imm = imm)
    (h_input_rd : auipc_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some auipc_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_AUIPC_pure auipc_input).nextPC = nextPC_val)
    (h_rd_idx : auipc_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) : OpEnvelope state m r_main
  -- ============================ JAL (1 mem entry) =======================
  | jal
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21) (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_jal : m.op r_main = OP_FLAG)
    (h_jal_subset : ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_success : (PureSpec.execute_JAL_pure jal_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val)
    (h_rd_idx : jal_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) : OpEnvelope state m r_main
  -- ============================ JALR (1 mem entry, do-block) ============
  | jalr
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12) (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_jalr : m.op r_main = OP_COPYB)
    (h_jalr_subset :
      ZiskFv.Tactics.JumpArchetype.jalr_subset_holds m r_main next_pc)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rd : jalr_input.rd = regidx_to_fin rd)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_input_pc : state.regs.get? Register.PC = .some jalr_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_success : (PureSpec.execute_JALR_pure jalr_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val)
    (h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) : OpEnvelope state m r_main
  -- ============================ ADD (3 mem entries, BinaryAdd) ==========
  | add
    (add_input : PureSpec.AddInput) (r1 r2 rd : regidx)
    (b : Valid_BinaryAdd C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_add : m.op r_main = OP_ADD)
    (h_main_subset : add_subset_holds m r_main)
    (h_b_core : ∀ r, ZiskFv.Airs.BinaryAdd.core_every_row b r)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok add_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok add_input.r2_val state)
    (h_input_rd : add_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some add_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_add_pure add_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : add_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ ADDI (do-block LHS, BinaryAdd) ==========
  | addi
    (addi_input : PureSpec.AddiInput) (r1 rd : regidx) (imm : BitVec 12)
    (b : Valid_BinaryAdd C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_addi : m.op r_main = OP_ADD)
    (h_main_subset : add_subset_holds m r_main)
    (h_b_core : ∀ r, ZiskFv.Airs.BinaryAdd.core_every_row b r)
    (h_addi_subset : itype_imm_subset_holds_main m r_main addi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addi_input.r1_val state)
    (h_input_imm : addi_input.imm = imm)
    (h_input_rd : addi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addi_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addi_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ ADDW (Binary, do-block) =================
  | addw
    (addw_input : PureSpec.AddwInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_addw : m.op r_main = OP_ADD_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok addw_input.r2_val state)
    (h_input_rd : addw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addw_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ SUBW (Binary, do-block) =================
  | subw
    (subw_input : PureSpec.SubwInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_subw : m.op r_main = OP_SUB_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok subw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok subw_input.r2_val state)
    (h_input_rd : subw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some subw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : subw_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ ADDIW (Binary, do-block, I-type) ========
  | addiw
    (addiw_input : PureSpec.AddiwInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_addiw : m.op r_main = OP_ADD_W)
    (h_addiw_subset : itype_imm_subset_holds_main m r_main addiw_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addiw_input.r1_val state)
    (h_input_imm : addiw_input.imm = imm)
    (h_input_rd : addiw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addiw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addiw_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ SUB (Binary, R-type) ====================
  | sub
    (sub_input : PureSpec.SubInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_sub : m.op r_main = OP_SUB)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sub_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sub_input.r2_val state)
    (h_input_rd : sub_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sub_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sub_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ AND (Binary, R-type) ====================
  | and_op
    (and_input : PureSpec.AndInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_and : m.op r_main = OP_AND)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok and_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok and_input.r2_val state)
    (h_input_rd : and_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some and_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_and_pure and_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : and_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ OR (Binary, R-type) =====================
  | or_op
    (or_input : PureSpec.OrInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_or : m.op r_main = OP_OR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok or_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok or_input.r2_val state)
    (h_input_rd : or_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some or_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_or_pure or_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : or_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ XOR (Binary, R-type) ====================
  | xor_op
    (xor_input : PureSpec.XorInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_xor : m.op r_main = OP_XOR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok xor_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok xor_input.r2_val state)
    (h_input_rd : xor_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some xor_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : xor_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ SLT (Binary, R-type) ====================
  | slt
    (slt_input : PureSpec.SltInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_slt : m.op r_main = OP_LT)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok slt_input.r2_val state)
    (h_input_rd : slt_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slt_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : slt_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ SLTU (Binary, R-type) ===================
  | sltu
    (sltu_input : PureSpec.SltuInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_sltu : m.op r_main = OP_LTU)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sltu_input.r2_val state)
    (h_input_rd : sltu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sltu_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ ANDI (Binary, I-type) ===================
  | andi
    (andi_input : PureSpec.AndiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_andi : m.op r_main = OP_AND)
    (h_andi_subset : itype_imm_subset_holds_main m r_main andi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok andi_input.r1_val state)
    (h_input_imm : andi_input.imm = imm)
    (h_input_rd : andi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some andi_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : andi_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ ORI (Binary, I-type) ====================
  | ori
    (ori_input : PureSpec.OriInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_ori : m.op r_main = OP_OR)
    (h_ori_subset : itype_imm_subset_holds_main m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok ori_input.r1_val state)
    (h_input_imm : ori_input.imm = imm)
    (h_input_rd : ori_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some ori_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : ori_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ XORI (Binary, I-type) ===================
  | xori
    (xori_input : PureSpec.XoriInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_xori : m.op r_main = OP_XOR)
    (h_xori_subset : itype_imm_subset_holds_main m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok xori_input.r1_val state)
    (h_input_imm : xori_input.imm = imm)
    (h_input_rd : xori_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some xori_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : xori_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ SLTI (Binary, I-type) ===================
  | slti
    (slti_input : PureSpec.SltiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_slti : m.op r_main = OP_LT)
    (h_slti_subset : itype_imm_subset_holds_main m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slti_input.r1_val state)
    (h_input_imm : slti_input.imm = imm)
    (h_input_rd : slti_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slti_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : slti_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ SLTIU (Binary, I-type) ==================
  | sltiu
    (sltiu_input : PureSpec.SltiuInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_sltiu : m.op r_main = OP_LTU)
    (h_sltiu_subset : itype_imm_subset_holds_main m r_main sltiu_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltiu_input.r1_val state)
    (h_input_imm : sltiu_input.imm = imm)
    (h_input_rd : sltiu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltiu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sltiu_input.rd = Transpiler.wrap_to_regidx e2.ptr) : OpEnvelope state m r_main
  -- ============================ SB (store, Main-only) ===================
  | sb
    (sb_input : PureSpec.SbInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op : m.op r_main = OP_COPYB)
    (h_main_ind_width : m.ind_width r_main = 1)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sb_state_assumptions sb_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREB_pure sb_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) : OpEnvelope state m r_main

namespace OpEnvelope

variable
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {m : Valid_Main C FGL FGL} {r_main : ℕ}

/-- The op-kind this envelope corresponds to. -/
def kind : OpEnvelope state m r_main → mainOpKind
  | .beq ..  => .EQ      -- branches don't have a single mainOpKind arm;
                          -- but the dispatcher pins `m.op r_main` via
                          -- the wrapper rather than a kind hypothesis,
                          -- so we map all six branches to `.EQ` (Zisk
                          -- has no separate op for branches; they all
                          -- live under is_external_op = 0 with op = ?
                          -- — see Main's PIL for the exact encoding).
                          -- NOTE: this routing-only choice has no
                          -- soundness implication; the dispatcher's
                          -- conclusion does not depend on `kind`.
  | .bne ..   => .EQ
  | .blt ..   => .EQ
  | .bge ..   => .EQ
  | .bltu ..  => .EQ
  | .bgeu ..  => .EQ
  | .fence .. => .FLAG
  | .lui ..   => .COPYB
  | .auipc .. => .FLAG
  | .jal ..   => .FLAG
  | .jalr ..  => .COPYB
  | .add ..   => .ADD
  | .addi ..  => .ADD
  | .addw ..  => .ADD_W
  | .subw ..  => .SUB_W
  | .addiw .. => .ADD_W
  | .sub ..   => .SUB
  | .and_op .. => .AND
  | .or_op ..  => .OR
  | .xor_op .. => .XOR
  | .slt ..    => .LT
  | .sltu ..   => .LTU
  | .andi ..   => .AND
  | .ori ..    => .OR
  | .xori ..   => .XOR
  | .slti ..   => .LT
  | .sltiu ..  => .LTU
  | .sb ..    => .COPYB

/-- The dispatcher's conclusion as a `Prop`. -/
def exec_eq : OpEnvelope state m r_main → Prop
  | .beq _ imm r1 r2 _ exec_row .. =>
      execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
        = (bus_effect exec_row [] state).2
  | .bne _ imm r1 r2 _ exec_row .. =>
      execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
        = (bus_effect exec_row [] state).2
  | .blt _ imm r1 r2 _ exec_row .. =>
      execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
        = (bus_effect exec_row [] state).2
  | .bge _ imm r1 r2 _ exec_row .. =>
      execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGE)) state
        = (bus_effect exec_row [] state).2
  | .bltu _ imm r1 r2 _ exec_row .. =>
      execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
        = (bus_effect exec_row [] state).2
  | .bgeu _ imm r1 r2 _ exec_row .. =>
      execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGEU)) state
        = (bus_effect exec_row [] state).2
  | .fence _ fm pred succ rs rd exec_row .. =>
      execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
        = (bus_effect exec_row [] state).2
  | .lui _ imm rd _ exec_row e_rd .. =>
      execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
        = (bus_effect exec_row [e_rd] state).2
  | .auipc _ imm rd exec_row e_rd .. =>
      execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
        = (bus_effect exec_row [e_rd] state).2
  | .jal _ imm rd _ _ exec_row e_rd .. =>
      execute_instruction (instruction.JAL (imm, rd)) state
        = (bus_effect exec_row [e_rd] state).2
  | .jalr _ imm rs1 rd _ _ exec_row e_rd .. =>
      (do
          Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
          LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
        = (bus_effect exec_row [e_rd] state).2
  | .add _ r1 r2 rd _ exec_row e0 e1 e2 .. =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .addi _ r1 rd imm _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .addw _ r1 r2 rd _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .subw _ r1 r2 rd _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .addiw _ r1 rd imm _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ADDIW (imm, r1, rd))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .sub _ r1 r2 rd _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .and_op _ r1 r2 rd _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.AND))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .or_op _ r1 r2 rd _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.OR))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .xor_op _ r1 r2 rd _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.XOR))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .slt _ r1 r2 rd _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .sltu _ r1 r2 rd _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .andi _ r1 rd imm _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .ori _ r1 rd imm _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .xori _ r1 rd imm _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .slti _ r1 rd imm _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .sltiu _ r1 rd imm _ exec_row e0 e1 e2 .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
        = (bus_effect exec_row [e0, e1, e2] state).2
  | .sb sb_input _ _ _ _ exec_row e0 e1 e2 .. =>
      execute_instruction (instruction.STORE (
        sb_input.imm,
        regidx.Regidx sb_input.r2,
        regidx.Regidx sb_input.r1,
        1
      )) state = (bus_effect exec_row [e0, e1, e2] state).2

end OpEnvelope

/-! ## The global theorem (representative slice)

For each constructor of `OpEnvelope`, dispatch to the corresponding
`dispatch_<OP>` theorem. The proof is one `match` arm per op,
delegating verbatim. -/

/-- **Global compliance theorem (representative slice).**

    Given an op-envelope packaging all the inputs and hypotheses the
    corresponding `dispatch_<OP>` theorem requires, the envelope's
    declared conclusion (`exec_eq`) holds.

    The conclusion's shape is determined by the envelope's
    constructor, so the global theorem is a 6-way (here) / 35-way
    (full) routing match.

    Soundness is inherited from the dispatchers; the dispatchers
    delegate to the 63 `equiv_<OP>_from_trust` wrappers; the wrappers
    consume the 147-axiom trust ledger. This theorem adds zero new
    trust. -/
theorem zisk_riscv_compliant_program_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (env : OpEnvelope (C := C) state m r_main) :
    env.exec_eq := by
  cases env with
  | beq beq_input imm r1 r2 misa_val exec_row
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
        h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_BEQ state beq_input imm r1 r2 misa_val exec_row
      h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
      h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
  | bne bne_input imm r1 r2 misa_val exec_row
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
        h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_BNE state bne_input imm r1 r2 misa_val exec_row
      h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
      h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
  | blt blt_input imm r1 r2 misa_val exec_row
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
        h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_BLT state blt_input imm r1 r2 misa_val exec_row
      h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
      h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
  | bge bge_input imm r1 r2 misa_val exec_row
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
        h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_BGE state bge_input imm r1 r2 misa_val exec_row
      h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
      h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
  | bltu bltu_input imm r1 r2 misa_val exec_row
         h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
         h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_BLTU state bltu_input imm r1 r2 misa_val exec_row
      h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
      h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
  | bgeu bgeu_input imm r1 r2 misa_val exec_row
         h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
         h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_BGEU state bgeu_input imm r1 r2 misa_val exec_row
      h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
      h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
  | fence fence_input fm pred succ rs rd exec_row
          h_main_active h_main_op_fence h_input_pc h_input_priv
          h_exec_len h_e0_mult h_e1_mult h_nextPC_matches =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_FENCE state fence_input fm pred succ rs rd m r_main
      exec_row h_main_active h_main_op_fence h_input_pc h_input_priv
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
  | lui lui_input imm rd next_pc exec_row e_rd
        h_main_active h_main_op_lui h_lui_subset
        h_input_imm h_input_rd h_input_pc
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_rd_mult h_rd_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_LUI state lui_input imm rd m r_main next_pc
      exec_row e_rd h_main_active h_main_op_lui h_lui_subset
      h_input_imm h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_rd_mult h_rd_as h_rd_idx
  | auipc auipc_input imm rd exec_row e_rd nextPC_val next_pc
          h_main_active h_main_op_auipc h_auipc_subset
          h_input_imm h_input_rd h_input_pc
          h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
          h_rd_mult h_rd_as h_nextPC_eq h_rd_idx
          h_no_wrap h_lo_bound h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_AUIPC state auipc_input imm rd exec_row e_rd nextPC_val
      m r_main next_pc h_main_active h_main_op_auipc h_auipc_subset
      h_input_imm h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_rd_mult h_rd_as h_nextPC_eq h_rd_idx
      h_no_wrap h_lo_bound h_pc_offset_lt_2_32
  | jal jal_input imm rd misa_val next_pc exec_row e_rd nextPC_val
        h_main_active h_main_op_jal h_jal_subset
        h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_rd_mult h_rd_as h_not_throws h_success h_nextPC_option h_rd_idx
        h_pc_bound h_lo_bound h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_JAL state jal_input imm rd misa_val m r_main next_pc
      exec_row e_rd nextPC_val h_main_active h_main_op_jal h_jal_subset
      h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_rd_mult h_rd_as h_not_throws h_success h_nextPC_option h_rd_idx
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
  | jalr jalr_input imm rs1 rd misa_val mseccfg exec_row e_rd nextPC_val next_pc
         h_main_active h_main_op_jalr h_jalr_subset
         h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
         h_cur_privilege h_mseccfg
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_rd_mult h_rd_as h_success h_nextPC_option h_rd_idx
         h_pc_bound h_lo_bound h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_JALR state jalr_input imm rs1 rd misa_val mseccfg
      exec_row e_rd nextPC_val m r_main next_pc
      h_main_active h_main_op_jalr h_jalr_subset
      h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
      h_cur_privilege h_mseccfg
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_rd_mult h_rd_as h_success h_nextPC_option h_rd_idx
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
  | add add_input r1 r2 rd b exec_row e0 e1 e2
        h_main_active h_main_op_add h_main_subset h_b_core h_lane_rd
        h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_ADD state add_input r1 r2 rd m b r_main exec_row e0 e1 e2
      h_main_active h_main_op_add h_main_subset h_b_core h_lane_rd
      h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | addi addi_input r1 rd imm b exec_row e0 e1 e2
         h_main_active h_main_op_addi h_main_subset h_b_core h_addi_subset h_lane_rd
         h_input_r1 h_input_imm h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_ADDI state addi_input r1 rd imm m b r_main exec_row e0 e1 e2
      h_main_active h_main_op_addi h_main_subset h_b_core h_addi_subset h_lane_rd
      h_input_r1 h_input_imm h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | addw addw_input r1 r2 rd v exec_row e0 e1 e2
         h_main_active h_main_op_addw h_lane_rd
         h_input_r1 h_input_r2 h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_ADDW state addw_input r1 r2 rd m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_addw h_lane_rd
      h_input_r1 h_input_r2 h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | subw subw_input r1 r2 rd v exec_row e0 e1 e2
         h_main_active h_main_op_subw h_lane_rd
         h_input_r1 h_input_r2 h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_SUBW state subw_input r1 r2 rd m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_subw h_lane_rd
      h_input_r1 h_input_r2 h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | addiw addiw_input r1 rd imm v exec_row e0 e1 e2
          h_main_active h_main_op_addiw h_addiw_subset h_lane_rd
          h_input_r1 h_input_imm h_input_rd h_input_pc
          h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
          h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_ADDIW state addiw_input r1 rd imm m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_addiw h_addiw_subset h_lane_rd
      h_input_r1 h_input_imm h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | sub sub_input r1 r2 rd v exec_row e0 e1 e2
        h_main_active h_main_op_sub h_lane_rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_SUB state sub_input r1 r2 rd m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_sub h_lane_rd
      h_input_r1 h_input_r2 h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | and_op and_input r1 r2 rd v exec_row e0 e1 e2
           h_main_active h_main_op_and h_lane_rd
           h_input_r1 h_input_r2 h_input_rd h_input_pc
           h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
           h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_AND state and_input r1 r2 rd m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_and h_lane_rd
      h_input_r1 h_input_r2 h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | or_op or_input r1 r2 rd v exec_row e0 e1 e2
          h_main_active h_main_op_or h_lane_rd
          h_input_r1 h_input_r2 h_input_rd h_input_pc
          h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
          h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_OR state or_input r1 r2 rd m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_or h_lane_rd
      h_input_r1 h_input_r2 h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | xor_op xor_input r1 r2 rd v exec_row e0 e1 e2
           h_main_active h_main_op_xor h_lane_rd
           h_input_r1 h_input_r2 h_input_rd h_input_pc
           h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
           h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_XOR state xor_input r1 r2 rd m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_xor h_lane_rd
      h_input_r1 h_input_r2 h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | slt slt_input r1 r2 rd v exec_row e0 e1 e2
        h_main_active h_main_op_slt h_lane_rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_SLT state slt_input r1 r2 rd m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_slt h_lane_rd
      h_input_r1 h_input_r2 h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | sltu sltu_input r1 r2 rd v exec_row e0 e1 e2
         h_main_active h_main_op_sltu h_lane_rd
         h_input_r1 h_input_r2 h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_SLTU state sltu_input r1 r2 rd m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_sltu h_lane_rd
      h_input_r1 h_input_r2 h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | andi andi_input r1 rd imm v exec_row e0 e1 e2
         h_main_active h_main_op_andi h_andi_subset h_lane_rd
         h_input_r1 h_input_imm h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_ANDI state andi_input r1 rd imm m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_andi h_andi_subset h_lane_rd
      h_input_r1 h_input_imm h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | ori ori_input r1 rd imm v exec_row e0 e1 e2
        h_main_active h_main_op_ori h_ori_subset h_lane_rd
        h_input_r1 h_input_imm h_input_rd h_input_pc
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_ORI state ori_input r1 rd imm m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_ori h_ori_subset h_lane_rd
      h_input_r1 h_input_imm h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | xori xori_input r1 rd imm v exec_row e0 e1 e2
         h_main_active h_main_op_xori h_xori_subset h_lane_rd
         h_input_r1 h_input_imm h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_XORI state xori_input r1 rd imm m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_xori h_xori_subset h_lane_rd
      h_input_r1 h_input_imm h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | slti slti_input r1 rd imm v exec_row e0 e1 e2
         h_main_active h_main_op_slti h_slti_subset h_lane_rd
         h_input_r1 h_input_imm h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_SLTI state slti_input r1 rd imm m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_slti h_slti_subset h_lane_rd
      h_input_r1 h_input_imm h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | sltiu sltiu_input r1 rd imm v exec_row e0 e1 e2
          h_main_active h_main_op_sltiu h_sltiu_subset h_lane_rd
          h_input_r1 h_input_imm h_input_rd h_input_pc
          h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
          h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_SLTIU state sltiu_input r1 rd imm m v r_main exec_row e0 e1 e2
      h_main_active h_main_op_sltiu h_sltiu_subset h_lane_rd
      h_input_r1 h_input_imm h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
  | sb sb_input mstatus pmaRegion misa mseccfg exec_row e0 e1 e2
       h_main_active h_main_op h_main_ind_width
       risc_v_assumptions h_opcode_assumptions
       h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
       h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as =>
    simp only [OpEnvelope.exec_eq]
    exact dispatch_SB state sb_input mstatus pmaRegion misa mseccfg
      m r_main exec_row e0 e1 e2
      h_main_active h_main_op h_main_ind_width
      risc_v_assumptions h_opcode_assumptions
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

end ZiskFv.Equivalence.Compliance.Global
