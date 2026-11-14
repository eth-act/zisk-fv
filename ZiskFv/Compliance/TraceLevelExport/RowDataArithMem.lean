import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.Pilot.SubNextPC
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
import ZiskFv.Compliance.ConstructionDiv
import ZiskFv.Compliance.ConstructionDivuw
import ZiskFv.Compliance.ConstructionRemu
import ZiskFv.Compliance.ConstructionRemuw
import ZiskFv.Compliance.ConstructionStore
import ZiskFv.Compliance.ConstructionLoad
import ZiskFv.Compliance.ConstructionBranch
import ZiskFv.Compliance.ConstructionJump
import ZiskFv.Compliance
import ZiskFv.Compliance.Defects
import ZiskFv.Compliance.TraceLevelExport.Base

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

/-- AUIPC theorem-domain range assumptions.

These are explicit soundness-domain conditions, not decoded placement facts or Sail/ZisK value
agreement. Keeping them separate from `Inputs_auipc` leaves the input record focused on state and
value agreement while preserving the same AUIPC range obligations at the theorem boundary. -/
structure AuipcRangeDomain (auipc_input : PureSpec.AuipcInput) : Prop where
  h_pc_bound : auipc_input.PC.toNat < GL_prime - 4
  h_target_nonneg : 0 ≤ (auipc_input.PC.toNat : Int)
    + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toInt
  h_target_lt : (auipc_input.PC.toNat : Int)
    + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toInt < GL_prime
  h_pc_offset_lt_2_32 :
    (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
      < 4294967296

/-- **`RTypePromises` minus derived next-PC and rd-placement fields (#100/#141).**

    Identical to `ZiskFv.EquivCore.Promises.RTypePromises` except that the
    `pure_nextPC` parameter and the `nextPC_matches : (register_type_pc_equiv ▸
    BitVec.ofNat 64 (exec_row[1]!.pc).val) = pure_nextPC` field are dropped, and
    the rd-write placement field `rd_idx` is also dropped.

    The next-PC promise is no longer caller-supplied for the bundle-shaped
    signed-M opcodes (MUL/MULH/MULHSU/DIV/REM/DIVW/REMW): it is DERIVED in the
    `<op>EnvOf` env-builder from the accepted trace's in-circuit `pcHandshakeBetween`
    transition certificate via `Pilot.sequential_nextPC_discharged` (the same
    kernel-only discharge the 56 already-rewired ops use) and re-attached through
    `withNextPC`. The rd-placement promise is likewise DERIVED in `<op>EnvOf`
    from the decoded ROM/Main `store_ind`/`store_offset` facts plus `AddressSpec`.

    Lives here, next to its only consumers (the signed-M `Inputs_<op>` /
    `<op>EnvOf`), rather than in `EquivCore/Promises/RType.lean`, to avoid a
    tree-wide rebuild of the ~250 files downstream of that foundational module. -/
structure RTypePromisesNoNextPC
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (input_r1_val input_r2_val : BitVec 64) (input_rd : Fin 32)
    (input_pc : BitVec 64)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL) where
  input_r1_eq : read_xreg (regidx_to_fin r1) state
    = EStateM.Result.ok input_r1_val state
  input_r2_eq : read_xreg (regidx_to_fin r2) state
    = EStateM.Result.ok input_r2_val state
  input_rd_eq : input_rd = regidx_to_fin rd
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
  exec_len : exec_row.length = 2
  e0_mult : exec_row[0]!.multiplicity = -1
  e1_mult : exec_row[1]!.multiplicity = 1
  m0_mult : e0.multiplicity = -1
  m0_as : e0.as.val = 1
  m1_mult : e1.multiplicity = -1
  m1_as : e1.as.val = 1
  m2_mult : e2.multiplicity = 1
  m2_as : e2.as.val = 1

/-- Re-attach discharged next-PC and rd-placement facts to a `RTypePromisesNoNextPC`
    bundle, recovering the full `RTypePromises`. The `h_nextPC` proof is sourced in
    `<op>EnvOf` from `Pilot.sequential_nextPC_discharged`; the `h_rd_idx` proof is
    sourced there from the decoded writeback destination and `AddressSpec`. -/
def RTypePromisesNoNextPC.withNextPC
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {input_r1_val input_r2_val : BitVec 64} {input_rd : Fin 32}
    {input_pc : BitVec 64} {r1 r2 rd : regidx}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    {e0 e1 e2 : Interaction.MemoryBusEntry FGL}
    (p : RTypePromisesNoNextPC state input_r1_val input_r2_val input_rd input_pc
      r1 r2 rd exec_row e0 e1 e2)
    (pure_nextPC : BitVec 64)
    (h_nextPC :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val)) = pure_nextPC)
    (h_rd_idx : input_rd = Transpiler.wrap_to_regidx e2.ptr) :
    ZiskFv.EquivCore.Promises.RTypePromises state input_r1_val input_r2_val input_rd
      input_pc pure_nextPC r1 r2 rd exec_row e0 e1 e2 where
  input_r1_eq := p.input_r1_eq
  input_r2_eq := p.input_r2_eq
  input_rd_eq := p.input_rd_eq
  input_pc_eq := p.input_pc_eq
  exec_len := p.exec_len
  e0_mult := p.e0_mult
  e1_mult := p.e1_mult
  nextPC_matches := h_nextPC
  m0_mult := p.m0_mult
  m0_as := p.m0_as
  m1_mult := p.m1_mult
  m1_as := p.m1_as
  m2_mult := p.m2_mult
  m2_as := p.m2_as
  rd_idx := h_rd_idx

structure Claim_add (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_add (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_add trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide ((regidx_to_fin c.rd).val ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  h_a_src_reg :
    (mainRowWithRomSub trace i).rom.a_src_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r1 ≠ 0))
  h_a_offset_imm0 :
    (mainRowWithRomSub trace i).rom.a_offset_imm0 =
      Transpiler.ind (regidx_to_fin c.r1)
  h_a_src_imm :
    (mainRowWithRomSub trace i).rom.a_src_imm =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r1 = 0))
  h_a_imm1 :
    (mainRowWithRomSub trace i).rom.a_imm1 = 0
  h_b_src_reg :
    (mainRowWithRomSub trace i).rom.b_src_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r2 ≠ 0))
  h_b_offset_imm0 :
    (mainRowWithRomSub trace i).rom.b_offset_imm0 =
      Transpiler.ind (regidx_to_fin c.r2)
  h_b_src_imm :
    (mainRowWithRomSub trace i).rom.b_src_imm =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r2 = 0))
  h_b_imm1 :
    (mainRowWithRomSub trace i).rom.b_imm1 = 0

structure InputsCore_add (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_add trace i) : Type where
  add_input : PureSpec.AddInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok add_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok add_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some add_input.PC
  h_input_rd : add_input.rd = regidx_to_fin c.rd

/-- The PC agreement `Inputs_add` carries on top of `InputsCore_add`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_add (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_add trace i) : Type extends InputsCore_add trace binding i c where
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = add_input.PC.toNat

/-- Per-op residual bundle for the `add` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_add` bundles them. -/
structure RowData_add
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_add trace i
  toDecode : Decode_add trace i toClaim
  toInputs : Inputs_add trace binding i toClaim

def toRowData_add {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_add trace i) (dec : Decode_add trace i c)
    (ia : Inputs_add trace binding i c) : RowData_add trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_addi (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_addi (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addi trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide ((regidx_to_fin c.rd).val ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  h_a_src_reg :
    (mainRowWithRomSub trace i).rom.a_src_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r1 ≠ 0))
  h_a_offset_imm0 :
    (mainRowWithRomSub trace i).rom.a_offset_imm0 =
      Transpiler.ind (regidx_to_fin c.r1)
  h_a_src_imm :
    (mainRowWithRomSub trace i).rom.a_src_imm =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r1 = 0))
  h_a_imm1 :
    (mainRowWithRomSub trace i).rom.a_imm1 = 0
  h_b_src_imm :
    (mainRowWithRomSub trace i).rom.b_src_imm = 1
  h_b_imm :
    BitVec.signExtend 64 c.imm =
      BitVec.ofNat 64
        (((mainRowWithRomSub trace i).rom.b_offset_imm0).val
          + ((mainRowWithRomSub trace i).rom.b_imm1).val * 4294967296)

structure InputsCore_addi (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addi trace i) : Type where
  addi_input : PureSpec.AddiInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok addi_input.r1_val (binding i)
  h_input_imm : addi_input.imm = c.imm
  h_input_pc : (binding i).regs.get? Register.PC = .some addi_input.PC
  h_input_rd : addi_input.rd = regidx_to_fin c.rd

/-- The PC agreement `Inputs_addi` carries on top of `InputsCore_addi`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_addi (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addi trace i) : Type extends InputsCore_addi trace binding i c where
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = addi_input.PC.toNat

/-- Per-op residual bundle for the `addi` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_addi` bundles them. -/
structure RowData_addi
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_addi trace i
  toDecode : Decode_addi trace i toClaim
  toInputs : Inputs_addi trace binding i toClaim

def toRowData_addi {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_addi trace i) (dec : Decode_addi trace i c)
    (ia : Inputs_addi trace binding i c) : RowData_addi trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_subw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_subw (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_subw trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SUB_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  h_a_src_reg :
    (mainRowWithRomSub trace i).rom.a_src_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r1 ≠ 0))
  h_a_offset_imm0 :
    (mainRowWithRomSub trace i).rom.a_offset_imm0 =
      Transpiler.ind (regidx_to_fin c.r1)
  h_a_src_imm :
    (mainRowWithRomSub trace i).rom.a_src_imm =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r1 = 0))
  h_a_imm1 :
    (mainRowWithRomSub trace i).rom.a_imm1 = 0
  h_b_src_reg :
    (mainRowWithRomSub trace i).rom.b_src_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r2 ≠ 0))
  h_b_offset_imm0 :
    (mainRowWithRomSub trace i).rom.b_offset_imm0 =
      Transpiler.ind (regidx_to_fin c.r2)
  h_b_src_imm :
    (mainRowWithRomSub trace i).rom.b_src_imm =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r2 = 0))
  h_b_imm1 :
    (mainRowWithRomSub trace i).rom.b_imm1 = 0

structure InputsCore_subw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_subw trace i) : Type where
  subw_input : PureSpec.SubwInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok subw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok subw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some subw_input.PC
  h_input_rd : subw_input.rd = regidx_to_fin c.rd

/-- The PC agreement `Inputs_subw` carries on top of `InputsCore_subw`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_subw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_subw trace i) : Type extends InputsCore_subw trace binding i c where
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = subw_input.PC.toNat

/-- Per-op residual bundle for the `subw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_subw` bundles them. -/
structure RowData_subw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_subw trace i
  toDecode : Decode_subw trace i toClaim
  toInputs : Inputs_subw trace binding i toClaim

def toRowData_subw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_subw trace i) (dec : Decode_subw trace i c)
    (ia : Inputs_subw trace binding i c) : RowData_subw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_addw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_addw (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addw trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  h_a_src_reg :
    (mainRowWithRomSub trace i).rom.a_src_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r1 ≠ 0))
  h_a_offset_imm0 :
    (mainRowWithRomSub trace i).rom.a_offset_imm0 =
      Transpiler.ind (regidx_to_fin c.r1)
  h_a_src_imm :
    (mainRowWithRomSub trace i).rom.a_src_imm =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r1 = 0))
  h_a_imm1 :
    (mainRowWithRomSub trace i).rom.a_imm1 = 0
  h_b_src_reg :
    (mainRowWithRomSub trace i).rom.b_src_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r2 ≠ 0))
  h_b_offset_imm0 :
    (mainRowWithRomSub trace i).rom.b_offset_imm0 =
      Transpiler.ind (regidx_to_fin c.r2)
  h_b_src_imm :
    (mainRowWithRomSub trace i).rom.b_src_imm =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r2 = 0))
  h_b_imm1 :
    (mainRowWithRomSub trace i).rom.b_imm1 = 0

structure InputsCore_addw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addw trace i) : Type where
  addw_input : PureSpec.AddwInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok addw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok addw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some addw_input.PC
  h_input_rd : addw_input.rd = regidx_to_fin c.rd

/-- The PC agreement `Inputs_addw` carries on top of `InputsCore_addw`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_addw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addw trace i) : Type extends InputsCore_addw trace binding i c where
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = addw_input.PC.toNat

/-- Per-op residual bundle for the `addw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_addw` bundles them. -/
structure RowData_addw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_addw trace i
  toDecode : Decode_addw trace i toClaim
  toInputs : Inputs_addw trace binding i toClaim

def toRowData_addw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_addw trace i) (dec : Decode_addw trace i c)
    (ia : Inputs_addw trace binding i c) : RowData_addw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_addiw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_addiw (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addiw trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_ADD_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide ((regidx_to_fin c.rd).val ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  h_a_src_reg :
    (mainRowWithRomSub trace i).rom.a_src_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r1 ≠ 0))
  h_a_offset_imm0 :
    (mainRowWithRomSub trace i).rom.a_offset_imm0 =
      Transpiler.ind (regidx_to_fin c.r1)
  h_a_src_imm :
    (mainRowWithRomSub trace i).rom.a_src_imm =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.r1 = 0))
  h_a_imm1 :
    (mainRowWithRomSub trace i).rom.a_imm1 = 0
  h_b_src_imm :
    (mainRowWithRomSub trace i).rom.b_src_imm = 1
  h_b_imm :
    BitVec.signExtend 64 c.imm =
      BitVec.ofNat 64
        (((mainRowWithRomSub trace i).rom.b_offset_imm0).val
          + ((mainRowWithRomSub trace i).rom.b_imm1).val * 4294967296)

structure InputsCore_addiw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addiw trace i) : Type where
  addiw_input : PureSpec.AddiwInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok addiw_input.r1_val (binding i)
  h_input_imm : addiw_input.imm = c.imm
  h_input_pc : (binding i).regs.get? Register.PC = .some addiw_input.PC
  h_input_rd : addiw_input.rd = regidx_to_fin c.rd

/-- The PC agreement `Inputs_addiw` carries on top of `InputsCore_addiw`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_addiw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addiw trace i) : Type extends InputsCore_addiw trace binding i c where
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = addiw_input.PC.toNat

/-- Per-op residual bundle for the `addiw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_addiw` bundles them. -/
structure RowData_addiw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_addiw trace i
  toDecode : Decode_addiw trace i toClaim
  toInputs : Inputs_addiw trace binding i toClaim

def toRowData_addiw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_addiw trace i) (dec : Decode_addiw trace i c)
    (ia : Inputs_addiw trace binding i c) : RowData_addiw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_lui (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 20
  rd : regidx

structure Decode_lui (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lui trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_store_ind :
    (mainRowWithRomLui trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomLui trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide ((regidx_to_fin c.rd).val ≠ 0))
  h_store_offset :
    (mainRowWithRomLui trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  h_imm_lo_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val).val
      = (c.imm ++ (0 : BitVec 12)).toNat
  h_imm_hi_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val).val
      = (BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toNat / 4294967296
  -- #100 next-PC transition inputs (replace the exec artifacts; LUI already
  -- carries h_set_pc above): the next row exists, plus the COPYB LUI-row
  -- jmp pins `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`;
  -- cf. `RowShape/Contract.lean` LUI arm, line 710). With set_pc=0 and
  -- jmp1=jmp2=4 the handshake mux collapses to pc+4 regardless of `flag`.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4

structure InputsCore_lui (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lui trace i) : Type where
  lui_input : PureSpec.LuiInput
  h_input_imm : lui_input.imm = c.imm
  h_input_rd : lui_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some lui_input.PC

/-- The PC agreement `Inputs_lui` carries on top of `InputsCore_lui`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_lui (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lui trace i) : Type extends InputsCore_lui trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = lui_input.PC.toNat

/-- Per-op residual bundle for the `lui` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_lui` bundles them. -/
structure RowData_lui
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_lui trace i
  toDecode : Decode_lui trace i toClaim
  toInputs : Inputs_lui trace binding i toClaim

def toRowData_lui {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_lui trace i) (dec : Decode_lui trace i c)
    (ia : Inputs_lui trace binding i c) : RowData_lui trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_auipc (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  imm : BitVec 20
  rd : regidx

structure Decode_auipc (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_auipc trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_FLAG
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 1
  h_store_ind :
    (mainRowWithRomLui trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomLui trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide ((regidx_to_fin c.rd).val ≠ 0))
  h_store_offset :
    (mainRowWithRomLui trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  h_jmp_offset2_imm :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
        i.val)
      = ((BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toInt : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts; AUIPC already
  -- carries h_set_pc above): the next row exists, plus the AUIPC FLAG-row jmp
  -- pin `jmp_offset1 = 4` and committed-program `jmp_offset2 = signExtend imm`
  -- (Rust lowerer `zib.j(4, imm)`; cf. `RowShape/Contract.lean` AUIPC arm). With set_pc=0 and flag=1
  -- the handshake mux selects the taken offset `jmp_offset1 = 4`, so
  -- next_pc = pc + 4. `flag = 1` is NOT pinned here: it is derived in
  -- `stepStrong_auipc` from the OP_FLAG decode pins + `internal_op0_sets_flag`.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4

structure InputsCore_auipc (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_auipc trace i) : Type where
  auipc_input : PureSpec.AuipcInput
  h_input_imm : auipc_input.imm = c.imm
  h_input_rd : auipc_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some auipc_input.PC
  -- #100: PC bridge. The AUIPC range/domain facts live in `RowOutsideDefectRegion`
  -- as `AuipcRangeDomain`.

/-- The PC agreement `Inputs_auipc` carries on top of `InputsCore_auipc`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_auipc (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_auipc trace i) : Type extends InputsCore_auipc trace binding i c where
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = auipc_input.PC.toNat

/-- Per-op residual bundle for the `auipc` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_auipc` bundles them. -/
structure RowData_auipc
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_auipc trace i
  toDecode : Decode_auipc trace i toClaim
  toInputs : Inputs_auipc trace binding i toClaim

def toRowData_auipc {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_auipc trace i) (dec : Decode_auipc trace i c)
    (ia : Inputs_auipc trace binding i c) : RowData_auipc trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_mulw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_mulw (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulw trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 1
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure InputsCore_mulw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulw trace i) : Type where
  mulw_input : PureSpec.MulwInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok mulw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok mulw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some mulw_input.PC
  h_input_rd : mulw_input.rd = regidx_to_fin c.rd
  h_a23 :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W),
    ((vOfMulwRow (mulwArow trace binding i ha ho)).a_2 0).val = 0
      ∧ ((vOfMulwRow (mulwArow trace binding i ha ho)).a_3 0).val = 0
  h_b23 :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W),
    ((vOfMulwRow (mulwArow trace binding i ha ho)).b_2 0).val = 0
      ∧ ((vOfMulwRow (mulwArow trace binding i ha ho)).b_3 0).val = 0
  h_sext_choice :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W),
    ((((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 4).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 5).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 6).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 7).val = 0)
        ∧ ((vOfMulwRow (mulwArow trace binding i ha ho)).c_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i ha ho)).c_1 0).val * 65536
              < 2147483648)
      ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 4).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 5).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 6).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 7).val = 255)
        ∧ ((vOfMulwRow (mulwArow trace binding i ha ho)).c_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i ha ho)).c_1 0).val * 65536
              ≥ 2147483648))
  h_rs1_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W),
    (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
      = (((vOfMulwRow (mulwArow trace binding i ha ho)).a_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i ha ho)).a_1 0).val * 65536 : ℤ)
          - ((vOfMulwRow (mulwArow trace binding i ha ho)).na 0).val * (2:ℤ)^32
  h_rs2_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W),
    (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
      = (((vOfMulwRow (mulwArow trace binding i ha ho)).b_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i ha ho)).b_1 0).val * 65536 : ℤ)
          - ((vOfMulwRow (mulwArow trace binding i ha ho)).nb 0).val * (2:ℤ)^32

/-- The PC agreement `Inputs_mulw` carries on top of `InputsCore_mulw`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_mulw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulw trace i) : Type extends InputsCore_mulw trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = mulw_input.PC.toNat

/-- Per-op residual bundle for the `mulw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_mulw` bundles them. -/
structure RowData_mulw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_mulw trace i
  toDecode : Decode_mulw trace i toClaim
  toInputs : Inputs_mulw trace binding i toClaim

def toRowData_mulw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_mulw trace i) (dec : Decode_mulw trace i c)
    (ia : Inputs_mulw trace binding i c) : RowData_mulw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_mul (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  srs1 : Signedness
  srs2 : Signedness

structure Decode_mul (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mul trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  -- #100 next-PC transition input: the next Main row exists (so the cross-row
  -- `pcHandshakeBetween` transition applies at the pair `(i, i+1)`). Together with
  -- the decode pins `set_pc = 0`, `jmp_offset1 = jmp_offset2 = 4` already above,
  -- this lets `<op>EnvOf` DERIVE the bundled `nextPC_matches` rather than take it
  -- from the caller. Terminal row = #103 cross-segment boundary.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure InputsCore_mul (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mul trace i) : Type where
  mul_input : PureSpec.MulInput
  v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL
  r_a : ℕ
  h_match_primary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a)
  -- #100: value/data promises only — the cross-world `nextPC_matches` sub-field is
  -- no longer caller-supplied (DERIVED in `mulEnvOf` via `sequential_nextPC_discharged`).
  promises : RTypePromisesNoNextPC
      (binding i) mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
      c.r1 c.r2 c.rd (busSub trace i (Pilot.execRowOf trace i)).exec_row
      (busSub trace i (Pilot.execRowOf trace i)).e0
      (busSub trace i (Pilot.execRowOf trace i)).e1
      (busSub trace i (Pilot.execRowOf trace i)).e2
  h_row_constraints :
    ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a
  arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a
  h_rs1_value : mul_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val
  h_rs2_value : mul_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val
  h_not_forge :
    ¬ ((v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0))

/-- The PC agreement `Inputs_mul` carries on top of `InputsCore_mul`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_mul (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mul trace i) : Type extends InputsCore_mul trace binding i c where
  -- #100 next-PC transition inputs (consumed by `mulEnvOf`): the committed Main `pc`
  -- column at row `i` equals the Sail PC (JAL/AUIPC-class provenance bridge), the
  -- `pc + 4` successor does not wrap FGL, and the bus exec_row is the real committed
  -- exec-bus row `execRowOf`. None asserts `exec_row[1].pc = …`; the next-PC fact is
  -- derived from the transition certificate. The value-defect gate is untouched.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = mul_input.PC.toNat

/-- Per-op residual bundle for the `mul` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_mul` bundles them. -/
structure RowData_mul
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_mul trace i
  toDecode : Decode_mul trace i toClaim
  toInputs : Inputs_mul trace binding i toClaim

def toRowData_mul {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_mul trace i) (dec : Decode_mul trace i c)
    (ia : Inputs_mul trace binding i c) : RowData_mul trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_mulh (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_mulh (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulh trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  -- #100 next-PC transition input (next Main row exists); see `Decode_mul.h_idx`.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure InputsCore_mulh (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulh trace i) : Type where
  mulh_input : PureSpec.MulhInput
  v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL
  r_a : ℕ
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a)
  -- #100: value/data promises only — `nextPC_matches` DERIVED in `mulhEnvOf`.
  promises : RTypePromisesNoNextPC
      (binding i) mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
      c.r1 c.r2 c.rd (busSub trace i (Pilot.execRowOf trace i)).exec_row
      (busSub trace i (Pilot.execRowOf trace i)).e0
      (busSub trace i (Pilot.execRowOf trace i)).e1
      (busSub trace i (Pilot.execRowOf trace i)).e2
  h_row_constraints :
    ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a
  arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a
  h_rs1_value : mulh_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val
  h_rs2_value : mulh_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val
  h_not_forge :
    ¬ ((v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0))

/-- The PC agreement `Inputs_mulh` carries on top of `InputsCore_mulh`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_mulh (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulh trace i) : Type extends InputsCore_mulh trace binding i c where
  -- #100 next-PC transition inputs (consumed by `mulhEnvOf`); see `Inputs_mul`.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = mulh_input.PC.toNat

/-- Per-op residual bundle for the `mulh` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_mulh` bundles them. -/
structure RowData_mulh
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_mulh trace i
  toDecode : Decode_mulh trace i toClaim
  toInputs : Inputs_mulh trace binding i toClaim

def toRowData_mulh {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_mulh trace i) (dec : Decode_mulh trace i c)
    (ia : Inputs_mulh trace binding i c) : RowData_mulh trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_mulhsu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_mulhsu (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulhsu trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  -- #100 next-PC transition input (next Main row exists); see `Decode_mul.h_idx`.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure InputsCore_mulhsu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulhsu trace i) : Type where
  mulhsu_input : PureSpec.MulhsuInput
  v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL
  r_a : ℕ
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a)
  -- #100: value/data promises only — `nextPC_matches` DERIVED in `mulhsuEnvOf`.
  promises : RTypePromisesNoNextPC
      (binding i) mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
      c.r1 c.r2 c.rd (busSub trace i (Pilot.execRowOf trace i)).exec_row
      (busSub trace i (Pilot.execRowOf trace i)).e0
      (busSub trace i (Pilot.execRowOf trace i)).e1
      (busSub trace i (Pilot.execRowOf trace i)).e2
  h_row_constraints :
    ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a
  arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a
  h_rs1_value : mulhsu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val
  h_rs2_value : mulhsu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val
  h_not_forge :
    ¬ ((v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
      ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0))

/-- The PC agreement `Inputs_mulhsu` carries on top of `InputsCore_mulhsu`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_mulhsu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulhsu trace i) : Type extends InputsCore_mulhsu trace binding i c where
  -- #100 next-PC transition inputs (consumed by `mulhsuEnvOf`); see `Inputs_mul`.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = mulhsu_input.PC.toNat

/-- Per-op residual bundle for the `mulhsu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_mulhsu` bundles them. -/
structure RowData_mulhsu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_mulhsu trace i
  toDecode : Decode_mulhsu trace i toClaim
  toInputs : Inputs_mulhsu trace binding i toClaim

def toRowData_mulhsu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_mulhsu trace i) (dec : Decode_mulhsu trace i c)
    (ia : Inputs_mulhsu trace binding i c) : RowData_mulhsu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_div (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_div (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_div trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  -- #100 next-PC transition input (next Main row exists); see `Decode_mul.h_idx`.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_DIV
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure InputsCore_div (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_div trace i) : Type where
  div_input : PureSpec.DivInput
  -- #100: value/data promises only — `nextPC_matches` DERIVED in `divEnvOf`.
  promises : RTypePromisesNoNextPC
      (binding i) div_input.r1_val div_input.r2_val div_input.rd div_input.PC
      c.r1 c.r2 c.rd (busSub trace i (Pilot.execRowOf trace i)).exec_row
      (busSub trace i (Pilot.execRowOf trace i)).e0
      (busSub trace i (Pilot.execRowOf trace i)).e1
      (busSub trace i (Pilot.execRowOf trace i)).e2
  h_rs1_value :
    ∀ (h_main_active :
        (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (h_main_op :
        (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV),
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            ((divV trace binding i h_main_active h_main_op).c_0 0).val
            ((divV trace binding i h_main_active h_main_op).c_1 0).val
            ((divV trace binding i h_main_active h_main_op).c_2 0).val
            ((divV trace binding i h_main_active h_main_op).c_3 0).val : ℤ)
            - ((divV trace binding i h_main_active h_main_op).np 0).val
                * (2 : ℤ) ^ 64
  h_rs2_value :
    ∀ (h_main_active :
        (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (h_main_op :
        (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV),
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            ((divV trace binding i h_main_active h_main_op).b_0 0).val
            ((divV trace binding i h_main_active h_main_op).b_1 0).val
            ((divV trace binding i h_main_active h_main_op).b_2 0).val
            ((divV trace binding i h_main_active h_main_op).b_3 0).val : ℤ)
            - ((divV trace binding i h_main_active h_main_op).nb 0).val
                * (2 : ℤ) ^ 64

/-- The PC agreement `Inputs_div` carries on top of `InputsCore_div`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_div (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_div trace i) : Type extends InputsCore_div trace binding i c where
  -- #100 next-PC transition inputs (consumed by `divEnvOf`); see `Inputs_mul`.
  -- These are next-PC plumbing only and leave the DivRemForge value gate untouched.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = div_input.PC.toNat

/-- Per-op residual bundle for the `div` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_div` bundles them. -/
structure RowData_div
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_div trace i
  toDecode : Decode_div trace i toClaim
  toInputs : Inputs_div trace binding i toClaim

def toRowData_div {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_div trace i) (dec : Decode_div trace i c)
    (ia : Inputs_div trace binding i c) : RowData_div trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_rem (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_rem (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_rem trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REM
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  -- #100 next-PC transition input (next Main row exists); see `Decode_mul.h_idx`.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_REM
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure InputsCore_rem (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_rem trace i) : Type where
  rem_input : PureSpec.RemInput
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a)
  -- #100: value/data promises only — `nextPC_matches` DERIVED in `remEnvOf`.
  promises : RTypePromisesNoNextPC
      (binding i) rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
      c.r1 c.r2 c.rd (busSub trace i (Pilot.execRowOf trace i)).exec_row
      (busSub trace i (Pilot.execRowOf trace i)).e0
      (busSub trace i (Pilot.execRowOf trace i)).e1
      (busSub trace i (Pilot.execRowOf trace i)).e2
  h_row_constraints :
    ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a
  arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a
  h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1
  h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1
  h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1
  h_np_xor :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
          - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
  h_nr_pin :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
              * (65536 * 65536 * 65536)) * 0 = 0
        ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
        ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0
  h_rs1_value :
    rem_input.r1_val.toInt
      = (ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
          - (v.np r_a).val * (2:ℤ)^64
  h_rs2_value :
    rem_input.r2_val.toInt
      = (ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
          - (v.nb r_a).val * (2:ℤ)^64
  h_r_le :
    ((ZiskFv.PackedBitVec.MulNoWrap.packed4
        (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
      - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ rem_input.r2_val.toInt.natAbs
  h_r_sign :
    0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
          - (v.nr r_a).val * (2:ℤ)^64) * rem_input.r1_val.toInt
  h_not_forge :
    ¬ ((ZiskFv.Compliance.Defects.signedRemainderInt v r_a).natAbs
        = rem_input.r2_val.toInt.natAbs)

/-- The PC agreement `Inputs_rem` carries on top of `InputsCore_rem`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_rem (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_rem trace i) : Type extends InputsCore_rem trace binding i c where
  -- #100 next-PC transition inputs (consumed by `remEnvOf`); see `Inputs_mul`.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = rem_input.PC.toNat

/-- Per-op residual bundle for the `rem` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_rem` bundles them. -/
structure RowData_rem
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_rem trace i
  toDecode : Decode_rem trace i toClaim
  toInputs : Inputs_rem trace binding i toClaim

def toRowData_rem {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_rem trace i) (dec : Decode_rem trace i c)
    (ia : Inputs_rem trace binding i c) : RowData_rem trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_divw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_divw (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_divw trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 1
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  -- #100 next-PC transition input (next Main row exists); see `Decode_mul.h_idx`.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_DIV_W
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure InputsCore_divw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_divw trace i) : Type where
  divw_input : PureSpec.DivwInput
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_match_primary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a)
  -- #100: value/data promises only — `nextPC_matches` DERIVED in `divwEnvOf`.
  promises : RTypePromisesNoNextPC
      (binding i) divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
      c.r1 c.r2 c.rd (busSub trace i (Pilot.execRowOf trace i)).exec_row
      (busSub trace i (Pilot.execRowOf trace i)).e0
      (busSub trace i (Pilot.execRowOf trace i)).e1
      (busSub trace i (Pilot.execRowOf trace i)).e2
  h_row_constraints :
    ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a
  h_boundary :
    ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a
  arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a
  h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1
  h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1
  h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1
  h_np_xor :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
          - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
  h_nr_pin :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0)
  h_m32_v : v.m32 r_a = 1
  h_div_v : v.div r_a = 1
  h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0
  h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0
  h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0
  h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0
  h_byte_lo :
    (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 0).val
        + (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 1).val * 256
        + (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 2).val * 65536
        + (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 3).val * 16777216
      = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536
  h_sext_choice :
    (((ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 4).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 5).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 6).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 7).val = 0)
      ∧ (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648)
    ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 4).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 5).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 6).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 7).val = 255)
      ∧ (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648)
  h_rs1_value :
    (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
      = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32
  h_rs2_value :
    (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
      = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32
  h_r_le :
    (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
      - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
        ≤ (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs
  h_r_sign :
    0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
        * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
  h_not_forge :
    ¬ (Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32
        ∧ (ZiskFv.Compliance.Defects.signedRemainderIntW v r_a).natAbs
          = (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)

/-- The PC agreement `Inputs_divw` carries on top of `InputsCore_divw`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_divw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_divw trace i) : Type extends InputsCore_divw trace binding i c where
  -- #100 next-PC transition inputs (consumed by `divwEnvOf`); see `Inputs_mul`.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = divw_input.PC.toNat

/-- Per-op residual bundle for the `divw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_divw` bundles them. -/
structure RowData_divw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_divw trace i
  toDecode : Decode_divw trace i toClaim
  toInputs : Inputs_divw trace binding i toClaim

def toRowData_divw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_divw trace i) (dec : Decode_divw trace i c)
    (ia : Inputs_divw trace binding i c) : RowData_divw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_remw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_remw (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_remw trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REM_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 1
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  -- #100 next-PC transition input (next Main row exists); see `Decode_mul.h_idx`.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_REM_W
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure InputsCore_remw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_remw trace i) : Type where
  remw_input : PureSpec.RemwInput
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a)
  -- #100: value/data promises only — `nextPC_matches` DERIVED in `remwEnvOf`.
  promises : RTypePromisesNoNextPC
      (binding i) remw_input.r1_val remw_input.r2_val remw_input.rd remw_input.PC
      c.r1 c.r2 c.rd (busSub trace i (Pilot.execRowOf trace i)).exec_row
      (busSub trace i (Pilot.execRowOf trace i)).e0
      (busSub trace i (Pilot.execRowOf trace i)).e1
      (busSub trace i (Pilot.execRowOf trace i)).e2
  h_row_constraints :
    ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a
  arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a
  arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a
  arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a
  h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1
  h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1
  h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1
  h_np_xor :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
          - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
  h_nr_pin :
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
      ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0)
  h_m32_v : v.m32 r_a = 1
  h_div_v : v.div r_a = 1
  h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0
  h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0
  h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0
  h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0
  h_byte_lo :
    (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 0).val
        + (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 1).val * 256
        + (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 2).val * 65536
        + (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 3).val * 16777216
      = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536
  h_sext_choice :
    (((ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 4).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 5).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 6).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 7).val = 0)
      ∧ (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648)
    ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 4).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 5).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 6).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt
          (busSub trace i (Pilot.execRowOf trace i)).e2 7).val = 255)
      ∧ (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648)
  h_rs1_value :
    (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
      = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32
  h_rs2_value :
    (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
      = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32
  h_r_le :
    (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
      - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
      ≤ (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs
  h_r_sign :
    0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
          - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
        * (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
  h_not_forge :
    ¬ (Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32
        ∧ (ZiskFv.Compliance.Defects.signedRemainderIntW v r_a).natAbs
          = (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs)

/-- The PC agreement `Inputs_remw` carries on top of `InputsCore_remw`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_remw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_remw trace i) : Type extends InputsCore_remw trace binding i c where
  -- #100 next-PC transition inputs (consumed by `remwEnvOf`); see `Inputs_mul`.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = remw_input.PC.toNat

/-- Per-op residual bundle for the `remw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_remw` bundles them. -/
structure RowData_remw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_remw trace i
  toDecode : Decode_remw trace i toClaim
  toInputs : Inputs_remw trace binding i toClaim

def toRowData_remw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_remw trace i) (dec : Decode_remw trace i c)
    (ia : Inputs_remw trace binding i c) : RowData_remw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_mulhu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_mulhu (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulhu trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_idx : i.val + 1 < trace.mainTable.table.length
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure InputsCore_mulhu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulhu trace i) : Type where
  mulhu_input : PureSpec.MulhuInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok mulhu_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok mulhu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some mulhu_input.PC
  h_input_rd : mulhu_input.rd = regidx_to_fin c.rd
  h_rs1_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH),
    mulhu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((vOfMulwRow (mulhuArow trace binding i ha ho)).a_0 0).val
        ((vOfMulwRow (mulhuArow trace binding i ha ho)).a_1 0).val
        ((vOfMulwRow (mulhuArow trace binding i ha ho)).a_2 0).val
        ((vOfMulwRow (mulhuArow trace binding i ha ho)).a_3 0).val
  h_rs2_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH),
    mulhu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((vOfMulwRow (mulhuArow trace binding i ha ho)).b_0 0).val
        ((vOfMulwRow (mulhuArow trace binding i ha ho)).b_1 0).val
        ((vOfMulwRow (mulhuArow trace binding i ha ho)).b_2 0).val
        ((vOfMulwRow (mulhuArow trace binding i ha ho)).b_3 0).val

/-- The PC agreement `Inputs_mulhu` carries on top of `InputsCore_mulhu`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_mulhu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_mulhu trace i) : Type extends InputsCore_mulhu trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = mulhu_input.PC.toNat

/-- Per-op residual bundle for the `mulhu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_mulhu` bundles them. -/
structure RowData_mulhu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_mulhu trace i
  toDecode : Decode_mulhu trace i toClaim
  toInputs : Inputs_mulhu trace binding i toClaim

def toRowData_mulhu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_mulhu trace i) (dec : Decode_mulhu trace i c)
    (ia : Inputs_mulhu trace binding i c) : RowData_mulhu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_divu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_divu (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_divu trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_idx : i.val + 1 < trace.mainTable.table.length
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure InputsCore_divu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_divu trace i) : Type where
  divu_input : PureSpec.DivuInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok divu_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok divu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some divu_input.PC
  h_input_rd : divu_input.rd = regidx_to_fin c.rd
  remainder_bound :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU),
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (divuArow trace binding i ha ho)) 0
  h_rs1_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU),
    divu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((divuArow trace binding i ha ho).chunks.c_0).val
        ((divuArow trace binding i ha ho).chunks.c_1).val
        ((divuArow trace binding i ha ho).chunks.c_2).val
        ((divuArow trace binding i ha ho).chunks.c_3).val
  h_rs2_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU),
    divu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((divuArow trace binding i ha ho).chunks.b_0).val
        ((divuArow trace binding i ha ho).chunks.b_1).val
        ((divuArow trace binding i ha ho).chunks.b_2).val
        ((divuArow trace binding i ha ho).chunks.b_3).val

/-- The PC agreement `Inputs_divu` carries on top of `InputsCore_divu`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_divu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_divu trace i) : Type extends InputsCore_divu trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = divu_input.PC.toNat

/-- Per-op residual bundle for the `divu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_divu` bundles them. -/
structure RowData_divu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_divu trace i
  toDecode : Decode_divu trace i toClaim
  toInputs : Inputs_divu trace binding i toClaim

def toRowData_divu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_divu trace i) (dec : Decode_divu trace i c)
    (ia : Inputs_divu trace binding i c) : RowData_divu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_divuw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_divuw (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_divuw trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 1
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_idx : i.val + 1 < trace.mainTable.table.length
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure InputsCore_divuw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_divuw trace i) : Type where
  divuw_input : PureSpec.DivuwInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok divuw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok divuw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some divuw_input.PC
  h_input_rd : divuw_input.rd = regidx_to_fin c.rd
  remainder_bound :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W),
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (divuwArow trace binding i ha ho)) 0
  h_b23 :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W),
    ((divuwArow trace binding i ha ho).chunks.b_2).val = 0
      ∧ ((divuwArow trace binding i ha ho).chunks.b_3).val = 0
  h_c23 :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W),
    ((divuwArow trace binding i ha ho).chunks.c_2).val = 0
      ∧ ((divuwArow trace binding i ha ho).chunks.c_3).val = 0
  h_sext_choice :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W),
    ((((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 4).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 5).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 6).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 7).val = 0)
        ∧ ((divuwArow trace binding i ha ho).chunks.a_0).val
            + ((divuwArow trace binding i ha ho).chunks.a_1).val * 65536
              < 2147483648)
      ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 4).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 5).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 6).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 7).val = 255)
        ∧ ((divuwArow trace binding i ha ho).chunks.a_0).val
            + ((divuwArow trace binding i ha ho).chunks.a_1).val * 65536
              ≥ 2147483648))
  h_rs1_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W),
    (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
    = ((divuwArow trace binding i ha ho).chunks.c_0).val
        + ((divuwArow trace binding i ha ho).chunks.c_1).val * 65536
  h_rs2_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W),
    (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
    = ((divuwArow trace binding i ha ho).chunks.b_0).val
        + ((divuwArow trace binding i ha ho).chunks.b_1).val * 65536

/-- The PC agreement `Inputs_divuw` carries on top of `InputsCore_divuw`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_divuw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_divuw trace i) : Type extends InputsCore_divuw trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = divuw_input.PC.toNat

/-- Per-op residual bundle for the `divuw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_divuw` bundles them. -/
structure RowData_divuw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_divuw trace i
  toDecode : Decode_divuw trace i toClaim
  toInputs : Inputs_divuw trace binding i toClaim

def toRowData_divuw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_divuw trace i) (dec : Decode_divuw trace i c)
    (ia : Inputs_divuw trace binding i c) : RowData_divuw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_remu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_remu (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_remu trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 0
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_idx : i.val + 1 < trace.mainTable.table.length
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure InputsCore_remu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_remu trace i) : Type where
  remu_input : PureSpec.RemuInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok remu_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok remu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some remu_input.PC
  h_input_rd : remu_input.rd = regidx_to_fin c.rd
  remainder_bound :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU),
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (remuArow trace binding i ha ho)) 0
  h_rs1_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU),
    remu_input.r1_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((remuArow trace binding i ha ho).chunks.c_0).val
        ((remuArow trace binding i ha ho).chunks.c_1).val
        ((remuArow trace binding i ha ho).chunks.c_2).val
        ((remuArow trace binding i ha ho).chunks.c_3).val
  h_rs2_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU),
    remu_input.r2_val.toNat
    = ZiskFv.PackedBitVec.MulNoWrap.packed4
        ((remuArow trace binding i ha ho).chunks.b_0).val
        ((remuArow trace binding i ha ho).chunks.b_1).val
        ((remuArow trace binding i ha ho).chunks.b_2).val
        ((remuArow trace binding i ha ho).chunks.b_3).val

/-- The PC agreement `Inputs_remu` carries on top of `InputsCore_remu`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_remu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_remu trace i) : Type extends InputsCore_remu trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = remu_input.PC.toNat

/-- Per-op residual bundle for the `remu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_remu` bundles them. -/
structure RowData_remu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_remu trace i
  toDecode : Decode_remu trace i toClaim
  toInputs : Inputs_remu trace binding i toClaim

def toRowData_remu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_remu trace i) (dec : Decode_remu trace i c)
    (ia : Inputs_remu trace binding i c) : RowData_remu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_remuw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_remuw (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_remuw trace i) : Type where
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_store_pc :
    (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
  h_m32 :
    (mainOfTable trace.program trace.mainTable).m32 i.val = 1
  h_set_pc :
    (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
  h_jmp_offset1 :
    (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
  h_jmp_offset2 :
    (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4
  h_idx : i.val + 1 < trace.mainTable.table.length
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2
  h_store_ind :
    (mainRowWithRomSub trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomSub trace i).rom.store_reg =
      ZiskFv.AirsClean.boolF (decide (regidx_to_fin c.rd ≠ 0))
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure InputsCore_remuw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_remuw trace i) : Type where
  remuw_input : PureSpec.RemuwInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok remuw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok remuw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some remuw_input.PC
  h_input_rd : remuw_input.rd = regidx_to_fin c.rd
  remainder_bound :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W),
    ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
      (vOfDivuRow (remuwArow trace binding i ha ho)) 0
  h_b23 :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W),
    ((remuwArow trace binding i ha ho).chunks.b_2).val = 0
      ∧ ((remuwArow trace binding i ha ho).chunks.b_3).val = 0
  h_c23 :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W),
    ((remuwArow trace binding i ha ho).chunks.c_2).val = 0
      ∧ ((remuwArow trace binding i ha ho).chunks.c_3).val = 0
  h_sext_choice :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W),
    ((((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 4).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 5).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 6).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 7).val = 0)
        ∧ ((remuwArow trace binding i ha ho).chunks.d_0).val
            + ((remuwArow trace binding i ha ho).chunks.d_1).val * 65536
              < 2147483648)
      ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 4).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 5).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 6).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace i (Pilot.execRowOf trace i)).e2 7).val = 255)
        ∧ ((remuwArow trace binding i ha ho).chunks.d_0).val
            + ((remuwArow trace binding i ha ho).chunks.d_1).val * 65536
              ≥ 2147483648))
  h_rs1_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W),
    (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
    = ((remuwArow trace binding i ha ho).chunks.c_0).val
        + ((remuwArow trace binding i ha ho).chunks.c_1).val * 65536
  h_rs2_value :
    ∀ (ha : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
      (ho : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W),
    (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
    = ((remuwArow trace binding i ha ho).chunks.b_0).val
        + ((remuwArow trace binding i ha ho).chunks.b_1).val * 65536

/-- The PC agreement `Inputs_remuw` carries on top of `InputsCore_remuw`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_remuw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_remuw trace i) : Type extends InputsCore_remuw trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = remuw_input.PC.toNat

/-- Per-op residual bundle for the `remuw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_remuw` bundles them. -/
structure RowData_remuw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_remuw trace i
  toDecode : Decode_remuw trace i toClaim
  toInputs : Inputs_remuw trace binding i toClaim

def toRowData_remuw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_remuw trace i) (dec : Decode_remuw trace i c)
    (ia : Inputs_remuw trace binding i c) : RowData_remuw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

/-- The exact decoded five register bits, without an encoder guard or default. -/
def storeRegBits (r : regidx) : BitVec 5 :=
  match r with
  | .Regidx bits => bits

@[simp] theorem storeRegBits_roundtrip (r : regidx) :
    regidx.Regidx (storeRegBits r) = r := by
  cases r <;> rfl
structure Claim_sb (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  imm : BitVec 12

structure Decode_sb (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sb trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_main_ind_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = 1
  h_store_ind :
    (mainRowWithRomSt trace i).rom.store_ind = 1
  h_store_reg :
    (mainRowWithRomSt trace i).rom.store_reg = 0
  h_store_offset_imm :
    (mainRowWithRomSt trace i).rom.store_offset =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB store-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` store/COPYB arm, lines 466-564).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4

/-- Construct runtime operands only from successful reads of this Sail state. -/
noncomputable def storeInput_sb
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 r2 : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_r2 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r2) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc) :
    PureSpec.SbInput where
  r1 := storeRegBits r1
  r2 := storeRegBits r2
  imm := imm
  r1_val := Classical.choose h_r1
  r2_val := Classical.choose h_r2
  PC := Classical.choose h_pc
structure InputsCore_sb (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sb trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_r2 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r2) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sb_state_assumptions
    (storeInput_sb (binding i) c.r1 c.r2 c.imm h_input_r1 h_input_r2 h_input_pc) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_a1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi (Classical.choose h_input_r1)
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r2)
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi (Classical.choose h_input_r2)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg

/-- Canonical pure input: the claim contributes decoded fields only. -/
noncomputable def InputsCore_sb.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_sb trace i}
    (inputs : InputsCore_sb trace binding i c) : PureSpec.SbInput :=
  storeInput_sb (binding i) c.r1 c.r2 c.imm
    inputs.h_input_r1 inputs.h_input_r2 inputs.h_input_pc

theorem InputsCore_sb.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_sb trace i}
    (inputs : InputsCore_sb trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- The complete pre-cutover store surface constructs the canonical record.
The three read-existence fields impose no additional caller condition: they
follow from the first three conjuncts of the unchanged opcode assumptions.
The resulting canonical input is exactly the original input, not a new value. -/
def InputsCore_sb.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.SbInput) (regs : ModeRegsFull)
    (h_opcode : PureSpec.sb_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_a1 : (mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi input.r1_val)
    (h_b0 : (mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo input.r2_val)
    (h_b1 : (mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi input.r2_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg) :
    { core : InputsCore_sb trace binding i
      { r1 := regidx.Regidx input.r1, r2 := regidx.Regidx input.r2, imm := input.imm } //
      core.input = input } := by
  have h_read1 : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  have h_read2 : read_xreg (regidx_to_fin (regidx.Regidx input.r2)) (binding i) =
      EStateM.Result.ok input.r2_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r2)
      (regidx_to_fin (regidx.Regidx input.r2)) (by simp [regidx_to_fin])]
    exact h_opcode.2.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read1⟩
  let h_r2 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r2)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r2_val, h_read2⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value1 : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read1)).1
  have h_value2 : Classical.choose h_r2 = input.r2_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r2).symm.trans h_read2)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  have h_input : storeInput_sb (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.r2) input.imm h_r1 h_r2 h_pc = input := by
    cases input
    simp only [storeInput_sb, storeRegBits, h_value1, h_value2, h_pc_value]
  refine ⟨{
    h_input_r1 := h_r1
    h_input_r2 := h_r2
    h_input_pc := h_pc
    regs := regs
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_a1_value := ?_
    h_b0_value := ?_
    h_b1_value := ?_
    h_risc_v_assumptions := h_platform }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value1] using h_a0
  · simpa only [h_value1] using h_a1
  · simpa only [h_value2] using h_b0
  · simpa only [h_value2] using h_b1
  · exact h_input

/-- The PC agreement `Inputs_sb` carries on top of `InputsCore_sb`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_sb (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sb trace i) : Type extends InputsCore_sb trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `sb` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sb` bundles them. -/
structure RowData_sb
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sb trace i
  toDecode : Decode_sb trace i toClaim
  toInputs : Inputs_sb trace binding i toClaim

def toRowData_sb {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sb trace i) (dec : Decode_sb trace i c)
    (ia : Inputs_sb trace binding i c) : RowData_sb trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_sh (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  imm : BitVec 12

structure Decode_sh (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sh trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_main_ind_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = 2
  h_store_ind :
    (mainRowWithRomSt trace i).rom.store_ind = 1
  h_store_reg :
    (mainRowWithRomSt trace i).rom.store_reg = 0
  h_store_offset_imm :
    (mainRowWithRomSt trace i).rom.store_offset =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB store-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` store/COPYB arm, lines 466-564).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4

/-- Construct runtime operands only from successful reads of this Sail state. -/
noncomputable def storeInput_sh
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 r2 : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_r2 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r2) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc) :
    PureSpec.ShInput where
  r1 := storeRegBits r1
  r2 := storeRegBits r2
  imm := imm
  r1_val := Classical.choose h_r1
  r2_val := Classical.choose h_r2
  PC := Classical.choose h_pc
structure InputsCore_sh (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sh trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_r2 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r2) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sh_state_assumptions
    (storeInput_sh (binding i) c.r1 c.r2 c.imm h_input_r1 h_input_r2 h_input_pc) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_a1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi (Classical.choose h_input_r1)
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r2)
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi (Classical.choose h_input_r2)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg

/-- Canonical pure input: the claim contributes decoded fields only. -/
noncomputable def InputsCore_sh.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_sh trace i}
    (inputs : InputsCore_sh trace binding i c) : PureSpec.ShInput :=
  storeInput_sh (binding i) c.r1 c.r2 c.imm
    inputs.h_input_r1 inputs.h_input_r2 inputs.h_input_pc

theorem InputsCore_sh.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_sh trace i}
    (inputs : InputsCore_sh trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- The complete pre-cutover store surface constructs the canonical record.
The three read-existence fields impose no additional caller condition: they
follow from the first three conjuncts of the unchanged opcode assumptions.
The resulting canonical input is exactly the original input, not a new value. -/
def InputsCore_sh.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.ShInput) (regs : ModeRegsFull)
    (h_opcode : PureSpec.sh_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_a1 : (mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi input.r1_val)
    (h_b0 : (mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo input.r2_val)
    (h_b1 : (mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi input.r2_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg) :
    { core : InputsCore_sh trace binding i
      { r1 := regidx.Regidx input.r1, r2 := regidx.Regidx input.r2, imm := input.imm } //
      core.input = input } := by
  have h_read1 : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  have h_read2 : read_xreg (regidx_to_fin (regidx.Regidx input.r2)) (binding i) =
      EStateM.Result.ok input.r2_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r2)
      (regidx_to_fin (regidx.Regidx input.r2)) (by simp [regidx_to_fin])]
    exact h_opcode.2.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read1⟩
  let h_r2 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r2)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r2_val, h_read2⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value1 : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read1)).1
  have h_value2 : Classical.choose h_r2 = input.r2_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r2).symm.trans h_read2)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  have h_input : storeInput_sh (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.r2) input.imm h_r1 h_r2 h_pc = input := by
    cases input
    simp only [storeInput_sh, storeRegBits, h_value1, h_value2, h_pc_value]
  refine ⟨{
    h_input_r1 := h_r1
    h_input_r2 := h_r2
    h_input_pc := h_pc
    regs := regs
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_a1_value := ?_
    h_b0_value := ?_
    h_b1_value := ?_
    h_risc_v_assumptions := h_platform }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value1] using h_a0
  · simpa only [h_value1] using h_a1
  · simpa only [h_value2] using h_b0
  · simpa only [h_value2] using h_b1
  · exact h_input

/-- The PC agreement `Inputs_sh` carries on top of `InputsCore_sh`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_sh (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sh trace i) : Type extends InputsCore_sh trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `sh` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sh` bundles them. -/
structure RowData_sh
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sh trace i
  toDecode : Decode_sh trace i toClaim
  toInputs : Inputs_sh trace binding i toClaim

def toRowData_sh {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sh trace i) (dec : Decode_sh trace i c)
    (ia : Inputs_sh trace binding i c) : RowData_sh trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_sw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  imm : BitVec 12

structure Decode_sw (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sw trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_main_ind_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = 4
  h_store_ind :
    (mainRowWithRomSt trace i).rom.store_ind = 1
  h_store_reg :
    (mainRowWithRomSt trace i).rom.store_reg = 0
  h_store_offset_imm :
    (mainRowWithRomSt trace i).rom.store_offset =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB store-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` store/COPYB arm, lines 466-564).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4

/-- Construct runtime operands only from successful reads of this Sail state. -/
noncomputable def storeInput_sw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 r2 : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_r2 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r2) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc) :
    PureSpec.SwInput where
  r1 := storeRegBits r1
  r2 := storeRegBits r2
  imm := imm
  r1_val := Classical.choose h_r1
  r2_val := Classical.choose h_r2
  PC := Classical.choose h_pc
structure InputsCore_sw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sw trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_r2 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r2) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sw_state_assumptions
    (storeInput_sw (binding i) c.r1 c.r2 c.imm h_input_r1 h_input_r2 h_input_pc) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_a1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi (Classical.choose h_input_r1)
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r2)
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi (Classical.choose h_input_r2)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg

/-- Canonical pure input: the claim contributes decoded fields only. -/
noncomputable def InputsCore_sw.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_sw trace i}
    (inputs : InputsCore_sw trace binding i c) : PureSpec.SwInput :=
  storeInput_sw (binding i) c.r1 c.r2 c.imm
    inputs.h_input_r1 inputs.h_input_r2 inputs.h_input_pc

theorem InputsCore_sw.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_sw trace i}
    (inputs : InputsCore_sw trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- The complete pre-cutover store surface constructs the canonical record.
The three read-existence fields impose no additional caller condition: they
follow from the first three conjuncts of the unchanged opcode assumptions.
The resulting canonical input is exactly the original input, not a new value. -/
def InputsCore_sw.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.SwInput) (regs : ModeRegsFull)
    (h_opcode : PureSpec.sw_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_a1 : (mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi input.r1_val)
    (h_b0 : (mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo input.r2_val)
    (h_b1 : (mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi input.r2_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg) :
    { core : InputsCore_sw trace binding i
      { r1 := regidx.Regidx input.r1, r2 := regidx.Regidx input.r2, imm := input.imm } //
      core.input = input } := by
  have h_read1 : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  have h_read2 : read_xreg (regidx_to_fin (regidx.Regidx input.r2)) (binding i) =
      EStateM.Result.ok input.r2_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r2)
      (regidx_to_fin (regidx.Regidx input.r2)) (by simp [regidx_to_fin])]
    exact h_opcode.2.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read1⟩
  let h_r2 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r2)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r2_val, h_read2⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value1 : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read1)).1
  have h_value2 : Classical.choose h_r2 = input.r2_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r2).symm.trans h_read2)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  have h_input : storeInput_sw (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.r2) input.imm h_r1 h_r2 h_pc = input := by
    cases input
    simp only [storeInput_sw, storeRegBits, h_value1, h_value2, h_pc_value]
  refine ⟨{
    h_input_r1 := h_r1
    h_input_r2 := h_r2
    h_input_pc := h_pc
    regs := regs
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_a1_value := ?_
    h_b0_value := ?_
    h_b1_value := ?_
    h_risc_v_assumptions := h_platform }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value1] using h_a0
  · simpa only [h_value1] using h_a1
  · simpa only [h_value2] using h_b0
  · simpa only [h_value2] using h_b1
  · exact h_input

/-- The PC agreement `Inputs_sw` carries on top of `InputsCore_sw`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_sw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sw trace i) : Type extends InputsCore_sw trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `sw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sw` bundles them. -/
structure RowData_sw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sw trace i
  toDecode : Decode_sw trace i toClaim
  toInputs : Inputs_sw trace binding i toClaim

def toRowData_sw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sw trace i) (dec : Decode_sw trace i c)
    (ia : Inputs_sw trace binding i c) : RowData_sw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_sd (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  imm : BitVec 12

structure Decode_sd (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sd trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_store_ind :
    (mainRowWithRomSt trace i).rom.store_ind = 1
  h_store_reg :
    (mainRowWithRomSt trace i).rom.store_reg = 0
  h_store_offset_imm :
    (mainRowWithRomSt trace i).rom.store_offset =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB store-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` store/COPYB arm, lines 466-564).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4

/-- Construct runtime operands only from successful reads of this Sail state. -/
noncomputable def storeInput_sd
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 r2 : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_r2 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r2) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc) :
    PureSpec.SdInput where
  r1 := storeRegBits r1
  r2 := storeRegBits r2
  imm := imm
  r1_val := Classical.choose h_r1
  r2_val := Classical.choose h_r2
  PC := Classical.choose h_pc
structure InputsCore_sd (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sd trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_r2 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r2) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sd_state_assumptions
    (storeInput_sd (binding i) c.r1 c.r2 c.imm h_input_r1 h_input_r2 h_input_pc) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_a1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi (Classical.choose h_input_r1)
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r2)
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi (Classical.choose h_input_r2)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg

/-- Canonical pure input: the claim contributes decoded fields only. -/
noncomputable def InputsCore_sd.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_sd trace i}
    (inputs : InputsCore_sd trace binding i c) : PureSpec.SdInput :=
  storeInput_sd (binding i) c.r1 c.r2 c.imm
    inputs.h_input_r1 inputs.h_input_r2 inputs.h_input_pc

theorem InputsCore_sd.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_sd trace i}
    (inputs : InputsCore_sd trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- The complete pre-cutover store surface constructs the canonical record.
The three read-existence fields impose no additional caller condition: they
follow from the first three conjuncts of the unchanged opcode assumptions.
The resulting canonical input is exactly the original input, not a new value. -/
def InputsCore_sd.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.SdInput) (regs : ModeRegsFull)
    (h_opcode : PureSpec.sd_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_a1 : (mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi input.r1_val)
    (h_b0 : (mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo input.r2_val)
    (h_b1 : (mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi input.r2_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg) :
    { core : InputsCore_sd trace binding i
      { r1 := regidx.Regidx input.r1, r2 := regidx.Regidx input.r2, imm := input.imm } //
      core.input = input } := by
  have h_read1 : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  have h_read2 : read_xreg (regidx_to_fin (regidx.Regidx input.r2)) (binding i) =
      EStateM.Result.ok input.r2_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r2)
      (regidx_to_fin (regidx.Regidx input.r2)) (by simp [regidx_to_fin])]
    exact h_opcode.2.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read1⟩
  let h_r2 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r2)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r2_val, h_read2⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value1 : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read1)).1
  have h_value2 : Classical.choose h_r2 = input.r2_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r2).symm.trans h_read2)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  have h_input : storeInput_sd (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.r2) input.imm h_r1 h_r2 h_pc = input := by
    cases input
    simp only [storeInput_sd, storeRegBits, h_value1, h_value2, h_pc_value]
  refine ⟨{
    h_input_r1 := h_r1
    h_input_r2 := h_r2
    h_input_pc := h_pc
    regs := regs
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_a1_value := ?_
    h_b0_value := ?_
    h_b1_value := ?_
    h_risc_v_assumptions := h_platform }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value1] using h_a0
  · simpa only [h_value1] using h_a1
  · simpa only [h_value2] using h_b0
  · simpa only [h_value2] using h_b1
  · exact h_input

/-- The PC agreement `Inputs_sd` carries on top of `InputsCore_sd`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_sd (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sd trace i) : Type extends InputsCore_sd trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `sd` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sd` bundles them. -/
structure RowData_sd
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sd trace i
  toDecode : Decode_sd trace i toClaim
  toInputs : Inputs_sd trace binding i toClaim

def toRowData_sd {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sd trace i) (dec : Decode_sd trace i c)
    (ia : Inputs_sd trace binding i c) : RowData_sd trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_ld (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_ld (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_ld trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (8 : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB load-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` load/COPYB arm, lines 290-336/704-713).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomLd trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomLd trace i).rom.store_reg =
      if (storeRegBits c.rd).toNat = 0 then 0 else 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 (storeRegBits c.rd))
  h_b_offset_imm0 :
    (mainRowWithRomLd trace i).rom.b_offset_imm0 =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)

/-- Read the exact current-domain address; no default bytes or predicate repair. -/
noncomputable def loadInput_ld
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc)
    (h_bytes : ∀ k : Fin 8, ∃ byte : BitVec 8,
      state.mem[(Classical.choose h_r1).toNat + (BitVec.signExtend 64 imm).toNat + k.val]? =
        some byte) : PureSpec.LdInput where
  r1 := storeRegBits r1
  rd := storeRegBits rd
  imm := imm
  r1_val := Classical.choose h_r1
  PC := Classical.choose h_pc
  data0 := Classical.choose (h_bytes ⟨0, by decide⟩)
  data1 := Classical.choose (h_bytes ⟨1, by decide⟩)
  data2 := Classical.choose (h_bytes ⟨2, by decide⟩)
  data3 := Classical.choose (h_bytes ⟨3, by decide⟩)
  data4 := Classical.choose (h_bytes ⟨4, by decide⟩)
  data5 := Classical.choose (h_bytes ⟨5, by decide⟩)
  data6 := Classical.choose (h_bytes ⟨6, by decide⟩)
  data7 := Classical.choose (h_bytes ⟨7, by decide⟩)

structure InputsCore_ld (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_ld trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  h_input_bytes : ∀ k : Fin 8, ∃ byte : BitVec 8,
    (binding i).mem[(Classical.choose h_input_r1).toNat +
      (BitVec.signExtend 64 c.imm).toNat + k.val]? = some byte
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.ld_state_assumptions
    (loadInput_ld (binding i) c.r1 c.rd c.imm h_input_r1 h_input_pc h_input_bytes) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

noncomputable def InputsCore_ld.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_ld trace i}
    (inputs : InputsCore_ld trace binding i c) : PureSpec.LdInput :=
  loadInput_ld (binding i) c.r1 c.rd c.imm
    inputs.h_input_r1 inputs.h_input_pc inputs.h_input_bytes

theorem InputsCore_ld.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_ld trace i}
    (inputs : InputsCore_ld trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- Exact complete old load surface constructs the new record and the SAME input.
In particular no read/mappedness, PC, parse or equality premise is added, and the
unchanged unwrapped-address opcode predicate is transported in full. -/
def InputsCore_ld.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.LdInput)
    (regs : ModeRegsFull) (mem : Valid_Mem FGL FGL) (r_mem : ℕ)
    (h_opcode : PureSpec.ld_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_msg : loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i))
    (h_sel : mem.sel r_mem = 1) (h_wr : mem.wr r_mem = 0) :
    { core : InputsCore_ld trace binding i
      { r1 := regidx.Regidx input.r1, rd := regidx.Regidx input.rd, imm := input.imm } //
      core.input = input } := by
  have h_read : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  let h_bytes : ∀ k : Fin 8, ∃ byte : BitVec 8,
      (binding i).mem[(Classical.choose h_r1).toNat +
        (BitVec.signExtend 64 input.imm).toNat + k.val]? = some byte := by
    intro k
    fin_cases k
    · exact ⟨input.data0, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1⟩
    · exact ⟨input.data1, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.1⟩
    · exact ⟨input.data2, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.1⟩
    · exact ⟨input.data3, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.1⟩
    · exact ⟨input.data4, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.2.1⟩
    · exact ⟨input.data5, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.2.2.1⟩
    · exact ⟨input.data6, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.2.2.2.1⟩
    · exact ⟨input.data7, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.2.2.2.2.1⟩
  have h_data0 : Classical.choose (h_bytes ⟨0, by decide⟩) = input.data0 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨0, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1)
  have h_data1 : Classical.choose (h_bytes ⟨1, by decide⟩) = input.data1 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨1, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.1)
  have h_data2 : Classical.choose (h_bytes ⟨2, by decide⟩) = input.data2 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨2, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.1)
  have h_data3 : Classical.choose (h_bytes ⟨3, by decide⟩) = input.data3 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨3, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.1)
  have h_data4 : Classical.choose (h_bytes ⟨4, by decide⟩) = input.data4 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨4, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.2.1)
  have h_data5 : Classical.choose (h_bytes ⟨5, by decide⟩) = input.data5 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨5, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.2.2.1)
  have h_data6 : Classical.choose (h_bytes ⟨6, by decide⟩) = input.data6 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨6, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.2.2.2.1)
  have h_data7 : Classical.choose (h_bytes ⟨7, by decide⟩) = input.data7 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨7, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.2.2.2.2.1)
  have h_input : loadInput_ld (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.rd) input.imm h_r1 h_pc h_bytes = input := by
    cases input
    dsimp only [loadInput_ld, storeRegBits]
    congr 1
  refine ⟨{
    h_input_r1 := h_r1
    h_input_pc := h_pc
    h_input_bytes := h_bytes
    regs := regs
    mem := mem
    r_mem := r_mem
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_risc_v_assumptions := h_platform
    h_msg := h_msg
    h_mem_sel := h_sel
    h_mem_wr := h_wr }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value] using h_a0
  · exact h_input

/-- The PC agreement `Inputs_ld` carries on top of `InputsCore_ld`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_ld (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_ld trace i) : Type extends InputsCore_ld trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `ld` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_ld` bundles them. -/
structure RowData_ld
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_ld trace i
  toDecode : Decode_ld trace i toClaim
  toInputs : Inputs_ld trace binding i toClaim

def toRowData_ld {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_ld trace i) (dec : Decode_ld trace i c)
    (ia : Inputs_ld trace binding i c) : RowData_ld trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_lbu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_lbu (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lbu trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (1 : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB load-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` load/COPYB arm, lines 290-336/704-713).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomLd trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomLd trace i).rom.store_reg =
      if (storeRegBits c.rd).toNat = 0 then 0 else 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 (storeRegBits c.rd))
  h_b_offset_imm0 :
    (mainRowWithRomLd trace i).rom.b_offset_imm0 =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)

/-- Read the exact current-domain address; no default bytes or predicate repair. -/
noncomputable def loadInput_lbu
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc)
    (h_bytes : ∀ k : Fin 1, ∃ byte : BitVec 8,
      state.mem[(Classical.choose h_r1).toNat + (BitVec.signExtend 64 imm).toNat + k.val]? =
        some byte) : PureSpec.LbuInput where
  r1 := storeRegBits r1
  rd := storeRegBits rd
  imm := imm
  r1_val := Classical.choose h_r1
  PC := Classical.choose h_pc
  data0 := Classical.choose (h_bytes ⟨0, by decide⟩)

structure InputsCore_lbu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lbu trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  h_input_bytes : ∀ k : Fin 1, ∃ byte : BitVec 8,
    (binding i).mem[(Classical.choose h_input_r1).toNat +
      (BitVec.signExtend 64 c.imm).toNat + k.val]? = some byte
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace i (Pilot.execRowOf trace i)).e1
  h_opcode_assumptions : PureSpec.lbu_state_assumptions
    (loadInput_lbu (binding i) c.r1 c.rd c.imm h_input_r1 h_input_pc h_input_bytes) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

noncomputable def InputsCore_lbu.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lbu trace i}
    (inputs : InputsCore_lbu trace binding i c) : PureSpec.LbuInput :=
  loadInput_lbu (binding i) c.r1 c.rd c.imm
    inputs.h_input_r1 inputs.h_input_pc inputs.h_input_bytes

theorem InputsCore_lbu.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lbu trace i}
    (inputs : InputsCore_lbu trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- Exact complete old load surface constructs the new record and the SAME input.
In particular no read/mappedness, PC, parse or equality premise is added, and the
unchanged unwrapped-address opcode predicate is transported in full. -/
def InputsCore_lbu.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.LbuInput)
    (regs : ModeRegsFull) (mem : Valid_Mem FGL FGL) (r_mem : ℕ)
    (align : MemAlignWitness (mainOfTable trace.program trace.mainTable)
      i.val (busLd trace i (Pilot.execRowOf trace i)).e1)
    (h_opcode : PureSpec.lbu_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_msg : loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i))
    (h_sel : mem.sel r_mem = 1) (h_wr : mem.wr r_mem = 0) :
    { core : InputsCore_lbu trace binding i
      { r1 := regidx.Regidx input.r1, rd := regidx.Regidx input.rd, imm := input.imm } //
      core.input = input } := by
  have h_read : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  let h_bytes : ∀ k : Fin 1, ∃ byte : BitVec 8,
      (binding i).mem[(Classical.choose h_r1).toNat +
        (BitVec.signExtend 64 input.imm).toNat + k.val]? = some byte := by
    intro k
    fin_cases k
    · exact ⟨input.data0, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1⟩
  have h_data0 : Classical.choose (h_bytes ⟨0, by decide⟩) = input.data0 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨0, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1)
  have h_input : loadInput_lbu (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.rd) input.imm h_r1 h_pc h_bytes = input := by
    cases input
    dsimp only [loadInput_lbu, storeRegBits]
    congr 1
  refine ⟨{
    h_input_r1 := h_r1
    h_input_pc := h_pc
    h_input_bytes := h_bytes
    regs := regs
    mem := mem
    r_mem := r_mem
    align := align
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_risc_v_assumptions := h_platform
    h_msg := h_msg
    h_mem_sel := h_sel
    h_mem_wr := h_wr }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value] using h_a0
  · exact h_input

/-- The PC agreement `Inputs_lbu` carries on top of `InputsCore_lbu`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_lbu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lbu trace i) : Type extends InputsCore_lbu trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `lbu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_lbu` bundles them. -/
structure RowData_lbu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_lbu trace i
  toDecode : Decode_lbu trace i toClaim
  toInputs : Inputs_lbu trace binding i toClaim

def toRowData_lbu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_lbu trace i) (dec : Decode_lbu trace i c)
    (ia : Inputs_lbu trace binding i c) : RowData_lbu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_lhu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_lhu (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lhu trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (2 : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB load-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` load/COPYB arm, lines 290-336/704-713).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomLd trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomLd trace i).rom.store_reg =
      if (storeRegBits c.rd).toNat = 0 then 0 else 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 (storeRegBits c.rd))
  h_b_offset_imm0 :
    (mainRowWithRomLd trace i).rom.b_offset_imm0 =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)

/-- Read the exact current-domain address; no default bytes or predicate repair. -/
noncomputable def loadInput_lhu
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc)
    (h_bytes : ∀ k : Fin 2, ∃ byte : BitVec 8,
      state.mem[(Classical.choose h_r1).toNat + (BitVec.signExtend 64 imm).toNat + k.val]? =
        some byte) : PureSpec.LhuInput where
  r1 := storeRegBits r1
  rd := storeRegBits rd
  imm := imm
  r1_val := Classical.choose h_r1
  PC := Classical.choose h_pc
  data0 := Classical.choose (h_bytes ⟨0, by decide⟩)
  data1 := Classical.choose (h_bytes ⟨1, by decide⟩)

structure InputsCore_lhu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lhu trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  h_input_bytes : ∀ k : Fin 2, ∃ byte : BitVec 8,
    (binding i).mem[(Classical.choose h_input_r1).toNat +
      (BitVec.signExtend 64 c.imm).toNat + k.val]? = some byte
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace i (Pilot.execRowOf trace i)).e1
  h_opcode_assumptions : PureSpec.lhu_state_assumptions
    (loadInput_lhu (binding i) c.r1 c.rd c.imm h_input_r1 h_input_pc h_input_bytes) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

noncomputable def InputsCore_lhu.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lhu trace i}
    (inputs : InputsCore_lhu trace binding i c) : PureSpec.LhuInput :=
  loadInput_lhu (binding i) c.r1 c.rd c.imm
    inputs.h_input_r1 inputs.h_input_pc inputs.h_input_bytes

theorem InputsCore_lhu.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lhu trace i}
    (inputs : InputsCore_lhu trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- Exact complete old load surface constructs the new record and the SAME input.
In particular no read/mappedness, PC, parse or equality premise is added, and the
unchanged unwrapped-address opcode predicate is transported in full. -/
def InputsCore_lhu.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.LhuInput)
    (regs : ModeRegsFull) (mem : Valid_Mem FGL FGL) (r_mem : ℕ)
    (align : MemAlignWitness (mainOfTable trace.program trace.mainTable)
      i.val (busLd trace i (Pilot.execRowOf trace i)).e1)
    (h_opcode : PureSpec.lhu_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_msg : loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i))
    (h_sel : mem.sel r_mem = 1) (h_wr : mem.wr r_mem = 0) :
    { core : InputsCore_lhu trace binding i
      { r1 := regidx.Regidx input.r1, rd := regidx.Regidx input.rd, imm := input.imm } //
      core.input = input } := by
  have h_read : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  let h_bytes : ∀ k : Fin 2, ∃ byte : BitVec 8,
      (binding i).mem[(Classical.choose h_r1).toNat +
        (BitVec.signExtend 64 input.imm).toNat + k.val]? = some byte := by
    intro k
    fin_cases k
    · exact ⟨input.data0, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1⟩
    · exact ⟨input.data1, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.1⟩
  have h_data0 : Classical.choose (h_bytes ⟨0, by decide⟩) = input.data0 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨0, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1)
  have h_data1 : Classical.choose (h_bytes ⟨1, by decide⟩) = input.data1 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨1, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.1)
  have h_input : loadInput_lhu (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.rd) input.imm h_r1 h_pc h_bytes = input := by
    cases input
    dsimp only [loadInput_lhu, storeRegBits]
    congr 1
  refine ⟨{
    h_input_r1 := h_r1
    h_input_pc := h_pc
    h_input_bytes := h_bytes
    regs := regs
    mem := mem
    r_mem := r_mem
    align := align
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_risc_v_assumptions := h_platform
    h_msg := h_msg
    h_mem_sel := h_sel
    h_mem_wr := h_wr }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value] using h_a0
  · exact h_input

/-- The PC agreement `Inputs_lhu` carries on top of `InputsCore_lhu`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_lhu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lhu trace i) : Type extends InputsCore_lhu trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `lhu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_lhu` bundles them. -/
structure RowData_lhu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_lhu trace i
  toDecode : Decode_lhu trace i toClaim
  toInputs : Inputs_lhu trace binding i toClaim

def toRowData_lhu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_lhu trace i) (dec : Decode_lhu trace i c)
    (ia : Inputs_lhu trace binding i c) : RowData_lhu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_lwu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_lwu (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lwu trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_COPYB
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (4 : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB load-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` load/COPYB arm, lines 290-336/704-713).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomLd trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomLd trace i).rom.store_reg =
      if (storeRegBits c.rd).toNat = 0 then 0 else 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 (storeRegBits c.rd))
  h_b_offset_imm0 :
    (mainRowWithRomLd trace i).rom.b_offset_imm0 =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)

/-- Read the exact current-domain address; no default bytes or predicate repair. -/
noncomputable def loadInput_lwu
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc)
    (h_bytes : ∀ k : Fin 4, ∃ byte : BitVec 8,
      state.mem[(Classical.choose h_r1).toNat + (BitVec.signExtend 64 imm).toNat + k.val]? =
        some byte) : PureSpec.LwuInput where
  r1 := storeRegBits r1
  rd := storeRegBits rd
  imm := imm
  r1_val := Classical.choose h_r1
  PC := Classical.choose h_pc
  data0 := Classical.choose (h_bytes ⟨0, by decide⟩)
  data1 := Classical.choose (h_bytes ⟨1, by decide⟩)
  data2 := Classical.choose (h_bytes ⟨2, by decide⟩)
  data3 := Classical.choose (h_bytes ⟨3, by decide⟩)

structure InputsCore_lwu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lwu trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  h_input_bytes : ∀ k : Fin 4, ∃ byte : BitVec 8,
    (binding i).mem[(Classical.choose h_input_r1).toNat +
      (BitVec.signExtend 64 c.imm).toNat + k.val]? = some byte
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace i (Pilot.execRowOf trace i)).e1
  h_opcode_assumptions : PureSpec.lwu_state_assumptions
    (loadInput_lwu (binding i) c.r1 c.rd c.imm h_input_r1 h_input_pc h_input_bytes) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

noncomputable def InputsCore_lwu.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lwu trace i}
    (inputs : InputsCore_lwu trace binding i c) : PureSpec.LwuInput :=
  loadInput_lwu (binding i) c.r1 c.rd c.imm
    inputs.h_input_r1 inputs.h_input_pc inputs.h_input_bytes

theorem InputsCore_lwu.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lwu trace i}
    (inputs : InputsCore_lwu trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- Exact complete old load surface constructs the new record and the SAME input.
In particular no read/mappedness, PC, parse or equality premise is added, and the
unchanged unwrapped-address opcode predicate is transported in full. -/
def InputsCore_lwu.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.LwuInput)
    (regs : ModeRegsFull) (mem : Valid_Mem FGL FGL) (r_mem : ℕ)
    (align : MemAlignWitness (mainOfTable trace.program trace.mainTable)
      i.val (busLd trace i (Pilot.execRowOf trace i)).e1)
    (h_opcode : PureSpec.lwu_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_msg : loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i))
    (h_sel : mem.sel r_mem = 1) (h_wr : mem.wr r_mem = 0) :
    { core : InputsCore_lwu trace binding i
      { r1 := regidx.Regidx input.r1, rd := regidx.Regidx input.rd, imm := input.imm } //
      core.input = input } := by
  have h_read : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  let h_bytes : ∀ k : Fin 4, ∃ byte : BitVec 8,
      (binding i).mem[(Classical.choose h_r1).toNat +
        (BitVec.signExtend 64 input.imm).toNat + k.val]? = some byte := by
    intro k
    fin_cases k
    · exact ⟨input.data0, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1⟩
    · exact ⟨input.data1, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.1⟩
    · exact ⟨input.data2, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.1⟩
    · exact ⟨input.data3, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.1⟩
  have h_data0 : Classical.choose (h_bytes ⟨0, by decide⟩) = input.data0 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨0, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1)
  have h_data1 : Classical.choose (h_bytes ⟨1, by decide⟩) = input.data1 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨1, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.1)
  have h_data2 : Classical.choose (h_bytes ⟨2, by decide⟩) = input.data2 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨2, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.1)
  have h_data3 : Classical.choose (h_bytes ⟨3, by decide⟩) = input.data3 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨3, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.1)
  have h_input : loadInput_lwu (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.rd) input.imm h_r1 h_pc h_bytes = input := by
    cases input
    dsimp only [loadInput_lwu, storeRegBits]
    congr 1
  refine ⟨{
    h_input_r1 := h_r1
    h_input_pc := h_pc
    h_input_bytes := h_bytes
    regs := regs
    mem := mem
    r_mem := r_mem
    align := align
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_risc_v_assumptions := h_platform
    h_msg := h_msg
    h_mem_sel := h_sel
    h_mem_wr := h_wr }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value] using h_a0
  · exact h_input

/-- The PC agreement `Inputs_lwu` carries on top of `InputsCore_lwu`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_lwu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lwu trace i) : Type extends InputsCore_lwu trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `lwu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_lwu` bundles them. -/
structure RowData_lwu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_lwu trace i
  toDecode : Decode_lwu trace i toClaim
  toInputs : Inputs_lwu trace binding i toClaim

def toRowData_lwu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_lwu trace i) (dec : Decode_lwu trace i c)
    (ia : Inputs_lwu trace binding i c) : RowData_lwu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_lb (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_lb (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lb trace i) : Type where
  v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary : ℕ
  offset : ℕ
  env : Environment FGL
  h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SIGNEXTEND_B
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (1 : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB load-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` load/COPYB arm, lines 290-336/704-713).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomLd trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomLd trace i).rom.store_reg =
      if (storeRegBits c.rd).toNat = 0 then 0 else 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 (storeRegBits c.rd))
  h_b_offset_imm0 :
    (mainRowWithRomLd trace i).rom.b_offset_imm0 =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)

/-- Read the exact current-domain address; no default bytes or predicate repair. -/
noncomputable def loadInput_lb
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc)
    (h_bytes : ∀ k : Fin 1, ∃ byte : BitVec 8,
      state.mem[(Classical.choose h_r1).toNat + (BitVec.signExtend 64 imm).toNat + k.val]? =
        some byte) : PureSpec.LbInput where
  r1 := storeRegBits r1
  rd := storeRegBits rd
  imm := imm
  r1_val := Classical.choose h_r1
  PC := Classical.choose h_pc
  data0 := Classical.choose (h_bytes ⟨0, by decide⟩)

structure InputsCore_lb (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lb trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  h_input_bytes : ∀ k : Fin 1, ∃ byte : BitVec 8,
    (binding i).mem[(Classical.choose h_input_r1).toNat +
      (BitVec.signExtend 64 c.imm).toNat + k.val]? = some byte
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.lb_state_assumptions
    (loadInput_lb (binding i) c.r1 c.rd c.imm h_input_r1 h_input_pc h_input_bytes) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

noncomputable def InputsCore_lb.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lb trace i}
    (inputs : InputsCore_lb trace binding i c) : PureSpec.LbInput :=
  loadInput_lb (binding i) c.r1 c.rd c.imm
    inputs.h_input_r1 inputs.h_input_pc inputs.h_input_bytes

theorem InputsCore_lb.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lb trace i}
    (inputs : InputsCore_lb trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- Exact complete old load surface constructs the new record and the SAME input.
In particular no read/mappedness, PC, parse or equality premise is added, and the
unchanged unwrapped-address opcode predicate is transported in full. -/
def InputsCore_lb.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.LbInput)
    (regs : ModeRegsFull) (mem : Valid_Mem FGL FGL) (r_mem : ℕ)
    (h_opcode : PureSpec.lb_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_msg : loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i))
    (h_sel : mem.sel r_mem = 1) (h_wr : mem.wr r_mem = 0) :
    { core : InputsCore_lb trace binding i
      { r1 := regidx.Regidx input.r1, rd := regidx.Regidx input.rd, imm := input.imm } //
      core.input = input } := by
  have h_read : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  let h_bytes : ∀ k : Fin 1, ∃ byte : BitVec 8,
      (binding i).mem[(Classical.choose h_r1).toNat +
        (BitVec.signExtend 64 input.imm).toNat + k.val]? = some byte := by
    intro k
    fin_cases k
    · exact ⟨input.data0, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1⟩
  have h_data0 : Classical.choose (h_bytes ⟨0, by decide⟩) = input.data0 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨0, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1)
  have h_input : loadInput_lb (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.rd) input.imm h_r1 h_pc h_bytes = input := by
    cases input
    dsimp only [loadInput_lb, storeRegBits]
    congr 1
  refine ⟨{
    h_input_r1 := h_r1
    h_input_pc := h_pc
    h_input_bytes := h_bytes
    regs := regs
    mem := mem
    r_mem := r_mem
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_risc_v_assumptions := h_platform
    h_msg := h_msg
    h_mem_sel := h_sel
    h_mem_wr := h_wr }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value] using h_a0
  · exact h_input

/-- The PC agreement `Inputs_lb` carries on top of `InputsCore_lb`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_lb (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lb trace i) : Type extends InputsCore_lb trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `lb` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_lb` bundles them. -/
structure RowData_lb
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_lb trace i
  toDecode : Decode_lb trace i toClaim
  toInputs : Inputs_lb trace binding i toClaim

def toRowData_lb {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_lb trace i) (dec : Decode_lb trace i c)
    (ia : Inputs_lb trace binding i c) : RowData_lb trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_lh (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_lh (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lh trace i) : Type where
  v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary : ℕ
  offset : ℕ
  env : Environment FGL
  h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SIGNEXTEND_H
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (2 : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB load-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` load/COPYB arm, lines 290-336/704-713).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomLd trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomLd trace i).rom.store_reg =
      if (storeRegBits c.rd).toNat = 0 then 0 else 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 (storeRegBits c.rd))
  h_b_offset_imm0 :
    (mainRowWithRomLd trace i).rom.b_offset_imm0 =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)

/-- Read the exact current-domain address; no default bytes or predicate repair. -/
noncomputable def loadInput_lh
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc)
    (h_bytes : ∀ k : Fin 2, ∃ byte : BitVec 8,
      state.mem[(Classical.choose h_r1).toNat + (BitVec.signExtend 64 imm).toNat + k.val]? =
        some byte) : PureSpec.LhInput where
  r1 := storeRegBits r1
  rd := storeRegBits rd
  imm := imm
  r1_val := Classical.choose h_r1
  PC := Classical.choose h_pc
  data0 := Classical.choose (h_bytes ⟨0, by decide⟩)
  data1 := Classical.choose (h_bytes ⟨1, by decide⟩)

structure InputsCore_lh (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lh trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  h_input_bytes : ∀ k : Fin 2, ∃ byte : BitVec 8,
    (binding i).mem[(Classical.choose h_input_r1).toNat +
      (BitVec.signExtend 64 c.imm).toNat + k.val]? = some byte
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.lh_state_assumptions
    (loadInput_lh (binding i) c.r1 c.rd c.imm h_input_r1 h_input_pc h_input_bytes) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

noncomputable def InputsCore_lh.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lh trace i}
    (inputs : InputsCore_lh trace binding i c) : PureSpec.LhInput :=
  loadInput_lh (binding i) c.r1 c.rd c.imm
    inputs.h_input_r1 inputs.h_input_pc inputs.h_input_bytes

theorem InputsCore_lh.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lh trace i}
    (inputs : InputsCore_lh trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- Exact complete old load surface constructs the new record and the SAME input.
In particular no read/mappedness, PC, parse or equality premise is added, and the
unchanged unwrapped-address opcode predicate is transported in full. -/
def InputsCore_lh.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.LhInput)
    (regs : ModeRegsFull) (mem : Valid_Mem FGL FGL) (r_mem : ℕ)
    (h_opcode : PureSpec.lh_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_msg : loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i))
    (h_sel : mem.sel r_mem = 1) (h_wr : mem.wr r_mem = 0) :
    { core : InputsCore_lh trace binding i
      { r1 := regidx.Regidx input.r1, rd := regidx.Regidx input.rd, imm := input.imm } //
      core.input = input } := by
  have h_read : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  let h_bytes : ∀ k : Fin 2, ∃ byte : BitVec 8,
      (binding i).mem[(Classical.choose h_r1).toNat +
        (BitVec.signExtend 64 input.imm).toNat + k.val]? = some byte := by
    intro k
    fin_cases k
    · exact ⟨input.data0, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1⟩
    · exact ⟨input.data1, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.1⟩
  have h_data0 : Classical.choose (h_bytes ⟨0, by decide⟩) = input.data0 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨0, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1)
  have h_data1 : Classical.choose (h_bytes ⟨1, by decide⟩) = input.data1 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨1, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.1)
  have h_input : loadInput_lh (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.rd) input.imm h_r1 h_pc h_bytes = input := by
    cases input
    dsimp only [loadInput_lh, storeRegBits]
    congr 1
  refine ⟨{
    h_input_r1 := h_r1
    h_input_pc := h_pc
    h_input_bytes := h_bytes
    regs := regs
    mem := mem
    r_mem := r_mem
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_risc_v_assumptions := h_platform
    h_msg := h_msg
    h_mem_sel := h_sel
    h_mem_wr := h_wr }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value] using h_a0
  · exact h_input

/-- The PC agreement `Inputs_lh` carries on top of `InputsCore_lh`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_lh (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lh trace i) : Type extends InputsCore_lh trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `lh` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_lh` bundles them. -/
structure RowData_lh
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_lh trace i
  toDecode : Decode_lh trace i toClaim
  toInputs : Inputs_lh trace binding i toClaim

def toRowData_lh {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_lh trace i) (dec : Decode_lh trace i c)
    (ia : Inputs_lh trace binding i c) : RowData_lh trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_lw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_lw (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lw trace i) : Type where
  v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
  r_binary : ℕ
  offset : ℕ
  env : Environment FGL
  h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
  h_match :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SIGNEXTEND_W
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_width :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).ind_width
      i.val = (4 : FGL)
  -- #100 next-PC transition inputs (replace the exec artifacts): the next row
  -- exists, plus the COPYB load-row decode pins `set_pc = 0`,
  -- `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer `zib.j(4, 4)`, no `set_pc()`;
  -- cf. `RowShape/Contract.lean` load/COPYB arm, lines 290-336/704-713).
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_store_ind :
    (mainRowWithRomLd trace i).rom.store_ind = 0
  h_store_reg :
    (mainRowWithRomLd trace i).rom.store_reg =
      if (storeRegBits c.rd).toNat = 0 then 0 else 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 (storeRegBits c.rd))
  h_b_offset_imm0 :
    (mainRowWithRomLd trace i).rom.b_offset_imm0 =
      ((BitVec.signExtend 64 c.imm).toInt : FGL)

/-- Read the exact current-domain address; no default bytes or predicate repair. -/
noncomputable def loadInput_lw
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state)
    (h_pc : ∃ pc : BitVec 64, state.regs.get? Register.PC = some pc)
    (h_bytes : ∀ k : Fin 4, ∃ byte : BitVec 8,
      state.mem[(Classical.choose h_r1).toNat + (BitVec.signExtend 64 imm).toNat + k.val]? =
        some byte) : PureSpec.LwInput where
  r1 := storeRegBits r1
  rd := storeRegBits rd
  imm := imm
  r1_val := Classical.choose h_r1
  PC := Classical.choose h_pc
  data0 := Classical.choose (h_bytes ⟨0, by decide⟩)
  data1 := Classical.choose (h_bytes ⟨1, by decide⟩)
  data2 := Classical.choose (h_bytes ⟨2, by decide⟩)
  data3 := Classical.choose (h_bytes ⟨3, by decide⟩)

structure InputsCore_lw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lw trace i) : Type where
  h_input_r1 : ∃ value : BitVec 64,
    read_xreg (regidx_to_fin c.r1) (binding i) = EStateM.Result.ok value (binding i)
  h_input_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc
  h_input_bytes : ∀ k : Fin 4, ∃ byte : BitVec 8,
    (binding i).mem[(Classical.choose h_input_r1).toNat +
      (BitVec.signExtend 64 c.imm).toNat + k.val]? = some byte
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.lw_state_assumptions
    (loadInput_lw (binding i) c.r1 c.rd c.imm h_input_r1 h_input_pc h_input_bytes) (binding i)
  h_a0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo (Classical.choose h_input_r1)
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

noncomputable def InputsCore_lw.input
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lw trace i}
    (inputs : InputsCore_lw trace binding i c) : PureSpec.LwInput :=
  loadInput_lw (binding i) c.r1 c.rd c.imm
    inputs.h_input_r1 inputs.h_input_pc inputs.h_input_bytes

theorem InputsCore_lw.input_pc_read
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions} {c : Claim_lw trace i}
    (inputs : InputsCore_lw trace binding i c) :
    (binding i).regs.get? Register.PC = some inputs.input.PC :=
  Classical.choose_spec inputs.h_input_pc

/-- Exact complete old load surface constructs the new record and the SAME input.
In particular no read/mappedness, PC, parse or equality premise is added, and the
unchanged unwrapped-address opcode predicate is transported in full. -/
def InputsCore_lw.of_state_assumptions
    {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    (i : Fin trace.numInstructions) (input : PureSpec.LwInput)
    (regs : ModeRegsFull) (mem : Valid_Mem FGL FGL) (r_mem : ℕ)
    (h_opcode : PureSpec.lw_state_assumptions input (binding i))
    (h_a0 : (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo input.r1_val)
    (h_platform : RISC_V_assumptions (binding i)
      regs.mstatus regs.pmaRegion regs.misa regs.mseccfg)
    (h_msg : loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i))
    (h_sel : mem.sel r_mem = 1) (h_wr : mem.wr r_mem = 0) :
    { core : InputsCore_lw trace binding i
      { r1 := regidx.Regidx input.r1, rd := regidx.Regidx input.rd, imm := input.imm } //
      core.input = input } := by
  have h_read : read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
      EStateM.Result.ok input.r1_val (binding i) := by
    rw [← rX_read_xreg_equiv (binding i) (regidx.Regidx input.r1)
      (regidx_to_fin (regidx.Regidx input.r1)) (by simp [regidx_to_fin])]
    exact h_opcode.2.1
  let h_r1 : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin (regidx.Regidx input.r1)) (binding i) =
        EStateM.Result.ok value (binding i) := ⟨input.r1_val, h_read⟩
  let h_pc : ∃ pc : BitVec 64, (binding i).regs.get? Register.PC = some pc :=
    ⟨input.PC, h_opcode.1⟩
  have h_value : Classical.choose h_r1 = input.r1_val :=
    (EStateM.Result.ok.inj ((Classical.choose_spec h_r1).symm.trans h_read)).1
  have h_pc_value : Classical.choose h_pc = input.PC :=
    Option.some.inj ((Classical.choose_spec h_pc).symm.trans h_opcode.1)
  let h_bytes : ∀ k : Fin 4, ∃ byte : BitVec 8,
      (binding i).mem[(Classical.choose h_r1).toNat +
        (BitVec.signExtend 64 input.imm).toNat + k.val]? = some byte := by
    intro k
    fin_cases k
    · exact ⟨input.data0, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1⟩
    · exact ⟨input.data1, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.1⟩
    · exact ⟨input.data2, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.1⟩
    · exact ⟨input.data3, by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.1⟩
  have h_data0 : Classical.choose (h_bytes ⟨0, by decide⟩) = input.data0 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨0, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.1)
  have h_data1 : Classical.choose (h_bytes ⟨1, by decide⟩) = input.data1 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨1, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.1)
  have h_data2 : Classical.choose (h_bytes ⟨2, by decide⟩) = input.data2 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨2, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.1)
  have h_data3 : Classical.choose (h_bytes ⟨3, by decide⟩) = input.data3 := by
    apply Option.some.inj
    exact (Classical.choose_spec (h_bytes ⟨3, by decide⟩)).symm.trans
      (by simpa only [h_value, Nat.add_zero] using h_opcode.2.2.2.2.2.1)
  have h_input : loadInput_lw (binding i) (regidx.Regidx input.r1)
      (regidx.Regidx input.rd) input.imm h_r1 h_pc h_bytes = input := by
    cases input
    dsimp only [loadInput_lw, storeRegBits]
    congr 1
  refine ⟨{
    h_input_r1 := h_r1
    h_input_pc := h_pc
    h_input_bytes := h_bytes
    regs := regs
    mem := mem
    r_mem := r_mem
    h_opcode_assumptions := ?_
    h_a0_value := ?_
    h_risc_v_assumptions := h_platform
    h_msg := h_msg
    h_mem_sel := h_sel
    h_mem_wr := h_wr }, ?_⟩
  · simpa only [h_input] using h_opcode
  · simpa only [h_value] using h_a0
  · exact h_input

/-- The PC agreement `Inputs_lw` carries on top of `InputsCore_lw`.

    No longer assumed at the root: `root_soundness` takes `InputsCore_<op>` and the
    two-premise `SegmentPcChain`, from which the dispatcher builds this field via
    `h_pc_bridge_of_pcBridge`, from the per-row PC agreement the induction in
    `stepSound_of_programDecodes` carries.  Kept as a field so every consumer reads it unchanged. -/
structure Inputs_lw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lw trace i) : Type extends InputsCore_lw trace binding i c where
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = (Classical.choose h_input_pc).toNat

/-- Per-op residual bundle for the `lw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_lw` bundles them. -/
structure RowData_lw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_lw trace i
  toDecode : Decode_lw trace i toClaim
  toInputs : Inputs_lw trace binding i toClaim

def toRowData_lw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_lw trace i) (dec : Decode_lw trace i c)
    (ia : Inputs_lw trace binding i c) : RowData_lw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

end ZiskFv.Compliance
