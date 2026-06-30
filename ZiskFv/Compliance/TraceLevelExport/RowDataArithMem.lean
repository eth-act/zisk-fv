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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure Inputs_add (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = add_input.PC.toNat
  h_pc_bound : add_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  h_b_src_imm :
    (mainRowWithRomSub trace i).rom.b_src_imm = 1
  h_b_imm :
    BitVec.signExtend 64 c.imm =
      BitVec.ofNat 64
        (((mainRowWithRomSub trace i).rom.b_offset_imm0).val
          + ((mainRowWithRomSub trace i).rom.b_imm1).val * 4294967296)

structure Inputs_addi (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addi trace i) : Type where
  addi_input : PureSpec.AddiInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok addi_input.r1_val (binding i)
  h_input_imm : addi_input.imm = c.imm
  h_input_pc : (binding i).regs.get? Register.PC = .some addi_input.PC
  h_input_rd : addi_input.rd = regidx_to_fin c.rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = addi_input.PC.toNat
  h_pc_bound : addi_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure Inputs_subw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = subw_input.PC.toNat
  h_pc_bound : subw_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure Inputs_addw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_b_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r2))
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = addw_input.PC.toNat
  h_pc_bound : addw_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  h_b_src_imm :
    (mainRowWithRomSub trace i).rom.b_src_imm = 1
  h_b_imm :
    BitVec.signExtend 64 c.imm =
      BitVec.ofNat 64
        (((mainRowWithRomSub trace i).rom.b_offset_imm0).val
          + ((mainRowWithRomSub trace i).rom.b_imm1).val * 4294967296)

structure Inputs_addiw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_addiw trace i) : Type where
  addiw_input : PureSpec.AddiwInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok addiw_input.r1_val (binding i)
  h_input_imm : addiw_input.imm = c.imm
  h_input_pc : (binding i).regs.get? Register.PC = .some addiw_input.PC
  h_input_rd : addiw_input.rd = regidx_to_fin c.rd
  h_a_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_a_hi_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
          (regidx_to_fin c.r1))
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = addiw_input.PC.toNat
  h_pc_bound : addiw_input.PC.toNat < GL_prime - 4

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

structure Inputs_lui (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lui trace i) : Type where
  lui_input : PureSpec.LuiInput
  h_input_imm : lui_input.imm = c.imm
  h_input_rd : lui_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some lui_input.PC
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = lui_input.PC.toNat
  h_pc_bound : lui_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomLui trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  -- #100 next-PC transition inputs (replace the exec artifacts; AUIPC already
  -- carries h_set_pc above): the next row exists, plus the AUIPC FLAG-row jmp
  -- pin `jmp_offset1 = 4` (Rust lowerer `zib.j(4, imm)`; cf.
  -- `RowShape/Contract.lean` AUIPC arm, line 246). With set_pc=0 and flag=1
  -- the handshake mux selects the taken offset `jmp_offset1 = 4`, so
  -- next_pc = pc + 4. `flag = 1` is NOT pinned here: it is derived in
  -- `stepStrong_auipc` from the OP_FLAG decode pins + `internal_op0_sets_flag`.
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_jmp1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4

structure Inputs_auipc (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_auipc trace i) : Type where
  auipc_input : PureSpec.AuipcInput
  h_input_imm : auipc_input.imm = c.imm
  h_input_rd : auipc_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some auipc_input.PC
  h_offset_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
        i.val).val
      = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = auipc_input.PC.toNat
  -- #100: the JAL/AUIPC-style PC-trajectory no-wrap bound on the `pc + 4`
  -- sequential successor (mirrors `Pilot.ofNat_fgl_pc_plus_4_eq`'s precondition),
  -- ruling out FGL wrap on the next PC. Replaces the cross-world `h_nextPC_matches`,
  -- which is now derived via `Pilot.flag_path_nextPC_discharged`.
  h_pc_bound : auipc_input.PC.toNat < GL_prime - 4
  h_no_wrap : auipc_input.PC.toNat
    + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
      < GL_prime
  h_pc_offset_lt_2_32 :
    (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
      < 4294967296

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure Inputs_mulw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = mulw_input.PC.toNat
  h_pc_bound : mulw_input.PC.toNat < GL_prime - 4
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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure Inputs_mul (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  -- #100 next-PC transition inputs (consumed by `mulEnvOf`): the committed Main `pc`
  -- column at row `i` equals the Sail PC (JAL/AUIPC-class provenance bridge), the
  -- `pc + 4` successor does not wrap FGL, and the bus exec_row is the real committed
  -- exec-bus row `execRowOf`. None asserts `exec_row[1].pc = …`; the next-PC fact is
  -- derived from the transition certificate. The value-defect gate is untouched.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = mul_input.PC.toNat
  h_pc_bound : mul_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure Inputs_mulh (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_sign_a : (v.na r_a).val
    = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0
  h_sign_b : (v.nb r_a).val
    = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
        (v.b_2 r_a).val (v.b_3 r_a).val then 1 else 0
  -- #100 next-PC transition inputs (consumed by `mulhEnvOf`); see `Inputs_mul`.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = mulh_input.PC.toNat
  h_pc_bound : mulh_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure Inputs_mulhsu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_sign_a : (v.na r_a).val
    = if 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
        (v.a_2 r_a).val (v.a_3 r_a).val then 1 else 0
  -- #100 next-PC transition inputs (consumed by `mulhsuEnvOf`); see `Inputs_mul`.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = mulhsu_input.PC.toNat
  h_pc_bound : mulhsu_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_DIV
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure Inputs_div (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_div trace i) : Type where
  div_input : PureSpec.DivInput
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_match_primary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a)
  -- #100: value/data promises only — `nextPC_matches` DERIVED in `divEnvOf`.
  promises : RTypePromisesNoNextPC
      (binding i) div_input.r1_val div_input.r2_val div_input.rd div_input.PC
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
      ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
          + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
              * (65536 * 65536 * 65536)) * 0 = 0
        ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
        ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0
  h_rs1_value :
    div_input.r1_val.toInt
      = (ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
          - (v.np r_a).val * (2:ℤ)^64
  h_rs2_value :
    div_input.r2_val.toInt
      = (ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
          - (v.nb r_a).val * (2:ℤ)^64
  h_r_le :
    ((ZiskFv.PackedBitVec.MulNoWrap.packed4
        (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
      - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ div_input.r2_val.toInt.natAbs
  h_r_sign :
    0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
          - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt
  h_not_forge :
    ¬ (div_input.r2_val.toInt ≠ 0
        ∧ (ZiskFv.Compliance.Defects.signedRemainderInt v r_a).natAbs
          = div_input.r2_val.toInt.natAbs)
  -- #100 next-PC transition inputs (consumed by `divEnvOf`); see `Inputs_mul`.
  -- These are next-PC plumbing only and leave the DivRemForge value gate untouched.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = div_input.PC.toNat
  h_pc_bound : div_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_REM
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure Inputs_rem (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  -- #100 next-PC transition inputs (consumed by `remEnvOf`); see `Inputs_mul`.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = rem_input.PC.toNat
  h_pc_bound : rem_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_DIV_W
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure Inputs_divw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  -- #100 next-PC transition inputs (consumed by `divwEnvOf`); see `Inputs_mul`.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = divw_input.PC.toNat
  h_pc_bound : divw_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_REM_W
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busSub trace i (Pilot.execRowOf trace i)).e2
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace i (Pilot.execRowOf trace i)).e2

structure Inputs_remw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  -- #100 next-PC transition inputs (consumed by `remwEnvOf`); see `Inputs_mul`.
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val = remw_input.PC.toNat
  h_pc_bound : remw_input.PC.toNat < GL_prime - 4

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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure Inputs_mulhu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = mulhu_input.PC.toNat
  h_pc_bound : mulhu_input.PC.toNat < GL_prime - 4
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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure Inputs_divu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = divu_input.PC.toNat
  h_pc_bound : divu_input.PC.toNat < GL_prime - 4
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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure Inputs_divuw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = divuw_input.PC.toNat
  h_pc_bound : divuw_input.PC.toNat < GL_prime - 4
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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure Inputs_remu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = remu_input.PC.toNat
  h_pc_bound : remu_input.PC.toNat < GL_prime - 4
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
  h_store_offset :
    (mainRowWithRomSub trace i).rom.store_offset =
      Transpiler.ind (regidx_to_fin c.rd)

structure Inputs_remuw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = remuw_input.PC.toNat
  h_pc_bound : remuw_input.PC.toNat < GL_prime - 4
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

structure Claim_sb (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  sb_input : PureSpec.SbInput

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

structure Inputs_sb (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sb trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sb_state_assumptions c.sb_input (binding i)
  h_store_addr_arith :
    ((mainRowWithRomSt trace i).rom.store_offset + (mainRowWithRomSt trace i).core.a_0).toNat =
      (c.sb_input.r1_val + BitVec.signExtend 64 c.sb_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo c.sb_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi c.sb_input.r2_val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.sb_input.PC.toNat
  h_pc_bound : c.sb_input.PC.toNat < GL_prime - 4
  h_m1 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 1]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 1 : BitVec 8)
  h_m2 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 2]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 2 : BitVec 8)
  h_m3 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 3]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 3 : BitVec 8)
  h_m4 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 4 : BitVec 8)
  h_m5 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 5 : BitVec 8)
  h_m6 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 6 : BitVec 8)
  h_m7 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 7 : BitVec 8)

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
  sh_input : PureSpec.ShInput

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

structure Inputs_sh (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sh trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sh_state_assumptions c.sh_input (binding i)
  h_store_addr_arith :
    ((mainRowWithRomSt trace i).rom.store_offset + (mainRowWithRomSt trace i).core.a_0).toNat =
      (c.sh_input.r1_val + BitVec.signExtend 64 c.sh_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo c.sh_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi c.sh_input.r2_val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.sh_input.PC.toNat
  h_pc_bound : c.sh_input.PC.toNat < GL_prime - 4
  h_m2 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 2]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 2 : BitVec 8)
  h_m3 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 3]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 3 : BitVec 8)
  h_m4 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 4 : BitVec 8)
  h_m5 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 5 : BitVec 8)
  h_m6 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 6 : BitVec 8)
  h_m7 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 7 : BitVec 8)

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
  sw_input : PureSpec.SwInput

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

structure Inputs_sw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sw trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sw_state_assumptions c.sw_input (binding i)
  h_store_addr_arith :
    ((mainRowWithRomSt trace i).rom.store_offset + (mainRowWithRomSt trace i).core.a_0).toNat =
      (c.sw_input.r1_val + BitVec.signExtend 64 c.sw_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo c.sw_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi c.sw_input.r2_val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.sw_input.PC.toNat
  h_pc_bound : c.sw_input.PC.toNat < GL_prime - 4
  h_m4 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 4 : BitVec 8)
  h_m5 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 5 : BitVec 8)
  h_m6 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 6 : BitVec 8)
  h_m7 : (binding i).mem[(busSt trace i (Pilot.execRowOf trace i)).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace i (Pilot.execRowOf trace i)).e2 7 : BitVec 8)

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
  sd_input : PureSpec.SdInput

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

structure Inputs_sd (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_sd trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sd_state_assumptions c.sd_input (binding i)
  h_store_addr_arith :
    ((mainRowWithRomSt trace i).rom.store_offset + (mainRowWithRomSt trace i).core.a_0).toNat =
      (c.sd_input.r1_val + BitVec.signExtend 64 c.sd_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo c.sd_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi c.sd_input.r2_val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.sd_input.PC.toNat
  h_pc_bound : c.sd_input.PC.toNat < GL_prime - 4

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
  ld_input : PureSpec.LdInput

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
    (mainRowWithRomLd trace i).rom.store_reg = 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.ld_input.rd)

structure Inputs_ld (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_ld trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.ld_state_assumptions c.ld_input (binding i)
  h_load_addr_arith :
    ((mainRowWithRomLd trace i).rom.b_offset_imm0 + (mainRowWithRomLd trace i).core.a_0).toNat =
      c.ld_input.r1_val.toNat + (BitVec.signExtend 64 c.ld_input.imm).toNat
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.ld_input.PC.toNat
  h_pc_bound : c.ld_input.PC.toNat < GL_prime - 4
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace i (Pilot.execRowOf trace i)).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

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
  lbu_input : PureSpec.LbuInput

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
    (mainRowWithRomLd trace i).rom.store_reg = 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lbu_input.rd)

structure Inputs_lbu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lbu trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace i (Pilot.execRowOf trace i)).e1
  h_opcode_assumptions : PureSpec.lbu_state_assumptions c.lbu_input (binding i)
  h_load_addr_arith :
    ((mainRowWithRomLd trace i).rom.b_offset_imm0 + (mainRowWithRomLd trace i).core.a_0).toNat =
      c.lbu_input.r1_val.toNat + (BitVec.signExtend 64 c.lbu_input.imm).toNat
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.lbu_input.PC.toNat
  h_pc_bound : c.lbu_input.PC.toNat < GL_prime - 4
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace i (Pilot.execRowOf trace i)).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

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
  lhu_input : PureSpec.LhuInput

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
    (mainRowWithRomLd trace i).rom.store_reg = 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lhu_input.rd)

structure Inputs_lhu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lhu trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace i (Pilot.execRowOf trace i)).e1
  h_opcode_assumptions : PureSpec.lhu_state_assumptions c.lhu_input (binding i)
  h_load_addr_arith :
    ((mainRowWithRomLd trace i).rom.b_offset_imm0 + (mainRowWithRomLd trace i).core.a_0).toNat =
      c.lhu_input.r1_val.toNat + (BitVec.signExtend 64 c.lhu_input.imm).toNat
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.lhu_input.PC.toNat
  h_pc_bound : c.lhu_input.PC.toNat < GL_prime - 4
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace i (Pilot.execRowOf trace i)).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

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
  lwu_input : PureSpec.LwuInput

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
    (mainRowWithRomLd trace i).rom.store_reg = 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lwu_input.rd)

structure Inputs_lwu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lwu trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace i (Pilot.execRowOf trace i)).e1
  h_opcode_assumptions : PureSpec.lwu_state_assumptions c.lwu_input (binding i)
  h_load_addr_arith :
    ((mainRowWithRomLd trace i).rom.b_offset_imm0 + (mainRowWithRomLd trace i).core.a_0).toNat =
      c.lwu_input.r1_val.toNat + (BitVec.signExtend 64 c.lwu_input.imm).toNat
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.lwu_input.PC.toNat
  h_pc_bound : c.lwu_input.PC.toNat < GL_prime - 4
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace i (Pilot.execRowOf trace i)).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

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
  lb_input : PureSpec.LbInput

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
    (mainRowWithRomLd trace i).rom.store_reg = 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lb_input.rd)

structure Inputs_lb (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lb trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.lb_state_assumptions c.lb_input (binding i)
  h_load_addr_arith :
    ((mainRowWithRomLd trace i).rom.b_offset_imm0 + (mainRowWithRomLd trace i).core.a_0).toNat =
      c.lb_input.r1_val.toNat + (BitVec.signExtend 64 c.lb_input.imm).toNat
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.lb_input.PC.toNat
  h_pc_bound : c.lb_input.PC.toNat < GL_prime - 4
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace i (Pilot.execRowOf trace i)).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

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
  lh_input : PureSpec.LhInput

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
    (mainRowWithRomLd trace i).rom.store_reg = 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lh_input.rd)

structure Inputs_lh (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lh trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.lh_state_assumptions c.lh_input (binding i)
  h_load_addr_arith :
    ((mainRowWithRomLd trace i).rom.b_offset_imm0 + (mainRowWithRomLd trace i).core.a_0).toNat =
      c.lh_input.r1_val.toNat + (BitVec.signExtend 64 c.lh_input.imm).toNat
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.lh_input.PC.toNat
  h_pc_bound : c.lh_input.PC.toNat < GL_prime - 4
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace i (Pilot.execRowOf trace i)).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

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
  lw_input : PureSpec.LwInput

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
    (mainRowWithRomLd trace i).rom.store_reg = 1
  h_b_src_ind :
    (mainRowWithRomLd trace i).rom.b_src_ind = 1
  h_store_offset :
    (mainRowWithRomLd trace i).rom.store_offset = Transpiler.ind (Transpiler.regidxOfBitVec5 c.lw_input.rd)

structure Inputs_lw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (c : Claim_lw trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.lw_state_assumptions c.lw_input (binding i)
  h_load_addr_arith :
    ((mainRowWithRomLd trace i).rom.b_offset_imm0 + (mainRowWithRomLd trace i).core.a_0).toNat =
      c.lw_input.r1_val.toNat + (BitVec.signExtend 64 c.lw_input.imm).toNat
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_pc_bridge :
    ((mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.lw_input.PC.toNat
  h_pc_bound : c.lw_input.PC.toNat < GL_prime - 4
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace i (Pilot.execRowOf trace i)).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

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
