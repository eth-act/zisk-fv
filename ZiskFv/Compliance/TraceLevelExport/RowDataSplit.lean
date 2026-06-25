import ZiskFv.Compliance.TraceLevelExport.RowDataAluShift
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem
import ZiskFv.Compliance.TraceLevelExport.RowDataControl

/-!
# Per-op claim / decode / inputs split (root_soundness 3-way refactor)

For each RV64IM op, `RowData_<op>` is split into `Claim_<op>` (ziskStep claim),
`Decode_<op>` (rowDecodes), `Inputs_<op>` (inputsAgree), with `toRowData_<op>`
reassembling the untouched flat `RowData_<op>`. Generated from the validated
`add` template (workflow wwvvvytoj). The 63 `stepStrong_<op>` proofs are unchanged.
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

seal mulwArow mulhuArow divuArow divuwArow remuArow remuwArow

set_option maxHeartbeats 8000000

structure Claim_sub (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sub (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sub trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SUB
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sub (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sub trace i) : Type where
  sub_input : PureSpec.SubInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok sub_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok sub_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some sub_input.PC
  h_input_rd : sub_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
  h_rd_idx :
    sub_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_sub {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sub trace i) (dec : Decode_sub trace binding i c)
    (ia : Inputs_sub trace binding i c) : RowData_sub trace binding i where
  sub_input := ia.sub_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_and (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_and (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_and trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_AND
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_and (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_and trace i) : Type where
  and_input : PureSpec.AndInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok and_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok and_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some and_input.PC
  h_input_rd : and_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_and_pure and_input).nextPC
  h_rd_idx :
    and_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_and {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_and trace i) (dec : Decode_and trace binding i c)
    (ia : Inputs_and trace binding i c) : RowData_and trace binding i where
  and_input := ia.and_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_or (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_or (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_or trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_OR
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_or (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_or trace i) : Type where
  or_input : PureSpec.OrInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok or_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok or_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some or_input.PC
  h_input_rd : or_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_or_pure or_input).nextPC
  h_rd_idx :
    or_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_or {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_or trace i) (dec : Decode_or trace binding i c)
    (ia : Inputs_or trace binding i c) : RowData_or trace binding i where
  or_input := ia.or_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_xor (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_xor (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_xor trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_XOR
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_xor (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_xor trace i) : Type where
  xor_input : PureSpec.XorInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok xor_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok xor_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some xor_input.PC
  h_input_rd : xor_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC
  h_rd_idx :
    xor_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_xor {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_xor trace i) (dec : Decode_xor trace binding i c)
    (ia : Inputs_xor trace binding i c) : RowData_xor trace binding i where
  xor_input := ia.xor_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_slt (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_slt (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_slt trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_slt (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_slt trace i) : Type where
  slt_input : PureSpec.SltInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok slt_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok slt_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some slt_input.PC
  h_input_rd : slt_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC
  h_rd_idx :
    slt_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_slt {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_slt trace i) (dec : Decode_slt trace binding i c)
    (ia : Inputs_slt trace binding i c) : RowData_slt trace binding i where
  slt_input := ia.slt_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_sltu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sltu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sltu trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sltu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sltu trace i) : Type where
  sltu_input : PureSpec.SltuInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok sltu_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok sltu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some sltu_input.PC
  h_input_rd : sltu_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC
  h_rd_idx :
    sltu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_sltu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sltu trace i) (dec : Decode_sltu trace binding i c)
    (ia : Inputs_sltu trace binding i c) : RowData_sltu trace binding i where
  sltu_input := ia.sltu_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_andi (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_andi (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_andi trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_AND
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_andi (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_andi trace i) : Type where
  andi_input : PureSpec.AndiInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok andi_input.r1_val (binding i)
  h_input_imm : andi_input.imm = c.imm
  h_input_pc : (binding i).regs.get? Register.PC = .some andi_input.PC
  h_input_rd : andi_input.rd = regidx_to_fin c.rd
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
  h_andi_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val andi_input.imm
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
  h_rd_idx :
    andi_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_andi {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_andi trace i) (dec : Decode_andi trace binding i c)
    (ia : Inputs_andi trace binding i c) : RowData_andi trace binding i where
  andi_input := ia.andi_input
  r1 := c.r1
  rd := c.rd
  imm := c.imm
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_imm := ia.h_input_imm
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_andi_subset := ia.h_andi_subset
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_ori (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_ori (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_ori trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_OR
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_ori (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_ori trace i) : Type where
  ori_input : PureSpec.OriInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok ori_input.r1_val (binding i)
  h_input_imm : ori_input.imm = c.imm
  h_input_pc : (binding i).regs.get? Register.PC = .some ori_input.PC
  h_input_rd : ori_input.rd = regidx_to_fin c.rd
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
  h_ori_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val ori_input.imm
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
  h_rd_idx :
    ori_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_ori {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_ori trace i) (dec : Decode_ori trace binding i c)
    (ia : Inputs_ori trace binding i c) : RowData_ori trace binding i where
  ori_input := ia.ori_input
  r1 := c.r1
  rd := c.rd
  imm := c.imm
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_imm := ia.h_input_imm
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_ori_subset := ia.h_ori_subset
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_xori (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_xori (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_xori trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_XOR
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_xori (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_xori trace i) : Type where
  xori_input : PureSpec.XoriInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok xori_input.r1_val (binding i)
  h_input_imm : xori_input.imm = c.imm
  h_input_pc : (binding i).regs.get? Register.PC = .some xori_input.PC
  h_input_rd : xori_input.rd = regidx_to_fin c.rd
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
  h_xori_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val xori_input.imm
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
  h_rd_idx :
    xori_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_xori {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_xori trace i) (dec : Decode_xori trace binding i c)
    (ia : Inputs_xori trace binding i c) : RowData_xori trace binding i where
  xori_input := ia.xori_input
  r1 := c.r1
  rd := c.rd
  imm := c.imm
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_imm := ia.h_input_imm
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_xori_subset := ia.h_xori_subset
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_slti (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_slti (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_slti trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_slti (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_slti trace i) : Type where
  slti_input : PureSpec.SltiInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok slti_input.r1_val (binding i)
  h_input_imm : slti_input.imm = c.imm
  h_input_pc : (binding i).regs.get? Register.PC = .some slti_input.PC
  h_input_rd : slti_input.rd = regidx_to_fin c.rd
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
  h_slti_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val slti_input.imm
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
  h_rd_idx :
    slti_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_slti {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_slti trace i) (dec : Decode_slti trace binding i c)
    (ia : Inputs_slti trace binding i c) : RowData_slti trace binding i where
  slti_input := ia.slti_input
  r1 := c.r1
  rd := c.rd
  imm := c.imm
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_imm := ia.h_input_imm
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_slti_subset := ia.h_slti_subset
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_sltiu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sltiu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sltiu trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sltiu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sltiu trace i) : Type where
  sltiu_input : PureSpec.SltiuInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok sltiu_input.r1_val (binding i)
  h_input_imm : sltiu_input.imm = c.imm
  h_input_pc : (binding i).regs.get? Register.PC = .some sltiu_input.PC
  h_input_rd : sltiu_input.rd = regidx_to_fin c.rd
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
  h_sltiu_subset : itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val sltiu_input.imm
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
  h_rd_idx :
    sltiu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_sltiu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sltiu trace i) (dec : Decode_sltiu trace binding i c)
    (ia : Inputs_sltiu trace binding i c) : RowData_sltiu trace binding i where
  sltiu_input := ia.sltiu_input
  r1 := c.r1
  rd := c.rd
  imm := c.imm
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_imm := ia.h_input_imm
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_sltiu_subset := ia.h_sltiu_subset
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_add (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_add (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_add (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_add_pure add_input).nextPC
  h_rd_idx :
    add_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_add {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_add trace i) (dec : Decode_add trace binding i c)
    (ia : Inputs_add trace binding i c) : RowData_add trace binding i where
  add_input := ia.add_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_addi (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_addi (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_addi (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_addi_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val addi_input.imm
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
  h_rd_idx :
    addi_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_addi {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_addi trace i) (dec : Decode_addi trace binding i c)
    (ia : Inputs_addi trace binding i c) : RowData_addi trace binding i where
  addi_input := ia.addi_input
  r1 := c.r1
  rd := c.rd
  imm := c.imm
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_set_pc := dec.h_set_pc
  h_input_r1 := ia.h_input_r1
  h_input_imm := ia.h_input_imm
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_addi_subset := ia.h_addi_subset
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_sll (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sll (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sll trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sll (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sll trace i) : Type where
  sll_input : PureSpec.SllInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok sll_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok sll_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some sll_input.PC
  h_input_rd : sll_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
  h_rd_idx :
    sll_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_sll {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sll trace i) (dec : Decode_sll trace binding i c)
    (ia : Inputs_sll trace binding i c) : RowData_sll trace binding i where
  sll_input := ia.sll_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_srl (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_srl (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_srl trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_srl (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_srl trace i) : Type where
  srl_input : PureSpec.SrlInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok srl_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok srl_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some srl_input.PC
  h_input_rd : srl_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
  h_rd_idx :
    srl_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_srl {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_srl trace i) (dec : Decode_srl trace binding i c)
    (ia : Inputs_srl trace binding i c) : RowData_srl trace binding i where
  srl_input := ia.srl_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_sra (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sra (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sra trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sra (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sra trace i) : Type where
  sra_input : PureSpec.SraInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok sra_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok sra_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some sra_input.PC
  h_input_rd : sra_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
  h_rd_idx :
    sra_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_sra {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sra trace i) (dec : Decode_sra trace binding i c)
    (ia : Inputs_sra trace binding i c) : RowData_sra trace binding i where
  sra_input := ia.sra_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_slli (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  shamt : BitVec 6
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_slli (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_slli trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      shamt_b_lo c.shamt
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_slli (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_slli trace i) : Type where
  slli_input : PureSpec.SlliInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok slli_input.r1_val (binding i)
  h_input_shamt : slli_input.shamt = c.shamt
  h_input_pc : (binding i).regs.get? Register.PC = .some slli_input.PC
  h_input_rd : slli_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
  h_rd_idx :
    slli_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_slli {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_slli trace i) (dec : Decode_slli trace binding i c)
    (ia : Inputs_slli trace binding i c) : RowData_slli trace binding i where
  slli_input := ia.slli_input
  r1 := c.r1
  rd := c.rd
  shamt := c.shamt
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_shamt := ia.h_input_shamt
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := dec.h_b_lo_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_srli (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  shamt : BitVec 6
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_srli (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_srli trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      shamt_b_lo c.shamt
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_srli (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_srli trace i) : Type where
  srli_input : PureSpec.SrliInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok srli_input.r1_val (binding i)
  h_input_shamt : srli_input.shamt = c.shamt
  h_input_pc : (binding i).regs.get? Register.PC = .some srli_input.PC
  h_input_rd : srli_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
  h_rd_idx :
    srli_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_srli {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_srli trace i) (dec : Decode_srli trace binding i c)
    (ia : Inputs_srli trace binding i c) : RowData_srli trace binding i where
  srli_input := ia.srli_input
  r1 := c.r1
  rd := c.rd
  shamt := c.shamt
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_shamt := ia.h_input_shamt
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := dec.h_b_lo_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_srai (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  shamt : BitVec 6
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_srai (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_srai trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_b_lo_t :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      shamt_b_lo c.shamt
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_srai (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_srai trace i) : Type where
  srai_input : PureSpec.SraiInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok srai_input.r1_val (binding i)
  h_input_shamt : srai_input.shamt = c.shamt
  h_input_pc : (binding i).regs.get? Register.PC = .some srai_input.PC
  h_input_rd : srai_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
  h_rd_idx :
    srai_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_srai {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_srai trace i) (dec : Decode_srai trace binding i c)
    (ia : Inputs_srai trace binding i c) : RowData_srai trace binding i where
  srai_input := ia.srai_input
  r1 := c.r1
  rd := c.rd
  shamt := c.shamt
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_shamt := ia.h_input_shamt
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := dec.h_b_lo_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_subw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_subw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_subw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
  h_rd_idx :
    subw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_subw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_subw trace i) (dec : Decode_subw trace binding i c)
    (ia : Inputs_subw trace binding i c) : RowData_subw trace binding i where
  subw_input := ia.subw_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_addw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_addw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_addw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
  h_rd_idx :
    addw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_addw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_addw trace i) (dec : Decode_addw trace binding i c)
    (ia : Inputs_addw trace binding i c) : RowData_addw trace binding i where
  addw_input := ia.addw_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_addiw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_addiw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_addiw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_addiw_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val addiw_input.imm
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
  h_rd_idx :
    addiw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_addiw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_addiw trace i) (dec : Decode_addiw trace binding i c)
    (ia : Inputs_addiw trace binding i c) : RowData_addiw trace binding i where
  addiw_input := ia.addiw_input
  r1 := c.r1
  rd := c.rd
  imm := c.imm
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_imm := ia.h_input_imm
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_addiw_subset := ia.h_addiw_subset
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_sllw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sllw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sllw trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sllw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sllw trace i) : Type where
  sllw_input : PureSpec.SllwInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok sllw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok sllw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some sllw_input.PC
  h_input_rd : sllw_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC
  h_rd_idx :
    sllw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_sllw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sllw trace i) (dec : Decode_sllw trace binding i c)
    (ia : Inputs_sllw trace binding i c) : RowData_sllw trace binding i where
  sllw_input := ia.sllw_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_srlw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_srlw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_srlw trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_srlw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_srlw trace i) : Type where
  srlw_input : PureSpec.SrlwInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok srlw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok srlw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some srlw_input.PC
  h_input_rd : srlw_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC
  h_rd_idx :
    srlw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_srlw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_srlw trace i) (dec : Decode_srlw trace binding i c)
    (ia : Inputs_srlw trace binding i c) : RowData_srlw trace binding i where
  srlw_input := ia.srlw_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_sraw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sraw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sraw trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sraw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sraw trace i) : Type where
  sraw_input : PureSpec.SrawInput
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok sraw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok sraw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some sraw_input.PC
  h_input_rd : sraw_input.rd = regidx_to_fin c.rd
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC
  h_rd_idx :
    sraw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_sraw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sraw trace i) (dec : Decode_sraw trace binding i c)
    (ia : Inputs_sraw trace binding i c) : RowData_sraw trace binding i where
  sraw_input := ia.sraw_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  h_b_hi_t := ia.h_b_hi_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_slliw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  slliw_input : PureSpec.SlliwInput
  r1 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_slliw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_slliw trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SLL_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_slliw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_slliw trace i) : Type where
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok c.slliw_input.r1_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some c.slliw_input.PC
  h_input_rd : c.slliw_input.rd = regidx_to_fin c.rd
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
      shamt_w_b_lo c.slliw_input.shamt
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIWOP_slliw_pure c.slliw_input).nextPC
  h_rd_idx :
    c.slliw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_slliw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_slliw trace i) (dec : Decode_slliw trace binding i c)
    (ia : Inputs_slliw trace binding i c) : RowData_slliw trace binding i where
  slliw_input := c.slliw_input
  r1 := c.r1
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_srliw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  srliw_input : PureSpec.SrliwInput
  r1 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_srliw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_srliw trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRL_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_srliw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_srliw trace i) : Type where
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok c.srliw_input.r1_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some c.srliw_input.PC
  h_input_rd : c.srliw_input.rd = regidx_to_fin c.rd
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
      shamt_w_b_lo c.srliw_input.shamt
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIWOP_srliw_pure c.srliw_input).nextPC
  h_rd_idx :
    c.srliw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_srliw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_srliw trace i) (dec : Decode_srliw trace binding i c)
    (ia : Inputs_srliw trace binding i c) : RowData_srliw trace binding i where
  srliw_input := c.srliw_input
  r1 := c.r1
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_sraiw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  sraiw_input : PureSpec.SraiwInput
  r1 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sraiw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sraiw trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_SRA_W
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sraiw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sraiw trace i) : Type where
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok c.sraiw_input.r1_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some c.sraiw_input.PC
  h_input_rd : c.sraiw_input.rd = regidx_to_fin c.rd
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
      shamt_w_b_lo c.sraiw_input.shamt
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_SHIFTIWOP_sraiw_pure c.sraiw_input).nextPC
  h_rd_idx :
    c.sraiw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr

def toRowData_sraiw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sraiw trace i) (dec : Decode_sraiw trace binding i c)
    (ia : Inputs_sraiw trace binding i c) : RowData_sraiw trace binding i where
  sraiw_input := c.sraiw_input
  r1 := c.r1
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_store_pc := dec.h_store_pc
  h_input_r1 := ia.h_input_r1
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  h_a_lo_t := ia.h_a_lo_t
  h_a_hi_t := ia.h_a_hi_t
  h_b_lo_t := ia.h_b_lo_t
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_mul (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  srs1 : Signedness
  srs2 : Signedness
  bus : ZiskFv.Compliance.BusRows

structure Decode_mul (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2
  bounds : ZiskFv.Compliance.ByteBounds c.bus.e2

structure Inputs_mul (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_mul trace i) : Type where
  mul_input : PureSpec.MulInput
  v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL
  r_a : ℕ
  h_match_primary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding i) mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
      (PureSpec.execute_MULH_mul_pure mul_input).nextPC
      c.r1 c.r2 c.rd c.bus.exec_row c.bus.e0 c.bus.e1 c.bus.e2
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

def toRowData_mul {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_mul trace i) (dec : Decode_mul trace binding i c)
    (ia : Inputs_mul trace binding i c) : RowData_mul trace binding i where
  mul_input := ia.mul_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  srs1 := c.srs1
  srs2 := c.srs2
  bus := c.bus
  v := ia.v
  r_a := ia.r_a
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  h_match_primary := ia.h_match_primary
  promises := ia.promises
  arith_mem := dec.arith_mem
  bounds := dec.bounds
  h_row_constraints := ia.h_row_constraints
  arith_table := ia.arith_table
  arith_chunk_ranges := ia.arith_chunk_ranges
  arith_carry_ranges := ia.arith_carry_ranges
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value
  h_not_forge := ia.h_not_forge

structure Claim_mulh (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows

structure Decode_mulh (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2
  bounds : ZiskFv.Compliance.ByteBounds c.bus.e2

structure Inputs_mulh (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_mulh trace i) : Type where
  mulh_input : PureSpec.MulhInput
  v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL
  r_a : ℕ
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding i) mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
      (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
      c.r1 c.r2 c.rd c.bus.exec_row c.bus.e0 c.bus.e1 c.bus.e2
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

def toRowData_mulh {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_mulh trace i) (dec : Decode_mulh trace binding i c)
    (ia : Inputs_mulh trace binding i c) : RowData_mulh trace binding i where
  mulh_input := ia.mulh_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  bus := c.bus
  v := ia.v
  r_a := ia.r_a
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  h_match_secondary := ia.h_match_secondary
  promises := ia.promises
  arith_mem := dec.arith_mem
  bounds := dec.bounds
  h_row_constraints := ia.h_row_constraints
  arith_table := ia.arith_table
  arith_chunk_ranges := ia.arith_chunk_ranges
  arith_carry_ranges := ia.arith_carry_ranges
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value
  h_not_forge := ia.h_not_forge
  h_sign_a := ia.h_sign_a
  h_sign_b := ia.h_sign_b

structure Claim_mulhsu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows

structure Decode_mulhsu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2
  bounds : ZiskFv.Compliance.ByteBounds c.bus.e2

structure Inputs_mulhsu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_mulhsu trace i) : Type where
  mulhsu_input : PureSpec.MulhsuInput
  v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL
  r_a : ℕ
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding i) mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
      (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
      c.r1 c.r2 c.rd c.bus.exec_row c.bus.e0 c.bus.e1 c.bus.e2
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

def toRowData_mulhsu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_mulhsu trace i) (dec : Decode_mulhsu trace binding i c)
    (ia : Inputs_mulhsu trace binding i c) : RowData_mulhsu trace binding i where
  mulhsu_input := ia.mulhsu_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  bus := c.bus
  v := ia.v
  r_a := ia.r_a
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  h_match_secondary := ia.h_match_secondary
  promises := ia.promises
  arith_mem := dec.arith_mem
  bounds := dec.bounds
  h_row_constraints := ia.h_row_constraints
  arith_table := ia.arith_table
  arith_chunk_ranges := ia.arith_chunk_ranges
  arith_carry_ranges := ia.arith_carry_ranges
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value
  h_not_forge := ia.h_not_forge
  h_sign_a := ia.h_sign_a

structure Claim_div (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows

structure Decode_div (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_DIV
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2
  bounds : ZiskFv.Compliance.ByteBounds c.bus.e2

structure Inputs_div (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_div trace i) : Type where
  div_input : PureSpec.DivInput
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_match_primary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding i) div_input.r1_val div_input.r2_val div_input.rd div_input.PC
      (PureSpec.execute_DIVREM_div_pure div_input).nextPC
      c.r1 c.r2 c.rd c.bus.exec_row c.bus.e0 c.bus.e1 c.bus.e2
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

def toRowData_div {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_div trace i) (dec : Decode_div trace binding i c)
    (ia : Inputs_div trace binding i c) : RowData_div trace binding i where
  div_input := ia.div_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  bus := c.bus
  v := ia.v
  r_a := ia.r_a
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  pins := dec.pins
  h_match_primary := ia.h_match_primary
  promises := ia.promises
  arith_mem := dec.arith_mem
  bounds := dec.bounds
  h_row_constraints := ia.h_row_constraints
  h_boundary := ia.h_boundary
  arith_table := ia.arith_table
  arith_chunk_ranges := ia.arith_chunk_ranges
  arith_carry_ranges := ia.arith_carry_ranges
  h_na_bool := ia.h_na_bool
  h_nb_bool := ia.h_nb_bool
  h_nr_bool := ia.h_nr_bool
  h_np_xor := ia.h_np_xor
  h_nr_pin := ia.h_nr_pin
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value
  h_r_le := ia.h_r_le
  h_r_sign := ia.h_r_sign
  h_not_forge := ia.h_not_forge

structure Claim_rem (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows

structure Decode_rem (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_REM
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2
  bounds : ZiskFv.Compliance.ByteBounds c.bus.e2

structure Inputs_rem (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_rem trace i) : Type where
  rem_input : PureSpec.RemInput
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding i) rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
      (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
      c.r1 c.r2 c.rd c.bus.exec_row c.bus.e0 c.bus.e1 c.bus.e2
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

def toRowData_rem {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_rem trace i) (dec : Decode_rem trace binding i c)
    (ia : Inputs_rem trace binding i c) : RowData_rem trace binding i where
  rem_input := ia.rem_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  bus := c.bus
  v := ia.v
  r_a := ia.r_a
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  pins := dec.pins
  h_match_secondary := ia.h_match_secondary
  promises := ia.promises
  arith_mem := dec.arith_mem
  bounds := dec.bounds
  h_row_constraints := ia.h_row_constraints
  arith_table := ia.arith_table
  arith_chunk_ranges := ia.arith_chunk_ranges
  arith_carry_ranges := ia.arith_carry_ranges
  h_na_bool := ia.h_na_bool
  h_nb_bool := ia.h_nb_bool
  h_nr_bool := ia.h_nr_bool
  h_np_xor := ia.h_np_xor
  h_nr_pin := ia.h_nr_pin
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value
  h_r_le := ia.h_r_le
  h_r_sign := ia.h_r_sign
  h_not_forge := ia.h_not_forge

structure Claim_divw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows

structure Decode_divw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_DIV_W
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2
  bounds : ZiskFv.Compliance.ByteBounds c.bus.e2

structure Inputs_divw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_divw trace i) : Type where
  divw_input : PureSpec.DivwInput
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_match_primary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding i) divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
      (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
      c.r1 c.r2 c.rd c.bus.exec_row c.bus.e0 c.bus.e1 c.bus.e2
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
    (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 0).val
        + (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 1).val * 256
        + (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 2).val * 65536
        + (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 3).val * 16777216
      = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536
  h_sext_choice :
    (((ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 4).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 5).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 6).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 7).val = 0)
      ∧ (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648)
    ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 4).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 5).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 6).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 7).val = 255)
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

def toRowData_divw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_divw trace i) (dec : Decode_divw trace binding i c)
    (ia : Inputs_divw trace binding i c) : RowData_divw trace binding i where
  divw_input := ia.divw_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  bus := c.bus
  v := ia.v
  r_a := ia.r_a
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  pins := dec.pins
  h_match_primary := ia.h_match_primary
  promises := ia.promises
  arith_mem := dec.arith_mem
  bounds := dec.bounds
  h_row_constraints := ia.h_row_constraints
  h_boundary := ia.h_boundary
  arith_table := ia.arith_table
  arith_chunk_ranges := ia.arith_chunk_ranges
  arith_carry_ranges := ia.arith_carry_ranges
  h_na_bool := ia.h_na_bool
  h_nb_bool := ia.h_nb_bool
  h_nr_bool := ia.h_nr_bool
  h_np_xor := ia.h_np_xor
  h_nr_pin := ia.h_nr_pin
  h_m32_v := ia.h_m32_v
  h_div_v := ia.h_div_v
  h_a23 := ia.h_a23
  h_b23 := ia.h_b23
  h_d23 := ia.h_d23
  h_c23 := ia.h_c23
  h_byte_lo := ia.h_byte_lo
  h_sext_choice := ia.h_sext_choice
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value
  h_r_le := ia.h_r_le
  h_r_sign := ia.h_r_sign
  h_not_forge := ia.h_not_forge

structure Claim_remw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  bus : ZiskFv.Compliance.BusRows

structure Decode_remw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  pins : ZiskFv.Compliance.MainRowPins
    (mainOfTable trace.program trace.mainTable) i.val 1 ZiskFv.Trusted.OP_REM_W
  arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (mainOfTable trace.program trace.mainTable) i.val c.bus.e2
  bounds : ZiskFv.Compliance.ByteBounds c.bus.e2

structure Inputs_remw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_remw trace i) : Type where
  remw_input : PureSpec.RemwInput
  v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL
  r_a : ℕ
  h_match_secondary :
    ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a)
  promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding i) remw_input.r1_val remw_input.r2_val remw_input.rd remw_input.PC
      (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC
      c.r1 c.r2 c.rd c.bus.exec_row c.bus.e0 c.bus.e1 c.bus.e2
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
    (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 0).val
        + (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 1).val * 256
        + (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 2).val * 65536
        + (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 3).val * 16777216
      = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536
  h_sext_choice :
    (((ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 4).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 5).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 6).val = 0
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 7).val = 0)
      ∧ (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648)
    ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 4).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 5).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 6).val = 255
        ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt c.bus.e2 7).val = 255)
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

def toRowData_remw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_remw trace i) (dec : Decode_remw trace binding i c)
    (ia : Inputs_remw trace binding i c) : RowData_remw trace binding i where
  remw_input := ia.remw_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  bus := c.bus
  v := ia.v
  r_a := ia.r_a
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  pins := dec.pins
  h_match_secondary := ia.h_match_secondary
  promises := ia.promises
  arith_mem := dec.arith_mem
  bounds := dec.bounds
  h_row_constraints := ia.h_row_constraints
  arith_table := ia.arith_table
  arith_chunk_ranges := ia.arith_chunk_ranges
  arith_carry_ranges := ia.arith_carry_ranges
  h_na_bool := ia.h_na_bool
  h_nb_bool := ia.h_nb_bool
  h_nr_bool := ia.h_nr_bool
  h_np_xor := ia.h_np_xor
  h_nr_pin := ia.h_nr_pin
  h_m32_v := ia.h_m32_v
  h_div_v := ia.h_div_v
  h_a23 := ia.h_a23
  h_b23 := ia.h_b23
  h_d23 := ia.h_d23
  h_c23 := ia.h_c23
  h_byte_lo := ia.h_byte_lo
  h_sext_choice := ia.h_sext_choice
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value
  h_r_le := ia.h_r_le
  h_r_sign := ia.h_r_sign
  h_not_forge := ia.h_not_forge

structure Claim_mulw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_mulw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_mulw trace i) : Type where
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_mulw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_mulw trace i) : Type where
  mulw_input : PureSpec.MulwInput
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok mulw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok mulw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some mulw_input.PC
  h_input_rd : mulw_input.rd = regidx_to_fin c.rd
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_MULW_pure mulw_input).nextPC
  h_rd_idx :
    mulw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr
  h_a23 :
    ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).a_2 0).val = 0
      ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).a_3 0).val = 0
  h_b23 :
    ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).b_2 0).val = 0
      ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).b_3 0).val = 0
  h_sext_choice :
    ((((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 4).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 5).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 6).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 7).val = 0)
        ∧ ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).c_0 0).val
            + ((vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)).c_1 0).val * 65536
              < 2147483648)
      ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 4).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 5).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 6).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 7).val = 255)
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

def toRowData_mulw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_mulw trace i) (dec : Decode_mulw trace binding i c)
    (ia : Inputs_mulw trace binding i c) : RowData_mulw trace binding i where
  mulw_input := ia.mulw_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := ia.h_main_op
  h_main_active := ia.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx
  h_a23 := ia.h_a23
  h_b23 := ia.h_b23
  h_sext_choice := ia.h_sext_choice
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value

structure Claim_mulhu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_mulhu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_mulhu trace i) : Type where
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i c.execRow).e2

structure Inputs_mulhu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_mulhu trace i) : Type where
  mulhu_input : PureSpec.MulhuInput
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok mulhu_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok mulhu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some mulhu_input.PC
  h_input_rd : mulhu_input.rd = regidx_to_fin c.rd
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
  h_rd_idx :
    mulhu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr
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

def toRowData_mulhu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_mulhu trace i) (dec : Decode_mulhu trace binding i c)
    (ia : Inputs_mulhu trace binding i c) : RowData_mulhu trace binding i where
  mulhu_input := ia.mulhu_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := ia.h_main_op
  h_main_active := ia.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx
  bounds := dec.bounds
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value

structure Claim_divu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_divu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_divu trace i) : Type where
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i c.execRow).e2

structure Inputs_divu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_divu trace i) : Type where
  divu_input : PureSpec.DivuInput
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok divu_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok divu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some divu_input.PC
  h_input_rd : divu_input.rd = regidx_to_fin c.rd
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
  h_rd_idx :
    divu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr
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

def toRowData_divu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_divu trace i) (dec : Decode_divu trace binding i c)
    (ia : Inputs_divu trace binding i c) : RowData_divu trace binding i where
  divu_input := ia.divu_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := ia.h_main_op
  h_main_active := ia.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx
  bounds := dec.bounds
  remainder_bound := ia.remainder_bound
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value

structure Claim_divuw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_divuw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_divuw trace i) : Type where
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i c.execRow).e2

structure Inputs_divuw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_divuw trace i) : Type where
  divuw_input : PureSpec.DivuwInput
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok divuw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok divuw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some divuw_input.PC
  h_input_rd : divuw_input.rd = regidx_to_fin c.rd
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
  h_rd_idx :
    divuw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr
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
    ((((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 4).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 5).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 6).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 7).val = 0)
        ∧ ((divuwArow trace binding i h_main_active h_main_op).chunks.a_0).val
            + ((divuwArow trace binding i h_main_active h_main_op).chunks.a_1).val * 65536
              < 2147483648)
      ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 4).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 5).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 6).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 7).val = 255)
        ∧ ((divuwArow trace binding i h_main_active h_main_op).chunks.a_0).val
            + ((divuwArow trace binding i h_main_active h_main_op).chunks.a_1).val * 65536
              ≥ 2147483648))
  h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
    = ((divuwArow trace binding i h_main_active h_main_op).chunks.c_0).val
        + ((divuwArow trace binding i h_main_active h_main_op).chunks.c_1).val * 65536
  h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
    = ((divuwArow trace binding i h_main_active h_main_op).chunks.b_0).val
        + ((divuwArow trace binding i h_main_active h_main_op).chunks.b_1).val * 65536

def toRowData_divuw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_divuw trace i) (dec : Decode_divuw trace binding i c)
    (ia : Inputs_divuw trace binding i c) : RowData_divuw trace binding i where
  divuw_input := ia.divuw_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := ia.h_main_op
  h_main_active := ia.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx
  bounds := dec.bounds
  remainder_bound := ia.remainder_bound
  h_b23 := ia.h_b23
  h_c23 := ia.h_c23
  h_sext_choice := ia.h_sext_choice
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value

structure Claim_remu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_remu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_remu trace i) : Type where
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i c.execRow).e2

structure Inputs_remu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_remu trace i) : Type where
  remu_input : PureSpec.RemuInput
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok remu_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok remu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some remu_input.PC
  h_input_rd : remu_input.rd = regidx_to_fin c.rd
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
  h_rd_idx :
    remu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr
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

def toRowData_remu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_remu trace i) (dec : Decode_remu trace binding i c)
    (ia : Inputs_remu trace binding i c) : RowData_remu trace binding i where
  remu_input := ia.remu_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := ia.h_main_op
  h_main_active := ia.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx
  bounds := dec.bounds
  remainder_bound := ia.remainder_bound
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value

structure Claim_remuw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_remuw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_remuw trace i) : Type where
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
  h_exec_len : (busSub trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSub trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSub trace binding i c.execRow).exec_row[1]!.multiplicity = 1
  bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i c.execRow).e2

structure Inputs_remuw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_remuw trace i) : Type where
  remuw_input : PureSpec.RemuwInput
  h_main_op :
    (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W
  h_main_active :
    (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
  h_input_r1 :
    read_xreg (regidx_to_fin c.r1) (binding i)
      = EStateM.Result.ok remuw_input.r1_val (binding i)
  h_input_r2 :
    read_xreg (regidx_to_fin c.r2) (binding i)
      = EStateM.Result.ok remuw_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some remuw_input.PC
  h_input_rd : remuw_input.rd = regidx_to_fin c.rd
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSub trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
  h_rd_idx :
    remuw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace binding i c.execRow).e2.ptr
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
    ((((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 4).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 5).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 6).val = 0
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 7).val = 0)
        ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.d_0).val
            + ((remuwArow trace binding i h_main_active h_main_op).chunks.d_1).val * 65536
              < 2147483648)
      ∨ (((ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 4).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 5).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 6).val = 255
          ∧ (ZiskFv.Channels.MemoryBusBytes.byteAt (busSub trace binding i c.execRow).e2 7).val = 255)
        ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.d_0).val
            + ((remuwArow trace binding i h_main_active h_main_op).chunks.d_1).val * 65536
              ≥ 2147483648))
  h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
    = ((remuwArow trace binding i h_main_active h_main_op).chunks.c_0).val
        + ((remuwArow trace binding i h_main_active h_main_op).chunks.c_1).val * 65536
  h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
    = ((remuwArow trace binding i h_main_active h_main_op).chunks.b_0).val
        + ((remuwArow trace binding i h_main_active h_main_op).chunks.b_1).val * 65536

def toRowData_remuw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_remuw trace i) (dec : Decode_remuw trace binding i c)
    (ia : Inputs_remuw trace binding i c) : RowData_remuw trace binding i where
  remuw_input := ia.remuw_input
  r1 := c.r1
  r2 := c.r2
  rd := c.rd
  h_main_op := ia.h_main_op
  h_main_active := ia.h_main_active
  h_store_pc := dec.h_store_pc
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_jmp_offset2 := dec.h_jmp_offset2
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_rd := ia.h_input_rd
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx
  bounds := dec.bounds
  remainder_bound := ia.remainder_bound
  h_b23 := ia.h_b23
  h_c23 := ia.h_c23
  h_sext_choice := ia.h_sext_choice
  h_rs1_value := ia.h_rs1_value
  h_rs2_value := ia.h_rs2_value

structure Claim_beq (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  exec_row : List (Interaction.ExecutionBusEntry FGL)

structure Decode_beq (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_beq trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_EQ
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_exec_len : c.exec_row.length = 2
  h_e0_mult : c.exec_row[0]!.multiplicity = -1
  h_e1_mult : c.exec_row[1]!.multiplicity = 1

structure Inputs_beq (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_beq trace i) : Type where
  beq_input : PureSpec.BeqInput
  misa_val : RegisterType Register.misa
  h_input_imm : beq_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok beq_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok beq_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some beq_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.exec_row[1]!.pc).val))
      = (PureSpec.execute_BEQ_pure beq_input).nextPC
  h_not_throws : (PureSpec.execute_BEQ_pure beq_input).throws = false
  h_success : (PureSpec.execute_BEQ_pure beq_input).success = true

def toRowData_beq {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_beq trace i) (dec : Decode_beq trace binding i c)
    (ia : Inputs_beq trace binding i c) : RowData_beq trace binding i where
  beq_input := ia.beq_input
  imm := c.imm
  r1 := c.r1
  r2 := c.r2
  misa_val := ia.misa_val
  exec_row := c.exec_row
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_store_pc := dec.h_store_pc
  h_jmp_offset2 := dec.h_jmp_offset2
  h_input_imm := ia.h_input_imm
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_misa := ia.h_input_misa
  h_misa_c := ia.h_misa_c
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_not_throws := ia.h_not_throws
  h_success := ia.h_success

structure Claim_bne (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  exec_row : List (Interaction.ExecutionBusEntry FGL)

structure Decode_bne (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_bne trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_EQ
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_exec_len : c.exec_row.length = 2
  h_e0_mult : c.exec_row[0]!.multiplicity = -1
  h_e1_mult : c.exec_row[1]!.multiplicity = 1

structure Inputs_bne (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_bne trace i) : Type where
  bne_input : PureSpec.BneInput
  misa_val : RegisterType Register.misa
  h_input_imm : bne_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok bne_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok bne_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bne_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.exec_row[1]!.pc).val))
      = (PureSpec.execute_BNE_pure bne_input).nextPC
  h_not_throws : (PureSpec.execute_BNE_pure bne_input).throws = false
  h_success : (PureSpec.execute_BNE_pure bne_input).success = true

def toRowData_bne {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_bne trace i) (dec : Decode_bne trace binding i c)
    (ia : Inputs_bne trace binding i c) : RowData_bne trace binding i where
  bne_input := ia.bne_input
  imm := c.imm
  r1 := c.r1
  r2 := c.r2
  misa_val := ia.misa_val
  exec_row := c.exec_row
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_store_pc := dec.h_store_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_input_imm := ia.h_input_imm
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_misa := ia.h_input_misa
  h_misa_c := ia.h_misa_c
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_not_throws := ia.h_not_throws
  h_success := ia.h_success

structure Claim_blt (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  exec_row : List (Interaction.ExecutionBusEntry FGL)

structure Decode_blt (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_blt trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_exec_len : c.exec_row.length = 2
  h_e0_mult : c.exec_row[0]!.multiplicity = -1
  h_e1_mult : c.exec_row[1]!.multiplicity = 1

structure Inputs_blt (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_blt trace i) : Type where
  blt_input : PureSpec.BltInput
  misa_val : RegisterType Register.misa
  h_input_imm : blt_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok blt_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok blt_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some blt_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.exec_row[1]!.pc).val))
      = (PureSpec.execute_BLT_pure blt_input).nextPC
  h_not_throws : (PureSpec.execute_BLT_pure blt_input).throws = false
  h_success : (PureSpec.execute_BLT_pure blt_input).success = true

def toRowData_blt {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_blt trace i) (dec : Decode_blt trace binding i c)
    (ia : Inputs_blt trace binding i c) : RowData_blt trace binding i where
  blt_input := ia.blt_input
  imm := c.imm
  r1 := c.r1
  r2 := c.r2
  misa_val := ia.misa_val
  exec_row := c.exec_row
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_store_pc := dec.h_store_pc
  h_jmp_offset2 := dec.h_jmp_offset2
  h_input_imm := ia.h_input_imm
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_misa := ia.h_input_misa
  h_misa_c := ia.h_misa_c
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_not_throws := ia.h_not_throws
  h_success := ia.h_success

structure Claim_bge (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  exec_row : List (Interaction.ExecutionBusEntry FGL)

structure Decode_bge (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_bge trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LT
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_exec_len : c.exec_row.length = 2
  h_e0_mult : c.exec_row[0]!.multiplicity = -1
  h_e1_mult : c.exec_row[1]!.multiplicity = 1

structure Inputs_bge (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_bge trace i) : Type where
  bge_input : PureSpec.BgeInput
  misa_val : RegisterType Register.misa
  h_input_imm : bge_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok bge_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok bge_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bge_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.exec_row[1]!.pc).val))
      = (PureSpec.execute_BGE_pure bge_input).nextPC
  h_not_throws : (PureSpec.execute_BGE_pure bge_input).throws = false
  h_success : (PureSpec.execute_BGE_pure bge_input).success = true

def toRowData_bge {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_bge trace i) (dec : Decode_bge trace binding i c)
    (ia : Inputs_bge trace binding i c) : RowData_bge trace binding i where
  bge_input := ia.bge_input
  imm := c.imm
  r1 := c.r1
  r2 := c.r2
  misa_val := ia.misa_val
  exec_row := c.exec_row
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_store_pc := dec.h_store_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_input_imm := ia.h_input_imm
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_misa := ia.h_input_misa
  h_misa_c := ia.h_misa_c
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_not_throws := ia.h_not_throws
  h_success := ia.h_success

structure Claim_bltu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  exec_row : List (Interaction.ExecutionBusEntry FGL)

structure Decode_bltu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_bltu trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_exec_len : c.exec_row.length = 2
  h_e0_mult : c.exec_row[0]!.multiplicity = -1
  h_e1_mult : c.exec_row[1]!.multiplicity = 1

structure Inputs_bltu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_bltu trace i) : Type where
  bltu_input : PureSpec.BltuInput
  misa_val : RegisterType Register.misa
  h_input_imm : bltu_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok bltu_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok bltu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bltu_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.exec_row[1]!.pc).val))
      = (PureSpec.execute_BLTU_pure bltu_input).nextPC
  h_not_throws : (PureSpec.execute_BLTU_pure bltu_input).throws = false
  h_success : (PureSpec.execute_BLTU_pure bltu_input).success = true

def toRowData_bltu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_bltu trace i) (dec : Decode_bltu trace binding i c)
    (ia : Inputs_bltu trace binding i c) : RowData_bltu trace binding i where
  bltu_input := ia.bltu_input
  imm := c.imm
  r1 := c.r1
  r2 := c.r2
  misa_val := ia.misa_val
  exec_row := c.exec_row
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_store_pc := dec.h_store_pc
  h_jmp_offset2 := dec.h_jmp_offset2
  h_input_imm := ia.h_input_imm
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_misa := ia.h_input_misa
  h_misa_c := ia.h_misa_c
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_not_throws := ia.h_not_throws
  h_success := ia.h_success

structure Claim_bgeu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  exec_row : List (Interaction.ExecutionBusEntry FGL)

structure Decode_bgeu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_bgeu trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_LTU
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 0
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 0
  h_jmp_offset1 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
      i.val = 4
  h_exec_len : c.exec_row.length = 2
  h_e0_mult : c.exec_row[0]!.multiplicity = -1
  h_e1_mult : c.exec_row[1]!.multiplicity = 1

structure Inputs_bgeu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_bgeu trace i) : Type where
  bgeu_input : PureSpec.BgeuInput
  misa_val : RegisterType Register.misa
  h_input_imm : bgeu_input.imm = c.imm
  h_input_r1 : read_xreg (regidx_to_fin c.r1) (binding i)
    = EStateM.Result.ok bgeu_input.r1_val (binding i)
  h_input_r2 : read_xreg (regidx_to_fin c.r2) (binding i)
    = EStateM.Result.ok bgeu_input.r2_val (binding i)
  h_input_pc : (binding i).regs.get? Register.PC = .some bgeu_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.exec_row[1]!.pc).val))
      = (PureSpec.execute_BGEU_pure bgeu_input).nextPC
  h_not_throws : (PureSpec.execute_BGEU_pure bgeu_input).throws = false
  h_success : (PureSpec.execute_BGEU_pure bgeu_input).success = true

def toRowData_bgeu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_bgeu trace i) (dec : Decode_bgeu trace binding i c)
    (ia : Inputs_bgeu trace binding i c) : RowData_bgeu trace binding i where
  bgeu_input := ia.bgeu_input
  imm := c.imm
  r1 := c.r1
  r2 := c.r2
  misa_val := ia.misa_val
  exec_row := c.exec_row
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_store_pc := dec.h_store_pc
  h_jmp_offset1 := dec.h_jmp_offset1
  h_input_imm := ia.h_input_imm
  h_input_r1 := ia.h_input_r1
  h_input_r2 := ia.h_input_r2
  h_input_pc := ia.h_input_pc
  h_input_misa := ia.h_input_misa
  h_misa_c := ia.h_misa_c
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_not_throws := ia.h_not_throws
  h_success := ia.h_success

structure Claim_lui (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  imm : BitVec 20
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_lui (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_imm_lo_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val).val
      = (c.imm ++ (0 : BitVec 12)).toNat
  h_imm_hi_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val).val
      = (BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toNat / 4294967296
  h_exec_len : c.execRow.length = 2
  h_e0_mult : c.execRow[0]!.multiplicity = -1
  h_e1_mult : c.execRow[1]!.multiplicity = 1

structure Inputs_lui (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_lui trace i) : Type where
  lui_input : PureSpec.LuiInput
  h_input_imm : lui_input.imm = c.imm
  h_input_rd : lui_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some lui_input.PC
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.execRow[1]!.pc).val))
      = (PureSpec.execute_LUI_pure lui_input).nextPC
  h_rd_idx :
    lui_input.rd =
      Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr

def toRowData_lui {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_lui trace i) (dec : Decode_lui trace binding i c)
    (ia : Inputs_lui trace binding i c) : RowData_lui trace binding i where
  lui_input := ia.lui_input
  imm := c.imm
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_store_pc := dec.h_store_pc
  h_input_imm := ia.h_input_imm
  h_input_rd := ia.h_input_rd
  h_input_pc := ia.h_input_pc
  h_imm_lo_nat := dec.h_imm_lo_nat
  h_imm_hi_nat := dec.h_imm_hi_nat
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx

structure Claim_auipc (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  imm : BitVec 20
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_auipc (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : c.execRow.length = 2
  h_e0_mult : c.execRow[0]!.multiplicity = -1
  h_e1_mult : c.execRow[1]!.multiplicity = 1

structure Inputs_auipc (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.execRow[1]!.pc).val))
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

def toRowData_auipc {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_auipc trace i) (dec : Decode_auipc trace binding i c)
    (ia : Inputs_auipc trace binding i c) : RowData_auipc trace binding i where
  auipc_input := ia.auipc_input
  imm := c.imm
  rd := c.rd
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_store_pc := dec.h_store_pc
  h_input_imm := ia.h_input_imm
  h_input_rd := ia.h_input_rd
  h_input_pc := ia.h_input_pc
  h_offset_bridge := ia.h_offset_bridge
  h_pc_bridge := ia.h_pc_bridge
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_rd_idx := ia.h_rd_idx
  h_no_wrap := ia.h_no_wrap
  h_pc_offset_lt_2_32 := ia.h_pc_offset_lt_2_32

structure Claim_jal (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  imm : BitVec 21
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_jal (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_jal trace i) : Type where
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
  h_jmp2 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
      i.val = 4
  h_exec_len : c.execRow.length = 2
  h_e0_mult : c.execRow[0]!.multiplicity = -1
  h_e1_mult : c.execRow[1]!.multiplicity = 1

structure Inputs_jal (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_jal trace i) : Type where
  jal_input : PureSpec.JalInput
  misa_val : RegisterType Register.misa
  nextPC_val : BitVec 64
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = jal_input.PC.toNat
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.execRow[1]!.pc).val))
      = nextPC_val
  h_input_rd : jal_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some jal_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_success : (PureSpec.execute_JAL_pure jal_input).success = true
  h_nextPC_option : (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val
  h_rd_idx : jal_input.rd = Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr
  h_input_imm : jal_input.imm = c.imm
  h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false
  h_pc_bound : jal_input.PC.toNat < GL_prime - 4
  h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296

def toRowData_jal {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_jal trace i) (dec : Decode_jal trace binding i c)
    (ia : Inputs_jal trace binding i c) : RowData_jal trace binding i where
  jal_input := ia.jal_input
  imm := c.imm
  rd := c.rd
  misa_val := ia.misa_val
  nextPC_val := ia.nextPC_val
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_store_pc := dec.h_store_pc
  h_jmp2 := dec.h_jmp2
  h_pc_bridge := ia.h_pc_bridge
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_input_rd := ia.h_input_rd
  h_input_pc := ia.h_input_pc
  h_input_misa := ia.h_input_misa
  h_misa_c := ia.h_misa_c
  h_success := ia.h_success
  h_nextPC_option := ia.h_nextPC_option
  h_rd_idx := ia.h_rd_idx
  h_input_imm := ia.h_input_imm
  h_not_throws := ia.h_not_throws
  h_pc_bound := ia.h_pc_bound
  h_pc_offset_lt_2_32 := ia.h_pc_offset_lt_2_32

structure Claim_jalr (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  imm : BitVec 12
  rs1 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_jalr (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_jalr trace i) : Type where
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_AND
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 1
  h_flag :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).flag
      i.val = 0
  h_m32 :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
      i.val = 0
  h_set_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
      i.val = 1
  h_store_pc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
      i.val = 1
  h_exec_len : c.execRow.length = 2
  h_e0_mult : c.execRow[0]!.multiplicity = -1
  h_e1_mult : c.execRow[1]!.multiplicity = 1

structure Inputs_jalr (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_jalr trace i) : Type where
  jalr_input : PureSpec.JalrInput
  misa_val : RegisterType Register.misa
  mseccfg : RegisterType Register.mseccfg
  nextPC_val : BitVec 64
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.execRow[1]!.pc).val))
      = nextPC_val
  h_input_rd : jalr_input.rd = regidx_to_fin c.rd
  h_input_pc : (binding i).regs.get? Register.PC = .some jalr_input.PC
  h_input_misa : (binding i).regs.get? Register.misa = .some misa_val
  h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1
  h_success : (PureSpec.execute_JALR_pure jalr_input).success = true
  h_nextPC_option : (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val
  h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr
  h_input_imm : jalr_input.imm = c.imm
  h_input_rs1 : read_xreg (regidx_to_fin c.rs1) (binding i)
    = EStateM.Result.ok jalr_input.rs1_val (binding i)
  h_cur_privilege : Sail.readReg Register.cur_privilege (binding i)
    = EStateM.Result.ok Privilege.Machine (binding i)
  h_mseccfg : Sail.readReg Register.mseccfg (binding i)
    = EStateM.Result.ok mseccfg (binding i)
  h_link_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val
      + (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
          i.val).val
      = (jalr_input.PC + 4#64).toNat
  h_pc_bound : jalr_input.PC.toNat < GL_prime - 4
  h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296

def toRowData_jalr {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_jalr trace i) (dec : Decode_jalr trace binding i c)
    (ia : Inputs_jalr trace binding i c) : RowData_jalr trace binding i where
  jalr_input := ia.jalr_input
  imm := c.imm
  rs1 := c.rs1
  rd := c.rd
  misa_val := ia.misa_val
  mseccfg := ia.mseccfg
  nextPC_val := ia.nextPC_val
  h_main_op := dec.h_main_op
  h_main_active := dec.h_main_active
  h_flag := dec.h_flag
  h_m32 := dec.h_m32
  h_set_pc := dec.h_set_pc
  h_store_pc := dec.h_store_pc
  execRow := c.execRow
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_input_rd := ia.h_input_rd
  h_input_pc := ia.h_input_pc
  h_input_misa := ia.h_input_misa
  h_misa_c := ia.h_misa_c
  h_success := ia.h_success
  h_nextPC_option := ia.h_nextPC_option
  h_rd_idx := ia.h_rd_idx
  h_input_imm := ia.h_input_imm
  h_input_rs1 := ia.h_input_rs1
  h_cur_privilege := ia.h_cur_privilege
  h_mseccfg := ia.h_mseccfg
  h_link_bridge := ia.h_link_bridge
  h_pc_bound := ia.h_pc_bound
  h_pc_offset_lt_2_32 := ia.h_pc_offset_lt_2_32

structure Claim_fence (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  fm : BitVec 4
  fenceP : BitVec 4
  fenceS : BitVec 4
  rs : regidx
  rd : regidx
  exec_row : List (Interaction.ExecutionBusEntry FGL)

structure Decode_fence (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_fence trace i) : Type where
  h_main_active :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
      i.val = 0
  h_main_op :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
      i.val = ZiskFv.Trusted.OP_FLAG
  h_exec_len : c.exec_row.length = 2
  h_e0_mult : c.exec_row[0]!.multiplicity = -1
  h_e1_mult : c.exec_row[1]!.multiplicity = 1
  h_fm_zero : c.fm = 0#4
  h_rs_x0 : ZiskFv.Compliance.Defects.IsX0Reg c.rs
  h_rd_x0 : ZiskFv.Compliance.Defects.IsX0Reg c.rd

structure Inputs_fence (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_fence trace i) : Type where
  fence_input : PureSpec.FenceInput
  h_input_pc : (binding i).regs.get? Register.PC = .some fence_input.PC
  h_input_priv :
    (binding i).regs.get? Register.cur_privilege = .some Privilege.Machine
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (c.exec_row[1]!.pc).val))
      = (PureSpec.execute_FENCE_pure fence_input).nextPC

def toRowData_fence {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_fence trace i) (dec : Decode_fence trace binding i c)
    (ia : Inputs_fence trace binding i c) : RowData_fence trace binding i where
  fence_input := ia.fence_input
  fm := c.fm
  fenceP := c.fenceP
  fenceS := c.fenceS
  rs := c.rs
  rd := c.rd
  exec_row := c.exec_row
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_input_pc := ia.h_input_pc
  h_input_priv := ia.h_input_priv
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_fm_zero := dec.h_fm_zero
  h_rs_x0 := dec.h_rs_x0
  h_rd_x0 := dec.h_rd_x0

structure Claim_sb (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  sb_input : PureSpec.SbInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sb (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busSt trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sb (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sb trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sb_state_assumptions c.sb_input (binding i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (c.sb_input.r1_val + BitVec.signExtend 64 c.sb_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo c.sb_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi c.sb_input.r2_val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STOREB_pure c.sb_input).nextPC
  h_m1 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 1]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 1 : BitVec 8)
  h_m2 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 2]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 2 : BitVec 8)
  h_m3 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 3]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 3 : BitVec 8)
  h_m4 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 4 : BitVec 8)
  h_m5 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 5 : BitVec 8)
  h_m6 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 6 : BitVec 8)
  h_m7 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 7 : BitVec 8)

def toRowData_sb {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sb trace i) (dec : Decode_sb trace binding i c)
    (ia : Inputs_sb trace binding i c) : RowData_sb trace binding i where
  sb_input := c.sb_input
  regs := ia.regs
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_main_ind_width := dec.h_main_ind_width
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr2 := ia.h_addr2
  h_b0_value := ia.h_b0_value
  h_b1_value := ia.h_b1_value
  execRow := c.execRow
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_m1 := ia.h_m1
  h_m2 := ia.h_m2
  h_m3 := ia.h_m3
  h_m4 := ia.h_m4
  h_m5 := ia.h_m5
  h_m6 := ia.h_m6
  h_m7 := ia.h_m7

structure Claim_sh (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  sh_input : PureSpec.ShInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sh (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busSt trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sh (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sh trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sh_state_assumptions c.sh_input (binding i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (c.sh_input.r1_val + BitVec.signExtend 64 c.sh_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo c.sh_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi c.sh_input.r2_val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STOREH_pure c.sh_input).nextPC
  h_m2 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 2]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 2 : BitVec 8)
  h_m3 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 3]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 3 : BitVec 8)
  h_m4 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 4 : BitVec 8)
  h_m5 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 5 : BitVec 8)
  h_m6 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 6 : BitVec 8)
  h_m7 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 7 : BitVec 8)

def toRowData_sh {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sh trace i) (dec : Decode_sh trace binding i c)
    (ia : Inputs_sh trace binding i c) : RowData_sh trace binding i where
  sh_input := c.sh_input
  regs := ia.regs
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_main_ind_width := dec.h_main_ind_width
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr2 := ia.h_addr2
  h_b0_value := ia.h_b0_value
  h_b1_value := ia.h_b1_value
  execRow := c.execRow
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_m2 := ia.h_m2
  h_m3 := ia.h_m3
  h_m4 := ia.h_m4
  h_m5 := ia.h_m5
  h_m6 := ia.h_m6
  h_m7 := ia.h_m7

structure Claim_sw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  sw_input : PureSpec.SwInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busSt trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sw trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sw_state_assumptions c.sw_input (binding i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (c.sw_input.r1_val + BitVec.signExtend 64 c.sw_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo c.sw_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi c.sw_input.r2_val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STOREW_pure c.sw_input).nextPC
  h_m4 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 4]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 4 : BitVec 8)
  h_m5 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 5]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 5 : BitVec 8)
  h_m6 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 6]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 6 : BitVec 8)
  h_m7 : (binding i).mem[(busSt trace binding i c.execRow).e2.ptr.toNat + 7]?
    = some (ZiskFv.Channels.MemoryBusBytes.byteAt (busSt trace binding i c.execRow).e2 7 : BitVec 8)

def toRowData_sw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sw trace i) (dec : Decode_sw trace binding i c)
    (ia : Inputs_sw trace binding i c) : RowData_sw trace binding i where
  sw_input := c.sw_input
  regs := ia.regs
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_main_ind_width := dec.h_main_ind_width
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr2 := ia.h_addr2
  h_b0_value := ia.h_b0_value
  h_b1_value := ia.h_b1_value
  execRow := c.execRow
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_m4 := ia.h_m4
  h_m5 := ia.h_m5
  h_m6 := ia.h_m6
  h_m7 := ia.h_m7

structure Claim_sd (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  sd_input : PureSpec.SdInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_sd (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busSt trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busSt trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busSt trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_sd (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_sd trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  h_opcode_assumptions : PureSpec.sd_state_assumptions c.sd_input (binding i)
  h_addr2 :
    (mainRowWithRomSt trace binding i).rom.addr2.toNat =
      (c.sd_input.r1_val + BitVec.signExtend 64 c.sd_input.imm).toNat
  h_b0_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
      ZiskFv.Trusted.lane_lo c.sd_input.r2_val
  h_b1_value :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
      ZiskFv.Trusted.lane_hi c.sd_input.r2_val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busSt trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_STORED_pure c.sd_input).nextPC

def toRowData_sd {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_sd trace i) (dec : Decode_sd trace binding i c)
    (ia : Inputs_sd trace binding i c) : RowData_sd trace binding i where
  sd_input := c.sd_input
  regs := ia.regs
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr2 := ia.h_addr2
  h_b0_value := ia.h_b0_value
  h_b1_value := ia.h_b1_value
  execRow := c.execRow
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches

structure Claim_ld (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  ld_input : PureSpec.LdInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_ld (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busLd trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_ld (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_ld trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.ld_state_assumptions c.ld_input (binding i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      c.ld_input.r1_val.toNat + (BitVec.signExtend 64 c.ld_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      c.ld_input.rd = 0
  h_addr2_idx :
    c.ld_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADD_pure c.ld_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace binding i c.execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

def toRowData_ld {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_ld trace i) (dec : Decode_ld trace binding i c)
    (ia : Inputs_ld trace binding i c) : RowData_ld trace binding i where
  ld_input := c.ld_input
  regs := ia.regs
  mem := ia.mem
  r_mem := ia.r_mem
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_width := dec.h_width
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr1 := ia.h_addr1
  h_addr2_zero_iff := ia.h_addr2_zero_iff
  h_addr2_idx := ia.h_addr2_idx
  execRow := c.execRow
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_memory_timeline := ia.h_memory_timeline
  h_msg := ia.h_msg
  h_mem_sel := ia.h_mem_sel
  h_mem_wr := ia.h_mem_wr

structure Claim_lbu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  lbu_input : PureSpec.LbuInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_lbu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busLd trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_lbu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_lbu trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace binding i c.execRow).e1
  h_opcode_assumptions : PureSpec.lbu_state_assumptions c.lbu_input (binding i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      c.lbu_input.r1_val.toNat + (BitVec.signExtend 64 c.lbu_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      c.lbu_input.rd = 0
  h_addr2_idx :
    c.lbu_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADBU_pure c.lbu_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace binding i c.execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

def toRowData_lbu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_lbu trace i) (dec : Decode_lbu trace binding i c)
    (ia : Inputs_lbu trace binding i c) : RowData_lbu trace binding i where
  lbu_input := c.lbu_input
  regs := ia.regs
  mem := ia.mem
  r_mem := ia.r_mem
  execRow := c.execRow
  align := ia.align
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_width := dec.h_width
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr1 := ia.h_addr1
  h_addr2_zero_iff := ia.h_addr2_zero_iff
  h_addr2_idx := ia.h_addr2_idx
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_memory_timeline := ia.h_memory_timeline
  h_msg := ia.h_msg
  h_mem_sel := ia.h_mem_sel
  h_mem_wr := ia.h_mem_wr

structure Claim_lhu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  lhu_input : PureSpec.LhuInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_lhu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busLd trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_lhu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_lhu trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace binding i c.execRow).e1
  h_opcode_assumptions : PureSpec.lhu_state_assumptions c.lhu_input (binding i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      c.lhu_input.r1_val.toNat + (BitVec.signExtend 64 c.lhu_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      c.lhu_input.rd = 0
  h_addr2_idx :
    c.lhu_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADHU_pure c.lhu_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace binding i c.execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

def toRowData_lhu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_lhu trace i) (dec : Decode_lhu trace binding i c)
    (ia : Inputs_lhu trace binding i c) : RowData_lhu trace binding i where
  lhu_input := c.lhu_input
  regs := ia.regs
  mem := ia.mem
  r_mem := ia.r_mem
  execRow := c.execRow
  align := ia.align
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_width := dec.h_width
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr1 := ia.h_addr1
  h_addr2_zero_iff := ia.h_addr2_zero_iff
  h_addr2_idx := ia.h_addr2_idx
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_memory_timeline := ia.h_memory_timeline
  h_msg := ia.h_msg
  h_mem_sel := ia.h_mem_sel
  h_mem_wr := ia.h_mem_wr

structure Claim_lwu (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  lwu_input : PureSpec.LwuInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_lwu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busLd trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_lwu (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_lwu trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  align : ZiskFv.Compliance.MemAlignWitness
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
    i.val (busLd trace binding i c.execRow).e1
  h_opcode_assumptions : PureSpec.lwu_state_assumptions c.lwu_input (binding i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      c.lwu_input.r1_val.toNat + (BitVec.signExtend 64 c.lwu_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      c.lwu_input.rd = 0
  h_addr2_idx :
    c.lwu_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADWU_pure c.lwu_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace binding i c.execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

def toRowData_lwu {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_lwu trace i) (dec : Decode_lwu trace binding i c)
    (ia : Inputs_lwu trace binding i c) : RowData_lwu trace binding i where
  lwu_input := c.lwu_input
  regs := ia.regs
  mem := ia.mem
  r_mem := ia.r_mem
  execRow := c.execRow
  align := ia.align
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_width := dec.h_width
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr1 := ia.h_addr1
  h_addr2_zero_iff := ia.h_addr2_zero_iff
  h_addr2_idx := ia.h_addr2_idx
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_memory_timeline := ia.h_memory_timeline
  h_msg := ia.h_msg
  h_mem_sel := ia.h_mem_sel
  h_mem_wr := ia.h_mem_wr

structure Claim_lb (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  lb_input : PureSpec.LbInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_lb (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busLd trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_lb (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_lb trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.lb_state_assumptions c.lb_input (binding i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      c.lb_input.r1_val.toNat + (BitVec.signExtend 64 c.lb_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      c.lb_input.rd = 0
  h_addr2_idx :
    c.lb_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADB_pure c.lb_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace binding i c.execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

def toRowData_lb {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_lb trace i) (dec : Decode_lb trace binding i c)
    (ia : Inputs_lb trace binding i c) : RowData_lb trace binding i where
  lb_input := c.lb_input
  regs := ia.regs
  mem := ia.mem
  r_mem := ia.r_mem
  v := dec.v
  r_binary := dec.r_binary
  offset := dec.offset
  env := dec.env
  h_static := dec.h_static
  h_match := dec.h_match
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_width := dec.h_width
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr1 := ia.h_addr1
  h_addr2_zero_iff := ia.h_addr2_zero_iff
  h_addr2_idx := ia.h_addr2_idx
  execRow := c.execRow
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_memory_timeline := ia.h_memory_timeline
  h_msg := ia.h_msg
  h_mem_sel := ia.h_mem_sel
  h_mem_wr := ia.h_mem_wr

structure Claim_lh (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  lh_input : PureSpec.LhInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_lh (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busLd trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_lh (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_lh trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.lh_state_assumptions c.lh_input (binding i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      c.lh_input.r1_val.toNat + (BitVec.signExtend 64 c.lh_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      c.lh_input.rd = 0
  h_addr2_idx :
    c.lh_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADH_pure c.lh_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace binding i c.execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

def toRowData_lh {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_lh trace i) (dec : Decode_lh trace binding i c)
    (ia : Inputs_lh trace binding i c) : RowData_lh trace binding i where
  lh_input := c.lh_input
  regs := ia.regs
  mem := ia.mem
  r_mem := ia.r_mem
  v := dec.v
  r_binary := dec.r_binary
  offset := dec.offset
  env := dec.env
  h_static := dec.h_static
  h_match := dec.h_match
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_width := dec.h_width
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr1 := ia.h_addr1
  h_addr2_zero_iff := ia.h_addr2_zero_iff
  h_addr2_idx := ia.h_addr2_idx
  execRow := c.execRow
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_memory_timeline := ia.h_memory_timeline
  h_msg := ia.h_msg
  h_mem_sel := ia.h_mem_sel
  h_mem_wr := ia.h_mem_wr

structure Claim_lw (trace : AcceptedZiskTrace) (i : Fin trace.numInstructions) where
  lw_input : PureSpec.LwInput
  execRow : List (Interaction.ExecutionBusEntry FGL)

structure Decode_lw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
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
  h_exec_len : (busLd trace binding i c.execRow).exec_row.length = 2
  h_e0_mult : (busLd trace binding i c.execRow).exec_row[0]!.multiplicity = -1
  h_e1_mult : (busLd trace binding i c.execRow).exec_row[1]!.multiplicity = 1

structure Inputs_lw (trace : AcceptedZiskTrace) (binding : SailTrace trace)
    (i : Fin trace.numInstructions) (c : Claim_lw trace i) : Type where
  regs : ZiskFv.Compliance.ModeRegsFull
  mem : Valid_Mem FGL FGL
  r_mem : ℕ
  h_opcode_assumptions : PureSpec.lw_state_assumptions c.lw_input (binding i)
  h_addr1 :
    (mainRowWithRomLd trace binding i).rom.addr1.toNat =
      c.lw_input.r1_val.toNat + (BitVec.signExtend 64 c.lw_input.imm).toNat
  h_addr2_zero_iff :
    Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2 = 0 ↔
      c.lw_input.rd = 0
  h_addr2_idx :
    c.lw_input.rd.toNat =
      (Transpiler.wrap_to_regidx (mainRowWithRomLd trace binding i).rom.addr2).val
  h_risc_v_assumptions :
    RISC_V_assumptions (binding i) regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
  h_nextPC_matches :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((busLd trace binding i c.execRow).exec_row[1]!.pc).val))
      = (PureSpec.execute_LOADW_pure c.lw_input).nextPC
  h_memory_timeline :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd trace binding i c.execRow).e1
  h_msg :
    loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace binding i)
  h_mem_sel : mem.sel r_mem = 1
  h_mem_wr : mem.wr r_mem = 0

def toRowData_lw {trace : AcceptedZiskTrace} {binding : SailTrace trace}
    {i : Fin trace.numInstructions}
    (c : Claim_lw trace i) (dec : Decode_lw trace binding i c)
    (ia : Inputs_lw trace binding i c) : RowData_lw trace binding i where
  lw_input := c.lw_input
  regs := ia.regs
  mem := ia.mem
  r_mem := ia.r_mem
  v := dec.v
  r_binary := dec.r_binary
  offset := dec.offset
  env := dec.env
  h_static := dec.h_static
  h_match := dec.h_match
  h_main_active := dec.h_main_active
  h_main_op := dec.h_main_op
  h_store_pc := dec.h_store_pc
  h_width := dec.h_width
  h_opcode_assumptions := ia.h_opcode_assumptions
  h_addr1 := ia.h_addr1
  h_addr2_zero_iff := ia.h_addr2_zero_iff
  h_addr2_idx := ia.h_addr2_idx
  execRow := c.execRow
  h_risc_v_assumptions := ia.h_risc_v_assumptions
  h_exec_len := dec.h_exec_len
  h_e0_mult := dec.h_e0_mult
  h_e1_mult := dec.h_e1_mult
  h_nextPC_matches := ia.h_nextPC_matches
  h_memory_timeline := ia.h_memory_timeline
  h_msg := ia.h_msg
  h_mem_sel := ia.h_mem_sel
  h_mem_wr := ia.h_mem_wr

end ZiskFv.Compliance
