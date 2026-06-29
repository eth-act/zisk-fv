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
import ZiskFv.Compliance.TraceLevelExport.Base
import ZiskFv.Compliance.Pilot.SubNextPC

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

-- #100 trace-derived SUB: `execRow` is no longer a free `Claim` binder; the SUB
-- arm pins it to the committed-trace `Pilot.execRowOf trace i` (whose producer
-- entry's `pc` reads the next-row Main `pc` column).  The three exec artifacts
-- (`h_exec_len`/`h_e0_mult`/`h_e1_mult`) thereby become `rfl` and are dropped;
-- in their place `Decode_sub` carries the in-circuit transition inputs
-- (the next-row-exists side condition `h_idx` + the R-type/SUB decode pins
-- `h_set_pc`/`h_jmp1`/`h_jmp2`) that `Pilot.sub_nextPC_discharged` consumes to
-- DERIVE the (removed) cross-world `h_nextPC_matches` from the accepted trace's
-- `transitions_hold` certificate.  The `SEGMENT_L1` fixed-column fact is no
-- longer a per-arm binder: it lives once on the trace as `segment_l1_fixed`
-- (read via `trace.mainTable_fixed`), the `main_height`-class shared home.
structure Claim_sub (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_sub (trace : AcceptedZiskTrace numInstructions)
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
  -- transition inputs (replace the removed exec artifacts; all sailTrace-free
  -- rowDecode-class facts): the next row exists, and the SUB/R-type decode pins
  -- `set_pc = 0`, `jmp_offset1 = jmp_offset2 = 4` (Rust lowerer
  -- `create_register_op(…, "sub", 4)` → `zib.j(4,4)`, no `set_pc()`; cf.
  -- `RowShape/Contract.lean` SUB arm, `main.pil:150-152`).  The `SEGMENT_L1`
  -- fixed-column fact is NOT carried per-arm: `Pilot.sub_nextPC_discharged`
  -- reads it off the accepted trace's shared `segment_l1_fixed` certificate
  -- (`trace.mainTable_fixed`), the once-for-all `main_height`-class home.
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

structure Inputs_sub (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  -- #100: the JAL/AUIPC-style PC provenance bridge + no-wrap bound (the same
  -- shapes `Inputs_jal`/`Inputs_jalr` already carry).  `Pilot.sub_nextPC_discharged`
  -- consumes these — together with the `Decode_sub` transition inputs — to DERIVE
  -- the (now-removed) cross-world `h_nextPC_matches` from the in-circuit
  -- `pcHandshakeBetween` transition certificate, rather than asserting it.
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = sub_input.PC.toNat
  h_pc_bound : sub_input.PC.toNat < GL_prime - 4

/-- Per-op residual bundle for the `sub` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sub` bundles them. -/
structure RowData_sub
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sub trace i
  toDecode : Decode_sub trace i toClaim
  toInputs : Inputs_sub trace binding i toClaim

def toRowData_sub {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sub trace i) (dec : Decode_sub trace i c)
    (ia : Inputs_sub trace binding i c) : RowData_sub trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_and (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_and (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_and (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = and_input.PC.toNat
  h_pc_bound : and_input.PC.toNat < GL_prime - 4

/-- Per-op residual bundle for the `and` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_and` bundles them. -/
structure RowData_and
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_and trace i
  toDecode : Decode_and trace i toClaim
  toInputs : Inputs_and trace binding i toClaim

def toRowData_and {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_and trace i) (dec : Decode_and trace i c)
    (ia : Inputs_and trace binding i c) : RowData_and trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_or (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_or (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_or (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = or_input.PC.toNat
  h_pc_bound : or_input.PC.toNat < GL_prime - 4

/-- Per-op residual bundle for the `or` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_or` bundles them. -/
structure RowData_or
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_or trace i
  toDecode : Decode_or trace i toClaim
  toInputs : Inputs_or trace binding i toClaim

def toRowData_or {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_or trace i) (dec : Decode_or trace i c)
    (ia : Inputs_or trace binding i c) : RowData_or trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_xor (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_xor (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_xor (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = xor_input.PC.toNat
  h_pc_bound : xor_input.PC.toNat < GL_prime - 4

/-- Per-op residual bundle for the `xor` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_xor` bundles them. -/
structure RowData_xor
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_xor trace i
  toDecode : Decode_xor trace i toClaim
  toInputs : Inputs_xor trace binding i toClaim

def toRowData_xor {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_xor trace i) (dec : Decode_xor trace i c)
    (ia : Inputs_xor trace binding i c) : RowData_xor trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_slt (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_slt (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_slt (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = slt_input.PC.toNat
  h_pc_bound : slt_input.PC.toNat < GL_prime - 4

/-- Per-op residual bundle for the `slt` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_slt` bundles them. -/
structure RowData_slt
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_slt trace i
  toDecode : Decode_slt trace i toClaim
  toInputs : Inputs_slt trace binding i toClaim

def toRowData_slt {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_slt trace i) (dec : Decode_slt trace i c)
    (ia : Inputs_slt trace binding i c) : RowData_slt trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_sltu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_sltu (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_sltu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = sltu_input.PC.toNat
  h_pc_bound : sltu_input.PC.toNat < GL_prime - 4

/-- Per-op residual bundle for the `sltu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sltu` bundles them. -/
structure RowData_sltu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sltu trace i
  toDecode : Decode_sltu trace i toClaim
  toInputs : Inputs_sltu trace binding i toClaim

def toRowData_sltu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sltu trace i) (dec : Decode_sltu trace i c)
    (ia : Inputs_sltu trace binding i c) : RowData_sltu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_andi (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_andi (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_andi (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = andi_input.PC.toNat
  h_pc_bound : andi_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    andi_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `andi` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_andi` bundles them. -/
structure RowData_andi
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_andi trace i
  toDecode : Decode_andi trace i toClaim
  toInputs : Inputs_andi trace binding i toClaim

def toRowData_andi {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_andi trace i) (dec : Decode_andi trace i c)
    (ia : Inputs_andi trace binding i c) : RowData_andi trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_ori (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_ori (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_ori (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = ori_input.PC.toNat
  h_pc_bound : ori_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    ori_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `ori` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_ori` bundles them. -/
structure RowData_ori
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_ori trace i
  toDecode : Decode_ori trace i toClaim
  toInputs : Inputs_ori trace binding i toClaim

def toRowData_ori {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_ori trace i) (dec : Decode_ori trace i c)
    (ia : Inputs_ori trace binding i c) : RowData_ori trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_xori (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_xori (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_xori (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = xori_input.PC.toNat
  h_pc_bound : xori_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    xori_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `xori` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_xori` bundles them. -/
structure RowData_xori
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_xori trace i
  toDecode : Decode_xori trace i toClaim
  toInputs : Inputs_xori trace binding i toClaim

def toRowData_xori {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_xori trace i) (dec : Decode_xori trace i c)
    (ia : Inputs_xori trace binding i c) : RowData_xori trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_slti (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_slti (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_slti (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = slti_input.PC.toNat
  h_pc_bound : slti_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    slti_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `slti` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_slti` bundles them. -/
structure RowData_slti
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_slti trace i
  toDecode : Decode_slti trace i toClaim
  toInputs : Inputs_slti trace binding i toClaim

def toRowData_slti {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_slti trace i) (dec : Decode_slti trace i c)
    (ia : Inputs_slti trace binding i c) : RowData_slti trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_sltiu (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  imm : BitVec 12

structure Decode_sltiu (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_sltiu (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = sltiu_input.PC.toNat
  h_pc_bound : sltiu_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    sltiu_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `sltiu` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sltiu` bundles them. -/
structure RowData_sltiu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sltiu trace i
  toDecode : Decode_sltiu trace i toClaim
  toInputs : Inputs_sltiu trace binding i toClaim

def toRowData_sltiu {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sltiu trace i) (dec : Decode_sltiu trace i c)
    (ia : Inputs_sltiu trace binding i c) : RowData_sltiu trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_sll (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_sll (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_sll (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = sll_input.PC.toNat
  h_pc_bound : sll_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    sll_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `sll` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sll` bundles them. -/
structure RowData_sll
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sll trace i
  toDecode : Decode_sll trace i toClaim
  toInputs : Inputs_sll trace binding i toClaim

def toRowData_sll {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sll trace i) (dec : Decode_sll trace i c)
    (ia : Inputs_sll trace binding i c) : RowData_sll trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_srl (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_srl (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_srl (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = srl_input.PC.toNat
  h_pc_bound : srl_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    srl_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `srl` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_srl` bundles them. -/
structure RowData_srl
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_srl trace i
  toDecode : Decode_srl trace i toClaim
  toInputs : Inputs_srl trace binding i toClaim

def toRowData_srl {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_srl trace i) (dec : Decode_srl trace i c)
    (ia : Inputs_srl trace binding i c) : RowData_srl trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_sra (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_sra (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_sra (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = sra_input.PC.toNat
  h_pc_bound : sra_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    sra_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `sra` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sra` bundles them. -/
structure RowData_sra
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sra trace i
  toDecode : Decode_sra trace i toClaim
  toInputs : Inputs_sra trace binding i toClaim

def toRowData_sra {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sra trace i) (dec : Decode_sra trace i c)
    (ia : Inputs_sra trace binding i c) : RowData_sra trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_slli (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  shamt : BitVec 6

structure Decode_slli (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_slli (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = slli_input.PC.toNat
  h_pc_bound : slli_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    slli_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `slli` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_slli` bundles them. -/
structure RowData_slli
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_slli trace i
  toDecode : Decode_slli trace i toClaim
  toInputs : Inputs_slli trace binding i toClaim

def toRowData_slli {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_slli trace i) (dec : Decode_slli trace i c)
    (ia : Inputs_slli trace binding i c) : RowData_slli trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_srli (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  shamt : BitVec 6

structure Decode_srli (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_srli (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = srli_input.PC.toNat
  h_pc_bound : srli_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    srli_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `srli` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_srli` bundles them. -/
structure RowData_srli
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_srli trace i
  toDecode : Decode_srli trace i toClaim
  toInputs : Inputs_srli trace binding i toClaim

def toRowData_srli {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_srli trace i) (dec : Decode_srli trace i c)
    (ia : Inputs_srli trace binding i c) : RowData_srli trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_srai (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  rd : regidx
  shamt : BitVec 6

structure Decode_srai (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_srai (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = srai_input.PC.toNat
  h_pc_bound : srai_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    srai_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `srai` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_srai` bundles them. -/
structure RowData_srai
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_srai trace i
  toDecode : Decode_srai trace i toClaim
  toInputs : Inputs_srai trace binding i toClaim

def toRowData_srai {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_srai trace i) (dec : Decode_srai trace i c)
    (ia : Inputs_srai trace binding i c) : RowData_srai trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_sllw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_sllw (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_sllw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = sllw_input.PC.toNat
  h_pc_bound : sllw_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    sllw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `sllw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sllw` bundles them. -/
structure RowData_sllw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sllw trace i
  toDecode : Decode_sllw trace i toClaim
  toInputs : Inputs_sllw trace binding i toClaim

def toRowData_sllw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sllw trace i) (dec : Decode_sllw trace i c)
    (ia : Inputs_sllw trace binding i c) : RowData_sllw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_srlw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_srlw (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_srlw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = srlw_input.PC.toNat
  h_pc_bound : srlw_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    srlw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `srlw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_srlw` bundles them. -/
structure RowData_srlw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_srlw trace i
  toDecode : Decode_srlw trace i toClaim
  toInputs : Inputs_srlw trace binding i toClaim

def toRowData_srlw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_srlw trace i) (dec : Decode_srlw trace i c)
    (ia : Inputs_srlw trace binding i c) : RowData_srlw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_sraw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  r1 : regidx
  r2 : regidx
  rd : regidx

structure Decode_sraw (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_sraw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = sraw_input.PC.toNat
  h_pc_bound : sraw_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    sraw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `sraw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sraw` bundles them. -/
structure RowData_sraw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sraw trace i
  toDecode : Decode_sraw trace i toClaim
  toInputs : Inputs_sraw trace binding i toClaim

def toRowData_sraw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sraw trace i) (dec : Decode_sraw trace i c)
    (ia : Inputs_sraw trace binding i c) : RowData_sraw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_slliw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  slliw_input : PureSpec.SlliwInput
  r1 : regidx
  rd : regidx

structure Decode_slliw (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_slliw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.slliw_input.PC.toNat
  h_pc_bound : c.slliw_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    c.slliw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `slliw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_slliw` bundles them. -/
structure RowData_slliw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_slliw trace i
  toDecode : Decode_slliw trace i toClaim
  toInputs : Inputs_slliw trace binding i toClaim

def toRowData_slliw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_slliw trace i) (dec : Decode_slliw trace i c)
    (ia : Inputs_slliw trace binding i c) : RowData_slliw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_srliw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  srliw_input : PureSpec.SrliwInput
  r1 : regidx
  rd : regidx

structure Decode_srliw (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_srliw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.srliw_input.PC.toNat
  h_pc_bound : c.srliw_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    c.srliw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `srliw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_srliw` bundles them. -/
structure RowData_srliw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_srliw trace i
  toDecode : Decode_srliw trace i toClaim
  toInputs : Inputs_srliw trace binding i toClaim

def toRowData_srliw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_srliw trace i) (dec : Decode_srliw trace i c)
    (ia : Inputs_srliw trace binding i c) : RowData_srliw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

structure Claim_sraiw (trace : AcceptedZiskTrace numInstructions) (i : Fin trace.numInstructions) where
  sraiw_input : PureSpec.SraiwInput
  r1 : regidx
  rd : regidx

structure Decode_sraiw (trace : AcceptedZiskTrace numInstructions)
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

structure Inputs_sraiw (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
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
  h_pc_bridge :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
      = c.sraiw_input.PC.toNat
  h_pc_bound : c.sraiw_input.PC.toNat < GL_prime - 4
  h_rd_idx :
    c.sraiw_input.rd =
      Transpiler.wrap_to_regidx (busSub trace i (Pilot.execRowOf trace i)).e2.ptr

/-- Per-op residual bundle for the `sraiw` archetype: the 3-way `Claim`/`Decode`/`Inputs`
    split is the single declaration site for every field; `RowData_sraiw` bundles them. -/
structure RowData_sraiw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) where
  toClaim : Claim_sraiw trace i
  toDecode : Decode_sraiw trace i toClaim
  toInputs : Inputs_sraiw trace binding i toClaim

def toRowData_sraiw {trace : AcceptedZiskTrace numInstructions} {binding : SailTrace trace.numInstructions}
    {i : Fin trace.numInstructions}
    (c : Claim_sraiw trace i) (dec : Decode_sraiw trace i c)
    (ia : Inputs_sraiw trace binding i c) : RowData_sraiw trace binding i where
  toClaim := c
  toDecode := dec
  toInputs := ia

end ZiskFv.Compliance
