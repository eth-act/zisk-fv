import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Compliance.AeneasBridgeTrust.Base

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : Nat}

/-- Construct the SB store envelope while deriving its Main `OP_COPYB` pins,
store width, and Clean `store_pc` fact from extracted row-shape equalities. -/
def OpEnvelope.sbOfExtractedShape
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 1)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
    (h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sb_state_assumptions sb_input state)
        (PureSpec.execute_STOREB_pure sb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sb_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sb_input.r2_val)
    (h_m1 : state.mem[bus.e2.ptr.toNat + 1]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1 : BitVec 8))
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    OpEnvelope state m r_main :=
  OpEnvelope.sb sb_input regs bus
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    (by simpa [natF] using
      MainRowProvenance.indWidth_of_extracted_shape provenance h_width)
    h_opcode_assumptions promises h_main_row h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_c_match h_addr2 h_b0_value h_b1_value h_m1 h_m2 h_m3 h_m4 h_m5 h_m6 h_m7

/-- Construct the SH store envelope while deriving its Main store shape fields
from extracted row-shape equalities. -/
def OpEnvelope.shOfExtractedShape
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 2)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
    (h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sh_state_assumptions sh_input state)
        (PureSpec.execute_STOREH_pure sh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sh_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sh_input.r2_val)
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    OpEnvelope state m r_main :=
  OpEnvelope.sh sh_input regs bus
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    (by simpa [natF] using
      MainRowProvenance.indWidth_of_extracted_shape provenance h_width)
    h_opcode_assumptions promises h_main_row h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_c_match h_addr2 h_b0_value h_b1_value h_m2 h_m3 h_m4 h_m5 h_m6 h_m7

/-- Construct the SW store envelope while deriving its Main store shape fields
from extracted row-shape equalities. -/
def OpEnvelope.swOfExtractedShape
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 4)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
    (h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sw_state_assumptions sw_input state)
        (PureSpec.execute_STOREW_pure sw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sw_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sw_input.r2_val)
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    OpEnvelope state m r_main :=
  OpEnvelope.sw sw_input regs bus
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    (by simpa [natF] using
      MainRowProvenance.indWidth_of_extracted_shape provenance h_width)
    h_opcode_assumptions promises h_main_row h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_c_match h_addr2 h_b0_value h_b1_value h_m4 h_m5 h_m6 h_m7

/-- Construct the SD store envelope while deriving its Main `OP_COPYB` pins and
Clean `store_pc` fact from extracted row-shape equalities. -/
def OpEnvelope.sdOfExtractedShape
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
    (h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sd_state_assumptions sd_input state)
        (PureSpec.execute_STORED_pure sd_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sd_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sd_input.r2_val) :
    OpEnvelope state m r_main :=
  OpEnvelope.sd sd_input regs bus
    (MainRowProvenance.copybPins_of_extracted_shape provenance h_op h_internal)
    h_opcode_assumptions promises h_main_row h_main_spec
    (MainRowProvenance.cleanStorePcZero_of_extracted_shape provenance
      h_store_pc_shape h_main_row)
    h_main_c_match h_addr2 h_b0_value h_b1_value

/-- The SB bridge predicate is derivable for the envelope constructed from
extracted store row-shape equalities and the remaining dynamic store facts. -/
theorem OpEnvelope.aeneasBridgeTrust_sbOfExtractedShape
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 1)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
    (h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sb_state_assumptions sb_input state)
        (PureSpec.execute_STOREB_pure sb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sb_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sb_input.r2_val)
    (h_m1 : state.mem[bus.e2.ptr.toNat + 1]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1 : BitVec 8))
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    (OpEnvelope.sbOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sb_input regs bus provenance h_op h_internal h_width h_store_pc_shape
      h_opcode_assumptions promises h_main_row h_main_spec h_main_c_match
      h_addr2 h_b0_value h_b1_value h_m1 h_m2 h_m3 h_m4 h_m5 h_m6
      h_m7).aeneasBridgeTrust := by
  unfold OpEnvelope.sbOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width,
    h_b0_value, h_b1_value⟩

/-- The SH bridge predicate is derivable for the envelope constructed from
extracted store row-shape equalities and the remaining dynamic store facts. -/
theorem OpEnvelope.aeneasBridgeTrust_shOfExtractedShape
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 2)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
    (h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sh_state_assumptions sh_input state)
        (PureSpec.execute_STOREH_pure sh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sh_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sh_input.r2_val)
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    (OpEnvelope.shOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sh_input regs bus provenance h_op h_internal h_width h_store_pc_shape
      h_opcode_assumptions promises h_main_row h_main_spec h_main_c_match
      h_addr2 h_b0_value h_b1_value h_m2 h_m3 h_m4 h_m5 h_m6
      h_m7).aeneasBridgeTrust := by
  unfold OpEnvelope.shOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width,
    h_b0_value, h_b1_value⟩

/-- The SW bridge predicate is derivable for the envelope constructed from
extracted store row-shape equalities and the remaining dynamic store facts. -/
theorem OpEnvelope.aeneasBridgeTrust_swOfExtractedShape
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_width : provenance.extractedRow.indWidth = 4)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
    (h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sw_state_assumptions sw_input state)
        (PureSpec.execute_STOREW_pure sw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sw_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sw_input.r2_val)
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    (OpEnvelope.swOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sw_input regs bus provenance h_op h_internal h_width h_store_pc_shape
      h_opcode_assumptions promises h_main_row h_main_spec h_main_c_match
      h_addr2 h_b0_value h_b1_value h_m4 h_m5 h_m6 h_m7).aeneasBridgeTrust := by
  unfold OpEnvelope.swOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨by simpa [natF] using
    MainRowProvenance.indWidth_of_extracted_shape provenance h_width,
    h_b0_value, h_b1_value⟩

/-- The SD bridge predicate is derivable for the envelope constructed from
extracted store row-shape equalities and the remaining dynamic store facts. -/
theorem OpEnvelope.aeneasBridgeTrust_sdOfExtractedShape
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_store_pc_shape : provenance.extractedRow.storePc = false)
    (h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input state)
    (promises : ZiskFv.EquivCore.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sd_state_assumptions sd_input state)
        (PureSpec.execute_STORED_pure sd_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat)
    (h_b0_value : m.b_0 r_main = ZiskFv.Trusted.lane_lo sd_input.r2_val)
    (h_b1_value : m.b_1 r_main = ZiskFv.Trusted.lane_hi sd_input.r2_val) :
    (OpEnvelope.sdOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sd_input regs bus provenance h_op h_internal h_store_pc_shape
      h_opcode_assumptions promises h_main_row h_main_spec h_main_c_match
      h_addr2 h_b0_value h_b1_value).aeneasBridgeTrust := by
  unfold OpEnvelope.sdOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_b0_value, h_b1_value⟩


end ZiskFv.Compliance
