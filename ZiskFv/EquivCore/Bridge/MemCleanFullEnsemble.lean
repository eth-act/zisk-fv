import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.EquivCore.Bridge.MemClean

/-!
# Full-ensemble constructors for Clean memory witnesses

This module is the T7 handoff layer between the full Clean ensemble balance
proofs and the existing load-side `MemClean` discharge witnesses.  It does
not add assumptions: it packages selected Main/Mem rows and derives the Mem
provider payload match from the full-ensemble same-message equality.
-/

namespace ZiskFv.EquivCore.Bridge.MemClean

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBus

/-- Build the generic load witness from selected full-ensemble Main `b` and
    Mem provider rows.

The caller still supplies the structural pins tying the selected Clean rows
to the legacy validators and ROM/row-shape facts.  The provider-side
`matches_memory_payload` field is derived here from full-ensemble
same-message evidence, preventing it from becoming a separate promise. -/
@[reducible]
def loadCleanWitness_of_full_ensemble_main_b_mem_provider
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (r_main r_mem : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        r1_val.toNat + (BitVec.signExtend 64 imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔ rd = 0)
    (h_addr2_idx :
      rd.toNat = (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_legacy_addr : mem.addr r_mem = bus.e1.ptr)
    (h_mem_wr : mem.wr r_mem = 0) :
    LoadCleanWitness main mem r_main bus r1_val imm rd := by
  refine
    { r_mem := r_mem
      mainRow := eval mainEnv mainRowVar
      memRow := eval memEnv memRowVar
      main_row := h_main_row
      mem_row := h_mem_row
      main_spec := h_main_spec
      store_pc := h_store_pc
      main_b_match := h_main_b_match
      main_c_match := h_main_c_match
      mem_match := ?_
      addr1 := h_addr1
      addr2_zero_iff := h_addr2_zero_iff
      addr2_idx := h_addr2_idx
      mem_sel := h_mem_sel
      mem_legacy_addr := h_mem_legacy_addr
      mem_wr := h_mem_wr }
  exact
    ZiskFv.AirsClean.FullEnsemble.mem_provider_payload_match_of_main_b_match_and_msg_eq
      h_mainEval h_providerEval h_msg h_main_b_match

/-- LD-specialized wrapper around
    `loadCleanWitness_of_full_ensemble_main_b_mem_provider`. -/
@[reducible]
def ldCleanWitness_of_full_ensemble_main_b_mem_provider
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (r_main r_mem : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (ld_input : PureSpec.LdInput)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        ld_input.r1_val.toNat + (BitVec.signExtend 64 ld_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        ld_input.rd = 0)
    (h_addr2_idx :
      ld_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_legacy_addr : mem.addr r_mem = bus.e1.ptr)
    (h_mem_wr : mem.wr r_mem = 0) :
    LdCleanWitness main mem r_main bus ld_input := by
  let w :=
    loadCleanWitness_of_full_ensemble_main_b_mem_provider
      main mem r_main r_mem bus ld_input.r1_val ld_input.imm ld_input.rd
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
      h_addr2_idx h_mem_sel h_mem_legacy_addr h_mem_wr
  exact
    { r_mem := w.r_mem
      mainRow := w.mainRow
      memRow := w.memRow
      main_row := w.main_row
      mem_row := w.mem_row
      main_spec := w.main_spec
      store_pc := w.store_pc
      main_b_match := w.main_b_match
      main_c_match := w.main_c_match
      mem_match := w.mem_match
      addr1 := w.addr1
      addr2_zero_iff := w.addr2_zero_iff
      addr2_idx := w.addr2_idx
      mem_sel := w.mem_sel
      mem_legacy_addr := w.mem_legacy_addr
      mem_wr := w.mem_wr }

/-- Build the SD store witness from a selected full-ensemble Main `c` row. -/
@[reducible]
def sdCleanWitness_of_full_ensemble_main_c
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (sd_input : PureSpec.SdInput)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat)
    (h_b0_value : main.b_0 r_main = ZiskFv.Trusted.lane_lo sd_input.r2_val)
    (h_b1_value : main.b_1 r_main = ZiskFv.Trusted.lane_hi sd_input.r2_val) :
    SdCleanWitness main r_main bus sd_input :=
  { mainRow := eval mainEnv mainRowVar
    main_row := h_main_row
    main_spec := h_main_spec
    store_pc := h_store_pc
    main_c_match := h_main_c_match
    addr2 := h_addr2
    b0_value := h_b0_value
    b1_value := h_b1_value }

/-- Build the SB store witness from a selected full-ensemble Main `c` row. -/
@[reducible]
def sbCleanWitness_of_full_ensemble_main_c
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat)
    (h_b0_value : main.b_0 r_main = ZiskFv.Trusted.lane_lo sb_input.r2_val)
    (h_b1_value : main.b_1 r_main = ZiskFv.Trusted.lane_hi sb_input.r2_val)
    (h_m1 : state.mem[bus.e2.ptr.toNat + 1]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1 : BitVec 8))
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    SbCleanWitness main r_main bus state sb_input :=
  { mainRow := eval mainEnv mainRowVar
    main_row := h_main_row
    main_spec := h_main_spec
    store_pc := h_store_pc
    main_c_match := h_main_c_match
    addr2 := h_addr2
    b0_value := h_b0_value
    b1_value := h_b1_value
    m1 := h_m1
    m2 := h_m2
    m3 := h_m3
    m4 := h_m4
    m5 := h_m5
    m6 := h_m6
    m7 := h_m7 }

/-- Build the SH store witness from a selected full-ensemble Main `c` row. -/
@[reducible]
def shCleanWitness_of_full_ensemble_main_c
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat)
    (h_b0_value : main.b_0 r_main = ZiskFv.Trusted.lane_lo sh_input.r2_val)
    (h_b1_value : main.b_1 r_main = ZiskFv.Trusted.lane_hi sh_input.r2_val)
    (h_m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2 : BitVec 8))
    (h_m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3 : BitVec 8))
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    ShCleanWitness main r_main bus state sh_input :=
  { mainRow := eval mainEnv mainRowVar
    main_row := h_main_row
    main_spec := h_main_spec
    store_pc := h_store_pc
    main_c_match := h_main_c_match
    addr2 := h_addr2
    b0_value := h_b0_value
    b1_value := h_b1_value
    m2 := h_m2
    m3 := h_m3
    m4 := h_m4
    m5 := h_m5
    m6 := h_m6
    m7 := h_m7 }

/-- Build the SW store witness from a selected full-ensemble Main `c` row. -/
@[reducible]
def swCleanWitness_of_full_ensemble_main_c
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {mainEnv : Environment FGL}
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 2))
    (h_addr2 :
      (eval mainEnv mainRowVar).rom.addr2.toNat =
        (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat)
    (h_b0_value : main.b_0 r_main = ZiskFv.Trusted.lane_lo sw_input.r2_val)
    (h_b1_value : main.b_1 r_main = ZiskFv.Trusted.lane_hi sw_input.r2_val)
    (h_m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4 : BitVec 8))
    (h_m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5 : BitVec 8))
    (h_m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6 : BitVec 8))
    (h_m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7 : BitVec 8)) :
    SwCleanWitness main r_main bus state sw_input :=
  { mainRow := eval mainEnv mainRowVar
    main_row := h_main_row
    main_spec := h_main_spec
    store_pc := h_store_pc
    main_c_match := h_main_c_match
    addr2 := h_addr2
    b0_value := h_b0_value
    b1_value := h_b1_value
    m4 := h_m4
    m5 := h_m5
    m6 := h_m6
    m7 := h_m7 }

end ZiskFv.EquivCore.Bridge.MemClean
