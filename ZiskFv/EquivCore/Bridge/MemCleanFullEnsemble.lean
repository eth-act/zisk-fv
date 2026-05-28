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
to the legacy validators and ROM/transpile facts.  The provider-side
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

end ZiskFv.EquivCore.Bridge.MemClean
