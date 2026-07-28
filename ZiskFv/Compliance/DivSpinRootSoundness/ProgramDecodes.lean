import ZiskFv.Compliance.DivSpinRootSoundness.Decode

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.DivSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.AirsClean.Main
open ZiskFv.Trusted

namespace ZiskFv.Compliance.DivSpinRootSoundness

def divSpinAddiX1ProgramDecode :
    ProgramDecode_addi divSpinAcceptedTrace
      ZiskFv.Compliance.DivSpinRootSoundness.divSpinAddiX1Index
      ZiskFv.Compliance.DivSpinRootSoundness.divSpinAddiX1Claim where
  h_idx := by
    rw [divSpinAcceptedTrace_mainTable_eq]
    norm_num [divSpinAddiX1Index, divSpinMainRows, divSpinMainTable, mainRowsTable]
  bits := divSpinAddiBits
  h_bits_ieo := rfl
  h_bits_m32 := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_bits_b_src_imm := rfl
  h_prog := by
    intro j hline
    have hj := ZiskFv.Compliance.DivSpinRootSoundness.divSpinProgramIndex_eq
      divSpinAddiX1Index j hline
    subst j
    norm_num [divSpinAcceptedTrace, divSpinProgram, divSpinAddiX1ProgramRow,
      divSpinAddiX1Claim, x1, Transpiler.ind, regidx_to_fin, packFlags,
      divSpinAddiBits, ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits,
      ZiskFv.AirsClean.boolF]
    all_goals decide

def divSpinAddiX2ProgramDecode :
    ProgramDecode_addi divSpinAcceptedTrace
      ZiskFv.Compliance.DivSpinRootSoundness.divSpinAddiX2Index
      ZiskFv.Compliance.DivSpinRootSoundness.divSpinAddiX2Claim where
  h_idx := by
    rw [divSpinAcceptedTrace_mainTable_eq]
    change 2 < 5
    decide
  bits := divSpinAddiBits
  h_bits_ieo := rfl
  h_bits_m32 := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_bits_b_src_imm := rfl
  h_prog := by
    intro j hline
    have hj := ZiskFv.Compliance.DivSpinRootSoundness.divSpinProgramIndex_eq
      divSpinAddiX2Index j hline
    subst j
    norm_num [divSpinAcceptedTrace, divSpinProgram, divSpinAddiX2ProgramRow,
      divSpinAddiX2Claim, x2, Transpiler.ind, regidx_to_fin, packFlags,
      divSpinAddiBits, ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits,
      ZiskFv.AirsClean.boolF]
    all_goals decide

def divSpinDivProgramDecode :
    ProgramDecode_div divSpinAcceptedTrace
      ZiskFv.Compliance.DivSpinRootSoundness.divSpinDivIndex
      ZiskFv.Compliance.DivSpinRootSoundness.divSpinDivClaim where
  h_idx := by
    rw [divSpinAcceptedTrace_mainTable_eq]
    norm_num [divSpinDivIndex, divSpinMainRows, divSpinMainTable, mainRowsTable]
  arith_mem := by
    refine {
      row := divSpinDivRow
      row_eq := ?_
      store_pc_zero := by rfl
      rd_write_match := ?_
    }
    · change divSpinDivRow.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable
            divSpinAcceptedTrace.program divSpinAcceptedTrace.mainTable) 2
      exact (congrArg MainRowWithRom.core
        (divSpinAcceptedMainRowAt divSpinDivIndex)).symm
    · simp [divSpinAcceptedMainRowAt, divSpinDivIndex, divSpinMainRows,
        divSpinDivRow, divSpinDivRowTemplate, mainRomRowOf,
        withMainRegisterPrevious, busSub, Pilot.execRowOf,
        ZiskFv.Airs.MemoryBus.matches_memory_entry,
        ZiskFv.AirsClean.Main.cMemMessage,
        ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry,
        AbstractInteraction.eval, ChannelInteraction.toRaw, Channel.emitted,
        Expression.eval, mainConstVar]
  bounds := by
    constructor <;>
      norm_num [busSub, Pilot.execRowOf, divSpinAcceptedTrace_mainTable_eq,
        divSpinAcceptedMainRowAt, divSpinDivIndex, divSpinMainRows, divSpinDivRow,
        divSpinDivRowTemplate, mainRomRowOf, withMainRegisterPrevious,
        divSpinDivProgramRow, divSpinDivBits, ZiskFv.AirsClean.boolF,
        ZiskFv.Channels.MemoryBusBytes.byteAt]
  bits := divSpinDivBits
  h_bits_ieo := rfl
  h_bits_m32 := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_prog := by
    intro j hline
    have hj := ZiskFv.Compliance.DivSpinRootSoundness.divSpinProgramIndex_eq
      divSpinDivIndex j hline
    subst j
    norm_num [divSpinAcceptedTrace, divSpinProgram, divSpinDivProgramRow,
      divSpinDivClaim, x3, Transpiler.ind, regidx_to_fin, packFlags,
      divSpinDivBits, ZiskFv.AirsClean.boolF, ZiskFv.Trusted.OP_DIV]
    all_goals decide

def divSpinJalProgramDecode :
    ProgramDecode_jal divSpinAcceptedTrace
      ZiskFv.Compliance.DivSpinRootSoundness.divSpinJalIndex
      ZiskFv.Compliance.DivSpinRootSoundness.divSpinJalClaim where
  h_idx := by
    rw [divSpinAcceptedTrace_mainTable_eq]
    norm_num [ZiskFv.Compliance.DivSpinRootSoundness.divSpinJalIndex,
      divSpinMainRows, divSpinMainTable, mainRowsTable]
  bits := AddSpinWitness.addSpinJalBits
  h_bits_ieo := rfl
  h_bits_m32 := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_prog := by
    intro j hline
    have hj := ZiskFv.Compliance.DivSpinRootSoundness.divSpinProgramIndex_eq
      ZiskFv.Compliance.DivSpinRootSoundness.divSpinJalIndex j hline
    subst j
    norm_num [divSpinAcceptedTrace, divSpinProgram, divSpinJalProgramRow,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalProgramRow,
      ZiskFv.Compliance.DivSpinRootSoundness.divSpinJalClaim,
      ZiskFv.Compliance.DivSpinRootSoundness.x0,
      Transpiler.ind, regidx_to_fin, packFlags, AddSpinWitness.addSpinJalBits,
      ZiskFv.AirsClean.boolF]
    all_goals decide +revert
