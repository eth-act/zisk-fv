import ZiskFv.Compliance.TraceLevelExport.CanonicalSyntaxBoundary

/-!
# Explicit current narrow-load provider obstruction

These are DOMAIN-OBSTRUCTION theorems, not contradiction-based Root closure.
The current Core insists on a direct native Mem six-tuple, whose width is8.
The actual narrow-load decode pins an indirect width1/2/4. Their simultaneous
inhabitance is impossible. No protected Core/decoder/dispatcher is changed,
and no supported source opcode is silently excluded or claimed solved.
-/

namespace ZiskFv.Compliance.CanonicalSyntaxBoundary.NarrowLoadProviderObstruction

open Goldilocks Air.Flat
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.Channels.MemoryBus

/-- Project the REAL typed six-tuple equality; native Mem width is literally8. -/
theorem native_link_width
    (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (memRow : ZiskFv.AirsClean.Mem.MemRow FGL)
    (message : loadMemMsg memRow = loadMainMsg mainRow) :
    (8 : FGL) = mainRow.rom.b_src_ind * (mainRow.core.ind_width - 8) + 8 := by
  have tuple := ZiskFv.AirsClean.FullEnsemble.memBusMessage_eq_of_eval_emitted_provider_msg_eq
    (mainMsg := ZiskFv.AirsClean.Main.bMemMessageExpr (mainConstVar mainRow))
    (providerMsg := ZiskFv.AirsClean.Mem.memBusMessageExpr (memConstVar memRow))
    (mainMult := (-1 : Expression FGL)) (providerMult := (1 : Expression FGL))
    (mainEnv := loadEvalEnv) (providerEnv := loadEvalEnv) (h_msg := message)
  have width := congrArg MemBusMessage.width tuple
  simpa only [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr,
    ZiskFv.AirsClean.Main.eval_bMemMessageExpr, eval_memConstVar, eval_mainConstVar,
    ZiskFv.AirsClean.Mem.memBusMessage, ZiskFv.AirsClean.Main.bMemMessage] using width

/-- An actual indirect narrow request cannot equal a native word-eight tuple. -/
theorem no_native_link_of_indirect_narrow
    (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (memRow : ZiskFv.AirsClean.Mem.MemRow FGL)
    (indirect : mainRow.rom.b_src_ind = 1)
    (narrow : mainRow.core.ind_width ≠ 8) :
    loadMemMsg memRow ≠ loadMainMsg mainRow := by
  intro message
  have width := native_link_width mainRow memRow message
  rw [indirect] at width
  exact narrow (by simpa only [one_mul, sub_add_cancel] using width.symm)

/-- Explicit inherited LBU Core/decode incompatibility; NOT semantic progress. -/
theorem lbu_core_incompatible_with_decode {n : Nat} {trace : AcceptedZiskTrace n}
    (history : SailTrace n) (i : Fin n) (claim : Claim_lbu trace i)
    (decoded : Decode_lbu trace i claim) (core : InputsCore_lbu trace history i claim) : False := by
  apply no_native_link_of_indirect_narrow (mainRowWithRomLd trace i)
    (ZiskFv.AirsClean.Mem.rowAt core.mem core.r_mem) decoded.h_b_src_ind ?_ core.h_msg
  rw [mainRowWithRomLd_core trace history i]
  change (mainOfTable trace.program trace.mainTable).ind_width i.val ≠ 8
  rw [decoded.h_width]
  decide +kernel

/-- Explicit inherited LHU Core/decode incompatibility; NOT semantic progress. -/
theorem lhu_core_incompatible_with_decode {n : Nat} {trace : AcceptedZiskTrace n}
    (history : SailTrace n) (i : Fin n) (claim : Claim_lhu trace i)
    (decoded : Decode_lhu trace i claim) (core : InputsCore_lhu trace history i claim) : False := by
  apply no_native_link_of_indirect_narrow (mainRowWithRomLd trace i)
    (ZiskFv.AirsClean.Mem.rowAt core.mem core.r_mem) decoded.h_b_src_ind ?_ core.h_msg
  rw [mainRowWithRomLd_core trace history i]
  change (mainOfTable trace.program trace.mainTable).ind_width i.val ≠ 8
  rw [decoded.h_width]
  decide +kernel

/-- Explicit inherited LWU Core/decode incompatibility; NOT semantic progress. -/
theorem lwu_core_incompatible_with_decode {n : Nat} {trace : AcceptedZiskTrace n}
    (history : SailTrace n) (i : Fin n) (claim : Claim_lwu trace i)
    (decoded : Decode_lwu trace i claim) (core : InputsCore_lwu trace history i claim) : False := by
  apply no_native_link_of_indirect_narrow (mainRowWithRomLd trace i)
    (ZiskFv.AirsClean.Mem.rowAt core.mem core.r_mem) decoded.h_b_src_ind ?_ core.h_msg
  rw [mainRowWithRomLd_core trace history i]
  change (mainOfTable trace.program trace.mainTable).ind_width i.val ≠ 8
  rw [decoded.h_width]
  decide +kernel

/-- Explicit inherited LB Core/decode incompatibility; NOT semantic progress. -/
theorem lb_core_incompatible_with_decode {n : Nat} {trace : AcceptedZiskTrace n}
    (history : SailTrace n) (i : Fin n) (claim : Claim_lb trace i)
    (decoded : Decode_lb trace i claim) (core : InputsCore_lb trace history i claim) : False := by
  apply no_native_link_of_indirect_narrow (mainRowWithRomLd trace i)
    (ZiskFv.AirsClean.Mem.rowAt core.mem core.r_mem) decoded.h_b_src_ind ?_ core.h_msg
  rw [mainRowWithRomLd_core trace history i]
  change (mainOfTable trace.program trace.mainTable).ind_width i.val ≠ 8
  rw [decoded.h_width]
  decide +kernel

/-- Explicit inherited LH Core/decode incompatibility; NOT semantic progress. -/
theorem lh_core_incompatible_with_decode {n : Nat} {trace : AcceptedZiskTrace n}
    (history : SailTrace n) (i : Fin n) (claim : Claim_lh trace i)
    (decoded : Decode_lh trace i claim) (core : InputsCore_lh trace history i claim) : False := by
  apply no_native_link_of_indirect_narrow (mainRowWithRomLd trace i)
    (ZiskFv.AirsClean.Mem.rowAt core.mem core.r_mem) decoded.h_b_src_ind ?_ core.h_msg
  rw [mainRowWithRomLd_core trace history i]
  change (mainOfTable trace.program trace.mainTable).ind_width i.val ≠ 8
  rw [decoded.h_width]
  decide +kernel

/-- Explicit inherited LW Core/decode incompatibility; NOT semantic progress. -/
theorem lw_core_incompatible_with_decode {n : Nat} {trace : AcceptedZiskTrace n}
    (history : SailTrace n) (i : Fin n) (claim : Claim_lw trace i)
    (decoded : Decode_lw trace i claim) (core : InputsCore_lw trace history i claim) : False := by
  apply no_native_link_of_indirect_narrow (mainRowWithRomLd trace i)
    (ZiskFv.AirsClean.Mem.rowAt core.mem core.r_mem) decoded.h_b_src_ind ?_ core.h_msg
  rw [mainRowWithRomLd_core trace history i]
  change (mainOfTable trace.program trace.mainTable).ind_width i.val ≠ 8
  rw [decoded.h_width]
  decide +kernel

end ZiskFv.Compliance.CanonicalSyntaxBoundary.NarrowLoadProviderObstruction
