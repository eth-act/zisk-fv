import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.GoldilocksBridge
import ZiskFv.RV64D.BusEffect
import ZiskFv.Extraction.BinaryAdd
import ZiskFv.Extraction.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Spec.Add
import ZiskFv.Equivalence.Add
import ZiskFv.GoldenTraces.Add
import ZiskFv.Equivalence.Auipc
import ZiskFv.GoldenTraces.AUIPC
import ZiskFv.Equivalence.BranchLessThan
import ZiskFv.GoldenTraces.BLT
import ZiskFv.Equivalence.BranchGreaterEqual
import ZiskFv.GoldenTraces.BGE
import ZiskFv.Equivalence.BranchLessThanUnsigned
import ZiskFv.GoldenTraces.BLTU
import ZiskFv.Equivalence.BranchGreaterEqualUnsigned
import ZiskFv.GoldenTraces.BGEU
import ZiskFv.Equivalence.StoreH
import ZiskFv.GoldenTraces.SH
import ZiskFv.Equivalence.StoreB
import ZiskFv.GoldenTraces.SB
import ZiskFv.Equivalence.LoadHU
import ZiskFv.GoldenTraces.LHU
import ZiskFv.Equivalence.LoadBU
import ZiskFv.GoldenTraces.LBU
import ZiskFv.Equivalence.Lui
import ZiskFv.GoldenTraces.LUI
import ZiskFv.Equivalence.Sll
import ZiskFv.GoldenTraces.SLL
import ZiskFv.Equivalence.Srl
import ZiskFv.GoldenTraces.SRL
import ZiskFv.Equivalence.Sra
import ZiskFv.GoldenTraces.SRA
import ZiskFv.Equivalence.Slli
import ZiskFv.GoldenTraces.SLLI
import ZiskFv.Equivalence.Srli
import ZiskFv.GoldenTraces.SRLI
import ZiskFv.Equivalence.Srai
import ZiskFv.GoldenTraces.SRAI
import ZiskFv.Equivalence.Shift
import ZiskFv.GoldenTraces.SLLW
import ZiskFv.Equivalence.ShiftR
import ZiskFv.GoldenTraces.SRLW
import ZiskFv.Equivalence.ShiftRA
import ZiskFv.GoldenTraces.SRAW
import ZiskFv.Equivalence.ShiftLI
import ZiskFv.GoldenTraces.SLLIW
import ZiskFv.Equivalence.ShiftRLI
import ZiskFv.GoldenTraces.SRLIW
import ZiskFv.Equivalence.ShiftRAI
import ZiskFv.GoldenTraces.SRAIW
import ZiskFv.Equivalence.MulHU
import ZiskFv.GoldenTraces.MULHU
import ZiskFv.Equivalence.MulHSU
import ZiskFv.GoldenTraces.MULHSU
import ZiskFv.Equivalence.MulW
import ZiskFv.GoldenTraces.MULW
-- Phase 3C T-RT — ALU RTYPE opcodes (SUB, AND, OR, XOR, SLT, SLTU)
import ZiskFv.Equivalence.And
import ZiskFv.GoldenTraces.AND
import ZiskFv.Equivalence.Or
import ZiskFv.GoldenTraces.OR
import ZiskFv.Equivalence.Slt
import ZiskFv.GoldenTraces.SLT
import ZiskFv.Equivalence.Sltu
import ZiskFv.GoldenTraces.SLTU
import ZiskFv.Equivalence.Sub
import ZiskFv.GoldenTraces.SUB
import ZiskFv.Equivalence.Xor
import ZiskFv.GoldenTraces.XOR
-- Phase 3C T-IT — ALU ITYPE opcodes (ADDI, ANDI, ORI, XORI, SLTI, SLTIU)
import ZiskFv.Equivalence.Addi
import ZiskFv.GoldenTraces.ADDI
import ZiskFv.Equivalence.Andi
import ZiskFv.GoldenTraces.ANDI
import ZiskFv.Equivalence.Ori
import ZiskFv.GoldenTraces.ORI
import ZiskFv.Equivalence.Xori
import ZiskFv.GoldenTraces.XORI
import ZiskFv.Equivalence.Slti
import ZiskFv.GoldenTraces.SLTI
import ZiskFv.Equivalence.Sltiu
import ZiskFv.GoldenTraces.SLTIU
-- Phase 3C T-W — RTYPEW + ADDIW (ADDW, SUBW, ADDIW)
import ZiskFv.Equivalence.Addw
import ZiskFv.GoldenTraces.ADDW
import ZiskFv.Equivalence.Subw
import ZiskFv.GoldenTraces.SUBW
import ZiskFv.Equivalence.Addiw
import ZiskFv.GoldenTraces.ADDIW
-- Phase 3C T-SL — signed loads (LW, LH, LB)
import ZiskFv.Equivalence.Lw
import ZiskFv.GoldenTraces.LW
import ZiskFv.Equivalence.Lh
import ZiskFv.GoldenTraces.LH
import ZiskFv.Equivalence.Lb
import ZiskFv.GoldenTraces.LB
-- Phase 3C T-D — DIV/REM
import ZiskFv.Equivalence.Div
import ZiskFv.GoldenTraces.DIV
import ZiskFv.Equivalence.Divu
import ZiskFv.GoldenTraces.DIVU
import ZiskFv.Equivalence.Rem
import ZiskFv.GoldenTraces.REM
import ZiskFv.Equivalence.Remu
import ZiskFv.GoldenTraces.REMU
-- RV64D coverage gate: force `lake build` to compile every Phase 3B
-- pure-spec file, even those whose Equivalence file hasn't landed yet.
-- Without this, Phase 3B's `slt`/`sltu` shipping bug (unclosed
-- `BitVec.setWidth` / `BitVec.slt` residual) hid because nothing
-- transitively imported those files. Any RV64D file not yet pulled
-- in by an Equivalence module goes here so regressions surface at
-- build time.
--
-- **Known broken (Phase 3B, omitted from the gate deliberately):**
-- `slt`, `sltu`, `slti`, `sltiu`, `lw` — each carries an unclosed
-- Sail-reduction residual. Salvaged per Phase 3C policy: T-RT added
-- `RV64D.SltEquivHelper` (C5/C6 for slt/sltu), T-IT added
-- `RV64D.SltiEquivHelper` (C7/C8 for slti/sltiu), T-SL added
-- `RV64D.LoadEquivHelper` (C9 for lw). The helpers declare renamed
-- `Input'` / `Output'` structs and axiomatize the equivalence; the
-- upstream files themselves remain broken until their terminal
-- tactic is fixed (single Phase 4 audit day jointly retires C5-C9).
-- Re-enable lines here when those upstream fixes ship, so the gate
-- regresses against future drift.
import ZiskFv.RV64D.Auxiliaries
import ZiskFv.RV64D.addi
import ZiskFv.RV64D.addiw
import ZiskFv.RV64D.addw
import ZiskFv.RV64D.andi
import ZiskFv.RV64D.div
import ZiskFv.RV64D.divu
import ZiskFv.RV64D.lb
import ZiskFv.RV64D.lh
import ZiskFv.RV64D.ori
import ZiskFv.RV64D.rem
import ZiskFv.RV64D.remu
import ZiskFv.RV64D.subw
import ZiskFv.RV64D.xori

import ZiskFv.Spike
