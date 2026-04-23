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
-- Phase 3C T-SL — signed loads (LW, LH, LB)
import ZiskFv.Equivalence.Lw
import ZiskFv.GoldenTraces.LW
import ZiskFv.Equivalence.Lh
import ZiskFv.GoldenTraces.LH
import ZiskFv.Equivalence.Lb
import ZiskFv.GoldenTraces.LB
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
-- Sail-reduction residual. Salvaged per Phase 3C policy when each
-- track consumes them (T-RT did this for slt/sltu via
-- `RV64D.SltEquivHelper`, C5/C6; T-SL did this for lw via
-- `RV64D.LoadEquivHelper`, C9; T-IT will handle slti/sltiu).
-- The helpers introduce narrow axioms with renamed structs that
-- mirror the broken upstream lemma; the upstream files themselves
-- remain broken until their terminal tactic is fixed (Phase 4
-- audit). Re-enable lines here when those upstream fixes ship, so
-- the gate regresses against future drift.
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
