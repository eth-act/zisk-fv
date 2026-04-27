import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.TranspileConsumers
import ZiskFv.Extraction.ArithTable
import ZiskFv.Airs.Arith.ArithTable
import ZiskFv.Airs.Arith.ArithRangeTable
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.GoldilocksBridge
import ZiskFv.RV64D.BusEffect
import ZiskFv.Extraction.BinaryAdd
import ZiskFv.Extraction.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
-- Track O POC: pilout bus-emission extraction + derivation lemma.
import ZiskFv.Extraction.Buses
import ZiskFv.Airs.BusShape
-- Track Q POC: operation-bus effect model + chip_op_bus_hyps lemmas.
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
-- Track N K2: promoted lane-match theorems for register memory-bus entries.
import ZiskFv.Airs.MemoryBus.LaneMatch
-- Track N K3: FGL → BitVec 64 arithmetic-extension lifts (h_rd_val bridges).
import ZiskFv.Fundamentals.PackedBitVec.Extensions
import ZiskFv.Spec.Add
import ZiskFv.Equivalence.Add
import ZiskFv.GoldenTraces.Add
-- Phase 4 T-LINT re-export audit: missing direct imports for older opcodes
-- whose equivalence theorems shipped before the coverage-gate discipline.
import ZiskFv.Equivalence.BranchEqual
import ZiskFv.Equivalence.BranchNotEqual
import ZiskFv.Equivalence.Jal
import ZiskFv.Equivalence.Jalr
import ZiskFv.Equivalence.LoadD
import ZiskFv.Equivalence.LoadWU
import ZiskFv.Equivalence.Mul
import ZiskFv.Equivalence.MulH
import ZiskFv.Equivalence.StoreD
import ZiskFv.Equivalence.StoreW
import ZiskFv.Equivalence.Auipc
import ZiskFv.GoldenTraces.AUIPC
import ZiskFv.Equivalence.Fence
import ZiskFv.Equivalence.Divuw
import ZiskFv.Equivalence.Remuw
import ZiskFv.Equivalence.Divw
import ZiskFv.Equivalence.Remw
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
-- Track N K4 — Signed-case PackedBitVec + MulFieldSigned + DivFieldSigned
import ZiskFv.Fundamentals.PackedBitVec.Signed
import ZiskFv.Spec.MulFieldSigned
import ZiskFv.Spec.DivFieldSigned
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
-- Any RV64D file not yet pulled in by an Equivalence module goes here
-- so regressions surface at build time.
import ZiskFv.RV64D.Auxiliaries
import ZiskFv.RV64D.addi
import ZiskFv.RV64D.addiw
import ZiskFv.RV64D.addw
import ZiskFv.RV64D.andi
import ZiskFv.RV64D.div
import ZiskFv.RV64D.divu
import ZiskFv.RV64D.lb
import ZiskFv.RV64D.lh
import ZiskFv.RV64D.lw
import ZiskFv.RV64D.ori
import ZiskFv.RV64D.rem
import ZiskFv.RV64D.remu
import ZiskFv.RV64D.slt
import ZiskFv.RV64D.slti
import ZiskFv.RV64D.sltiu
import ZiskFv.RV64D.sltu
import ZiskFv.RV64D.subw
import ZiskFv.RV64D.xori

-- Track N Phase 2: per-shape h_rd_val derivation lemmas.
import ZiskFv.Equivalence.RdValDerivation.Arith
import ZiskFv.Equivalence.RdValDerivation.JumpUType
import ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned
import ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned

import ZiskFv.Spike
