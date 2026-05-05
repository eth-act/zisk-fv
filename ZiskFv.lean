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
import ZiskFv.Extraction.Buses
import ZiskFv.Extraction.OperationBuses
import ZiskFv.Airs.BusShape
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Extraction.MemoryBuses
import ZiskFv.Airs.MemoryBus.Projection
import ZiskFv.Airs.MemoryBus.BusShape
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Extraction.Mem
import ZiskFv.Airs.Mem
import ZiskFv.Extraction.MemAlign
import ZiskFv.Extraction.MemAlignByte
import ZiskFv.Extraction.MemAlignReadByte
import ZiskFv.Extraction.MemAlignWriteByte
import ZiskFv.Airs.MemAlign
import ZiskFv.Airs.MemAlignByte
import ZiskFv.Airs.MemAlignReadByte
import ZiskFv.Airs.MemAlignWriteByte
-- Track N K3: FGL → BitVec 64 arithmetic-extension lifts (h_rd_val bridges).
import ZiskFv.Fundamentals.PackedBitVec.Extensions
-- Track N B.5: Goldilocks no-wrap toolkit (additive packings).
import ZiskFv.Fundamentals.PackedBitVec.NoWrap
-- finishing4 S1: multiplicative no-wrap toolkit (8-chunk carry chains).
import ZiskFv.Fundamentals.PackedBitVec.MulNoWrap
-- finishing4 S2: signed BitVec.toInt extension (sign-witness pattern + INT_MIN/-1 overflow).
import ZiskFv.Fundamentals.PackedBitVec.SignedNoWrap
-- finishing5 S2: wide-PC no-wrap toolkit (PC values can exceed GL_prime).
import ZiskFv.Fundamentals.PackedBitVec.WidePCNoWrap
import ZiskFv.Spec.Add
import ZiskFv.Equivalence.Add
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
import ZiskFv.Equivalence.Fence
import ZiskFv.Equivalence.Divuw
import ZiskFv.Equivalence.Remuw
import ZiskFv.Equivalence.Divw
import ZiskFv.Equivalence.Remw
import ZiskFv.Equivalence.BranchLessThan
import ZiskFv.Equivalence.BranchGreaterEqual
import ZiskFv.Equivalence.BranchLessThanUnsigned
import ZiskFv.Equivalence.BranchGreaterEqualUnsigned
import ZiskFv.Equivalence.StoreH
import ZiskFv.Equivalence.StoreB
import ZiskFv.Equivalence.LoadHU
import ZiskFv.Equivalence.LoadBU
import ZiskFv.Equivalence.Lui
import ZiskFv.Equivalence.Sll
import ZiskFv.Equivalence.Srl
import ZiskFv.Equivalence.Sra
import ZiskFv.Equivalence.Slli
import ZiskFv.Equivalence.Srli
import ZiskFv.Equivalence.Srai
import ZiskFv.Equivalence.Shift
import ZiskFv.Equivalence.ShiftR
import ZiskFv.Equivalence.ShiftRA
import ZiskFv.Equivalence.ShiftLI
import ZiskFv.Equivalence.ShiftRLI
import ZiskFv.Equivalence.ShiftRAI
import ZiskFv.Equivalence.MulHU
import ZiskFv.Equivalence.MulHSU
import ZiskFv.Equivalence.MulW
-- Phase 3C T-RT — ALU RTYPE opcodes (SUB, AND, OR, XOR, SLT, SLTU)
import ZiskFv.Equivalence.And
import ZiskFv.Equivalence.Or
import ZiskFv.Equivalence.Slt
import ZiskFv.Equivalence.Sltu
import ZiskFv.Equivalence.Sub
import ZiskFv.Equivalence.Xor
-- Phase 3C T-IT — ALU ITYPE opcodes (ADDI, ANDI, ORI, XORI, SLTI, SLTIU)
import ZiskFv.Equivalence.Addi
import ZiskFv.Equivalence.Andi
import ZiskFv.Equivalence.Ori
import ZiskFv.Equivalence.Xori
import ZiskFv.Equivalence.Slti
import ZiskFv.Equivalence.Sltiu
-- Phase 3C T-W — RTYPEW + ADDIW (ADDW, SUBW, ADDIW)
import ZiskFv.Equivalence.Addw
import ZiskFv.Equivalence.Subw
import ZiskFv.Equivalence.Addiw
-- Phase 3C T-SL — signed loads (LW, LH, LB)
import ZiskFv.Equivalence.Lw
import ZiskFv.Equivalence.Lh
import ZiskFv.Equivalence.Lb
-- Track N K4 — Signed-case PackedBitVec + MulFieldSigned + DivFieldSigned
import ZiskFv.Fundamentals.PackedBitVec.Signed
import ZiskFv.Spec.MulFieldSigned
import ZiskFv.Spec.DivFieldSigned
-- Phase 3C T-D — DIV/REM
import ZiskFv.Equivalence.Div
import ZiskFv.Equivalence.Divu
import ZiskFv.Equivalence.Rem
import ZiskFv.Equivalence.Remu
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

