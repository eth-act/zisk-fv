import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.TranspileConsumers
import ZiskFv.Extraction.ArithTable
import ZiskFv.Airs.Arith.ArithTable
import ZiskFv.Airs.Arith.ArithRangeTable
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.GoldilocksBridge
import ZiskFv.Sail.BusEffect
import Extraction.BinaryAdd
import Extraction.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import Extraction.Buses
import ZiskFv.Extraction.OperationBuses
import ZiskFv.Airs.BusShape
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Extraction.MemoryBuses
import ZiskFv.Airs.MemoryBus.Projection
import ZiskFv.Airs.MemoryBus.BusShape
import ZiskFv.Airs.MemoryBus.LaneMatch
import Extraction.Mem
import ZiskFv.Airs.Mem
import Extraction.MemAlign
import Extraction.MemAlignByte
import Extraction.MemAlignReadByte
import Extraction.MemAlignWriteByte
import ZiskFv.Airs.MemAlign
import ZiskFv.Airs.MemAlignByte
import ZiskFv.Airs.MemAlignReadByte
import ZiskFv.Airs.MemAlignWriteByte
-- FGL → BitVec 64 arithmetic-extension lifts (h_rd_val bridges).
import ZiskFv.Fundamentals.PackedBitVec.Extensions
-- Goldilocks no-wrap toolkit (additive packings).
import ZiskFv.Fundamentals.PackedBitVec.NoWrap
-- Multiplicative no-wrap toolkit (8-chunk carry chains).
import ZiskFv.Fundamentals.PackedBitVec.MulNoWrap
-- Signed BitVec.toInt extension (sign-witness pattern + INT_MIN/-1 overflow).
import ZiskFv.Fundamentals.PackedBitVec.SignedNoWrap
-- Wide-PC no-wrap toolkit (PC values can exceed GL_prime).
import ZiskFv.Fundamentals.PackedBitVec.WidePCNoWrap
import ZiskFv.Circuit.Add
import ZiskFv.Equivalence.Add
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
-- ALU RTYPE opcodes (SUB, AND, OR, XOR, SLT, SLTU)
import ZiskFv.Equivalence.And
import ZiskFv.Equivalence.Or
import ZiskFv.Equivalence.Slt
import ZiskFv.Equivalence.Sltu
import ZiskFv.Equivalence.Sub
import ZiskFv.Equivalence.Xor
-- ALU ITYPE opcodes (ADDI, ANDI, ORI, XORI, SLTI, SLTIU)
import ZiskFv.Equivalence.Addi
import ZiskFv.Equivalence.Andi
import ZiskFv.Equivalence.Ori
import ZiskFv.Equivalence.Xori
import ZiskFv.Equivalence.Slti
import ZiskFv.Equivalence.Sltiu
-- RTYPEW + ADDIW (ADDW, SUBW, ADDIW)
import ZiskFv.Equivalence.Addw
import ZiskFv.Equivalence.Subw
import ZiskFv.Equivalence.Addiw
-- Signed loads (LW, LH, LB)
import ZiskFv.Equivalence.Lw
import ZiskFv.Equivalence.Lh
import ZiskFv.Equivalence.Lb
-- Signed-case PackedBitVec + MulFieldSigned + DivFieldSigned
import ZiskFv.Fundamentals.PackedBitVec.Signed
import ZiskFv.Circuit.MulFieldSigned
import ZiskFv.Circuit.DivFieldSigned
-- DIV/REM
import ZiskFv.Equivalence.Div
import ZiskFv.Equivalence.Divu
import ZiskFv.Equivalence.Rem
import ZiskFv.Equivalence.Remu
-- Sail-side pure-spec files not pulled in transitively by any Equivalence
-- module above; imported here so regressions surface at build time.
import ZiskFv.Sail.Auxiliaries
import ZiskFv.Sail.addi
import ZiskFv.Sail.addiw
import ZiskFv.Sail.addw
import ZiskFv.Sail.andi
import ZiskFv.Sail.div
import ZiskFv.Sail.divu
import ZiskFv.Sail.lb
import ZiskFv.Sail.lh
import ZiskFv.Sail.lw
import ZiskFv.Sail.ori
import ZiskFv.Sail.rem
import ZiskFv.Sail.remu
import ZiskFv.Sail.slt
import ZiskFv.Sail.slti
import ZiskFv.Sail.sltiu
import ZiskFv.Sail.sltu
import ZiskFv.Sail.subw
import ZiskFv.Sail.xori

-- Per-shape h_rd_val derivation lemmas.
import ZiskFv.Equivalence.RdValDerivation.Arith
import ZiskFv.Equivalence.RdValDerivation.JumpUType
import ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned
import ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned

