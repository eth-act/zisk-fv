import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Field.GoldilocksBridge
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus

import ZiskFv.Airs.BusShape
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.Mem
import ZiskFv.ZiskCircuit.MemTimeline.Ordering
import ZiskFv.Airs.MemAlign
import ZiskFv.Airs.MemAlignByte
import ZiskFv.Airs.MemAlignReadByte
-- FGL → BitVec 64 arithmetic-extension lifts (h_rd_val bridges).
import ZiskFv.Bits.PackedBitVec.Extensions
-- Goldilocks no-wrap toolkit (additive packings).
import ZiskFv.Bits.PackedBitVec.NoWrap
-- Multiplicative no-wrap toolkit (8-chunk carry chains).
import ZiskFv.Bits.PackedBitVec.MulNoWrap
-- Signed BitVec.toInt extension (sign-witness pattern + INT_MIN/-1 overflow).
import ZiskFv.Bits.PackedBitVec.SignedNoWrap
-- Wide-PC no-wrap toolkit (PC values can exceed GL_prime).
import ZiskFv.Bits.PackedBitVec.WidePCNoWrap
import ZiskFv.ZiskCircuit.Add
import ZiskFv.Equivalence.Add
import ZiskFv.Equivalence.Beq
import ZiskFv.Equivalence.Bne
import ZiskFv.Equivalence.Jal
import ZiskFv.Equivalence.Jalr
import ZiskFv.Equivalence.Ld
import ZiskFv.Equivalence.Lwu
import ZiskFv.Equivalence.Mul
import ZiskFv.Equivalence.MulH
import ZiskFv.Equivalence.Sd
import ZiskFv.Equivalence.Sw
import ZiskFv.Equivalence.Auipc
import ZiskFv.Equivalence.Fence
import ZiskFv.Equivalence.Divuw
import ZiskFv.Equivalence.Remuw
import ZiskFv.Equivalence.Divw
import ZiskFv.Equivalence.Remw
import ZiskFv.Equivalence.Blt
import ZiskFv.Equivalence.Bge
import ZiskFv.Equivalence.Bltu
import ZiskFv.Equivalence.Bgeu
import ZiskFv.Equivalence.Sh
import ZiskFv.Equivalence.Sb
import ZiskFv.Equivalence.Lhu
import ZiskFv.Equivalence.Lbu
import ZiskFv.Equivalence.Lui
import ZiskFv.Equivalence.Sll
import ZiskFv.Equivalence.Srl
import ZiskFv.Equivalence.Sra
import ZiskFv.Equivalence.Slli
import ZiskFv.Equivalence.Srli
import ZiskFv.Equivalence.Srai
import ZiskFv.Equivalence.Sllw
import ZiskFv.Equivalence.Srlw
import ZiskFv.Equivalence.Sraw
import ZiskFv.Equivalence.Slliw
import ZiskFv.Equivalence.Srliw
import ZiskFv.Equivalence.Sraiw
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
-- Signed-case PackedBitVec
import ZiskFv.Bits.PackedBitVec.Signed
-- DIV/REM
import ZiskFv.Equivalence.Div
import ZiskFv.Equivalence.Divu
import ZiskFv.Equivalence.Rem
import ZiskFv.Equivalence.Remu
-- Sail-side pure-spec files not pulled in transitively by any Equivalence
-- module above; imported here so regressions surface at build time.
import ZiskFv.SailSpec.Auxiliaries
import ZiskFv.SailSpec.addi
import ZiskFv.SailSpec.addiw
import ZiskFv.SailSpec.addw
import ZiskFv.SailSpec.andi
import ZiskFv.SailSpec.div
import ZiskFv.SailSpec.divu
import ZiskFv.SailSpec.lb
import ZiskFv.SailSpec.lh
import ZiskFv.SailSpec.lw
import ZiskFv.SailSpec.ori
import ZiskFv.SailSpec.rem
import ZiskFv.SailSpec.remu
import ZiskFv.SailSpec.slt
import ZiskFv.SailSpec.slti
import ZiskFv.SailSpec.sltiu
import ZiskFv.SailSpec.sltu
import ZiskFv.SailSpec.subw
import ZiskFv.SailSpec.xori

-- Per-shape h_rd_val derivation lemmas.
import ZiskFv.EquivCore.WriteValueProofs.Arith
import ZiskFv.EquivCore.WriteValueProofs.JumpUType
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned
import ZiskFv.EquivCore.WriteValueProofs.MulDivRemSigned
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.ZiskCircuit.MemTimeline.Construction
import ZiskFv.ZiskCircuit.MemTimeline.Linkage
import ZiskFv.ZiskCircuit.MemTimeline.Spike
import ZiskFv.Compliance.RowProvenance
import ZiskFv.Compliance.AcceptedZiskTrace
import ZiskFv.Compliance.AcceptedZiskTrace.Spec
import ZiskFv.Compliance.SailTrace
import ZiskFv.Compliance.OpBusProviderMatch
import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.ConstructionAnd
import ZiskFv.Compliance.ConstructionLogic
import ZiskFv.Compliance.ConstructionCompare
import ZiskFv.Compliance.ConstructionIType
import ZiskFv.Compliance.ConstructionShift
import ZiskFv.Compliance.ConstructionAdd
import ZiskFv.Compliance.ConstructionWAlu
import ZiskFv.Compliance.ConstructionLui
import ZiskFv.Compliance.ConstructionAuipc
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.Compliance.ConstructionDivu
import ZiskFv.Compliance.ConstructionDivuw
import ZiskFv.Compliance.ConstructionRemu
import ZiskFv.Compliance.ConstructionRemuw
import ZiskFv.Compliance.ConstructionStore
import ZiskFv.Compliance.ConstructionLoad
import ZiskFv.Compliance.ConstructionBranch
import ZiskFv.Compliance.ConstructionJump
import ZiskFv.Compliance.TraceLevelExport
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBindingOps
import ZiskFv.Compliance.TraceLevelExport.ProgramDecode
import ZiskFv.Compliance
import ZiskFv.Compliance.EnsembleWitnessBuilder
-- In-build per-opcode static decode/row-mode pin discharge from the real
-- Aeneas-extracted ZisK lowerer (eth-act/zisk-fv#111). Standalone; not yet
-- wired into root_soundness. Per-theorem collectAxioms keeps the aeneas runtime
-- sorries out of every canonical equiv_<OP>/root_soundness closure.
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction
-- eth-act/zisk-fv#162: the raw-word→opcode decoder acceptance theorem
-- (`zisk_decoder_accepts_supported_shape`) + completeness-obligation discharge
-- (`real_decoder_accepts_in_shape`), proven in-build off the real Aeneas decoder.
import ZiskFv.Compliance.AeneasBridgeTrust.Decode
import ZiskFv.Soundness
import ZiskFv.Completeness.Rv
-- Quarantined aspirational route; kept here so it stays built/verified, but the
-- live endpoints in `ZiskFv.Completeness` do not depend on it.
-- See `ZiskFv/Completeness/Aspirational/README.md`.
import ZiskFv.Completeness.Aspirational
import ZiskFv.Completeness.Rv64im.SailDecode
import ZiskFv.Completeness.Rv64im.SailDecode.ZiskClassifyMatch
import ZiskFv.Completeness
