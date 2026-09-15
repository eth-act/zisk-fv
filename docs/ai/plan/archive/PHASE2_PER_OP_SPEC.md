# Phase 2 spec — per-opcode static decode/row-mode pins (63 RV64IM ops)

Source: catalog agent over RowProvenance.lean (RowMode structs + ExtractedConst),
AeneasBridgeTrust/Base.lean (per-arm conjuncts), ProductionM2.lean (lowering entry points).

## Static pins per family (op / isExternalOp / m32 / setPc / storePc)

- **ControlAndUType**: LUI(opCopyB,F,F,F,F) · AUIPC(opFlag,F,F,F,T) · JAL(opFlag,F,F,F,T) ·
  JALR(opAnd,T,F,T,T) · FENCE(opFlag,F,—,—,—).
- **Branches** (all isExt=T, m32=F, setPc=F, storePc=F): BEQ/BNE→opEq(9) · BLT/BGE→opLt(7) ·
  BLTU/BGEU→opLtu(6). Value pin: jmp_offset1/2 = 4 (Phase 3).
- **BinaryRType / ImmediateAlu** (isExt=T, setPc=F, storePc=F): ADD/ADDI→opAdd(10) · SUB→opSub(11) ·
  AND/ANDI→opAnd(14) · OR/ORI→opOr(15) · XOR/XORI→opXor(16) · SLT/SLTI→opLt(7) · SLTU/SLTIU→opLtu(6) ·
  ADDW/ADDIW→opAddW(26) · SUBW→opSubW(27). m32 varies per provider route.
- **Shifts** (isExt=T, setPc=F, storePc=F): SLL/SLLI→opSll(33) · SRL/SRLI→opSrl(34) · SRA/SRAI→opSra(35) ·
  SLLW/SLLIW→opSllW(36) · SRLW/SRLIW→opSrlW(37) · SRAW/SRAIW→opSraW(38).
- **Mul** (isExt=T, setPc=F, storePc=F, jmp=4): MUL→opMul(180) · MULH→opMulH(181) · MULHU→opMulUH(177) ·
  MULHSU→opMulSUH(179) · MULW→opMulW(182, m32=1).
- **DivRem** (isExt=T, setPc=F, storePc=F, jmp=4): DIV→opDiv(186) · DIVU→opDivU(184) · REM→opRem(187) ·
  REMU→opRemU(185) · DIVW→opDivW(190,m32=1) · DIVUW→opDivUW(188,m32=1) · REMW→opRemW(191,m32=1) ·
  REMUW→opRemUW(189,m32=1).
- **Loads** (setPc=F, storePc=F): LD/LBU/LHU/LWU→opCopyB(1),isExt=F · LB→opSignextendB(39),isExt=T ·
  LH→opSignextendH(40),isExt=T · LW→opSignextendW(41),isExt=T. Value pin: ind_width 1/2/4/8 (Phase 3).
- **Stores** (opCopyB(1), isExt=F, setPc=F, storePc=F): SB/SH/SW/SD. Value pins: ind_width, store (Phase 3).

## ProductionM2 lowering entry points (~9 distinct, big dedup)
`Riscv2ZiskContext.{lui(2417,CopyB), jalr(2354,And), jal(2205,Flag), auipc(2442,Flag), copyb}` +
typed builders `create_branch_op_typed`, `create_register_op_typed`, `create_precompiled_op_typed`,
`immediate_op_typed`. Each calls `op_zisk … ZiskOp.<X>`; `ZiskOp.code .X` is a numeric literal.

## Op-code lemmas needed (~33, all `rfl`)
`(ZiskOp.code .X).toNat = ExtractedConst.opX` for X ∈ {Flag0, CopyB1, Ltu6, Lt7, Eq9, Add10, Sub11,
And14, Or15, Xor16, AddW26, SubW27, Sll33, Srl34, Sra35, SllW36, SrlW37, SraW38, SignextendB39,
SignextendH40, SignextendW41, MulUH177, MulSUH179, Mul180, MulH181, MulW182, DivU184, RemU185, Div186,
Rem187, DivUW188, RemUW189, DivW190, RemW191}.

## Phase 3 (deferred) value pins
Loads/Stores: ind_width (+ store selector). Branches/Jumps: jmp_offset1/2. These need the
numBits 32/64 split + const-mirror recipe. Out of Phase 2 scope.

## Gaps
None — every op has a RowMode struct / aeneasBridgeTrust arm + ExtractedConst + lowering entry.
