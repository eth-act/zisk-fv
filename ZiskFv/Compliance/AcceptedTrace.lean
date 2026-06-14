import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.Compliance.AeneasBridgeTrust
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.EquivCore.Bridge.BinaryExtension
import ZiskFv.EquivCore.Promises.BranchHelpers
import ZiskFv.EquivCore.Promises.Fence
import ZiskFv.EquivCore.Promises.IType
import ZiskFv.EquivCore.Promises.Jump
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.UType

/-!
# Accepted trace construction spine

P4 starts replacing caller-supplied `OpEnvelope` packages with envelopes
constructed from an accepted full-ensemble trace plus one named program-binding
premise. This PR1 module introduces the input record and the first construction
template, for BEQ.

`ProgramBinding` is intentionally the only bucket-(b) premise here. It carries
the Sail/decode row facts that P4 does not prove from circuit constraints. The
BEQ constructor below still packages the branch operands and promise bundle
locally from those binding projections.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.AirsClean.FullEnsemble

/-- Accepted committed trace for the full RV64IM Clean ensemble. -/
structure AcceptedTrace where
  length : Nat
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program length
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble
  constraints : witness.Constraints
  spec : witness.Spec
  balanced : witness.BalancedChannels

/-- Opcode-family selector exposed by the program binding. PR1 only consumes
    `beq`; later P4 PRs extend the construction dispatcher over all tags. -/
inductive ArmTag where
  | beq
  | bne
  | blt
  | bge
  | bltu
  | bgeu
  | and
  | or
  | xor
  | slt
  | sltu
  | andi
  | ori
  | xori
  | slti
  | sltiu
  | addw
  | subw
  | addiw
  | sll
  | srl
  | sra
  | sllw
  | fence
  | auipc_x0
  | jal_x0
  | other
deriving DecidableEq, Repr

/-- BEQ-specific projection of the named `ProgramBinding` premise.

The fields are the raw Sail/decode/provenance facts. `ops` and `promises` below
package these facts into the existing compliance API without adding a second
caller-facing premise. -/
structure BeqRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.BeqInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misaVal : RegisterType Register.misa
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opEq
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_set_pc : provenance.extractedRow.setPc = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4
  h_input_imm : input.imm = imm
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_input_misa : state.regs.get? Register.misa = .some misaVal
  h_misa_c : Sail.BitVec.extractLsb misaVal 2 2 = 0#1
  h_target_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_BEQ_pure input).nextPC

namespace BeqRowBinding

/-- Branch operand bundle constructed from the named binding projection. -/
@[reducible]
def ops {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BeqRowBinding main r_main state) : BranchInstrOperands where
  imm := b.imm
  r1 := b.r1
  r2 := b.r2
  misa_val := b.misaVal
  exec_row := b.execRow

/-- Branch promise bundle constructed from the named binding projection. -/
@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BeqRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.BranchPromises
      state b.input.imm b.input.r1_val b.input.r2_val b.input.PC
      (b.ops).misa_val
      (PureSpec.execute_BEQ_pure b.input).nextPC
      (PureSpec.execute_BEQ_pure b.input).throws
      (PureSpec.execute_BEQ_pure b.input).success
      (b.ops).imm (b.ops).r1 (b.ops).r2 (b.ops).exec_row :=
  ZiskFv.EquivCore.Promises.BranchPromises.of_aligned_BEQ
    b.input
    b.h_input_imm
    b.h_input_r1
    b.h_input_r2
    b.h_input_pc
    b.h_input_misa
    b.h_misa_c
    b.h_target_aligned
    b.h_exec_len
    b.h_e0_mult
    b.h_e1_mult
    b.h_nextPC_matches

end BeqRowBinding

/-- BNE-specific projection of the named `ProgramBinding` premise. -/
structure BneRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.BneInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misaVal : RegisterType Register.misa
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opEq
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_set_pc : provenance.extractedRow.setPc = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4
  h_input_imm : input.imm = imm
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_input_misa : state.regs.get? Register.misa = .some misaVal
  h_misa_c : Sail.BitVec.extractLsb misaVal 2 2 = 0#1
  h_target_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_BNE_pure input).nextPC

namespace BneRowBinding

@[reducible]
def ops {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BneRowBinding main r_main state) : BranchInstrOperands where
  imm := b.imm
  r1 := b.r1
  r2 := b.r2
  misa_val := b.misaVal
  exec_row := b.execRow

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BneRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.BranchPromises
      state b.input.imm b.input.r1_val b.input.r2_val b.input.PC
      (b.ops).misa_val
      (PureSpec.execute_BNE_pure b.input).nextPC
      (PureSpec.execute_BNE_pure b.input).throws
      (PureSpec.execute_BNE_pure b.input).success
      (b.ops).imm (b.ops).r1 (b.ops).r2 (b.ops).exec_row :=
  ZiskFv.EquivCore.Promises.BranchPromises.of_aligned_BNE
    b.input b.h_input_imm b.h_input_r1 b.h_input_r2 b.h_input_pc
    b.h_input_misa b.h_misa_c b.h_target_aligned b.h_exec_len
    b.h_e0_mult b.h_e1_mult b.h_nextPC_matches

end BneRowBinding

/-- BLT-specific projection of the named `ProgramBinding` premise. -/
structure BltRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.BltInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misaVal : RegisterType Register.misa
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opLt
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_set_pc : provenance.extractedRow.setPc = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4
  h_input_imm : input.imm = imm
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_input_misa : state.regs.get? Register.misa = .some misaVal
  h_misa_c : Sail.BitVec.extractLsb misaVal 2 2 = 0#1
  h_target_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_BLT_pure input).nextPC

namespace BltRowBinding

@[reducible]
def ops {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BltRowBinding main r_main state) : BranchInstrOperands where
  imm := b.imm
  r1 := b.r1
  r2 := b.r2
  misa_val := b.misaVal
  exec_row := b.execRow

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BltRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.BranchPromises
      state b.input.imm b.input.r1_val b.input.r2_val b.input.PC
      (b.ops).misa_val
      (PureSpec.execute_BLT_pure b.input).nextPC
      (PureSpec.execute_BLT_pure b.input).throws
      (PureSpec.execute_BLT_pure b.input).success
      (b.ops).imm (b.ops).r1 (b.ops).r2 (b.ops).exec_row :=
  ZiskFv.EquivCore.Promises.BranchPromises.of_aligned_BLT
    b.input b.h_input_imm b.h_input_r1 b.h_input_r2 b.h_input_pc
    b.h_input_misa b.h_misa_c b.h_target_aligned b.h_exec_len
    b.h_e0_mult b.h_e1_mult b.h_nextPC_matches

end BltRowBinding

/-- BGE-specific projection of the named `ProgramBinding` premise. -/
structure BgeRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.BgeInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misaVal : RegisterType Register.misa
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opLt
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_set_pc : provenance.extractedRow.setPc = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4
  h_input_imm : input.imm = imm
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_input_misa : state.regs.get? Register.misa = .some misaVal
  h_misa_c : Sail.BitVec.extractLsb misaVal 2 2 = 0#1
  h_target_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_BGE_pure input).nextPC

namespace BgeRowBinding

@[reducible]
def ops {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BgeRowBinding main r_main state) : BranchInstrOperands where
  imm := b.imm
  r1 := b.r1
  r2 := b.r2
  misa_val := b.misaVal
  exec_row := b.execRow

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BgeRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.BranchPromises
      state b.input.imm b.input.r1_val b.input.r2_val b.input.PC
      (b.ops).misa_val
      (PureSpec.execute_BGE_pure b.input).nextPC
      (PureSpec.execute_BGE_pure b.input).throws
      (PureSpec.execute_BGE_pure b.input).success
      (b.ops).imm (b.ops).r1 (b.ops).r2 (b.ops).exec_row :=
  ZiskFv.EquivCore.Promises.BranchPromises.of_aligned_BGE
    b.input b.h_input_imm b.h_input_r1 b.h_input_r2 b.h_input_pc
    b.h_input_misa b.h_misa_c b.h_target_aligned b.h_exec_len
    b.h_e0_mult b.h_e1_mult b.h_nextPC_matches

end BgeRowBinding

/-- BLTU-specific projection of the named `ProgramBinding` premise. -/
structure BltuRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.BltuInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misaVal : RegisterType Register.misa
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opLtu
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_set_pc : provenance.extractedRow.setPc = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4
  h_input_imm : input.imm = imm
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_input_misa : state.regs.get? Register.misa = .some misaVal
  h_misa_c : Sail.BitVec.extractLsb misaVal 2 2 = 0#1
  h_target_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_BLTU_pure input).nextPC

namespace BltuRowBinding

@[reducible]
def ops {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BltuRowBinding main r_main state) : BranchInstrOperands where
  imm := b.imm
  r1 := b.r1
  r2 := b.r2
  misa_val := b.misaVal
  exec_row := b.execRow

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BltuRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.BranchPromises
      state b.input.imm b.input.r1_val b.input.r2_val b.input.PC
      (b.ops).misa_val
      (PureSpec.execute_BLTU_pure b.input).nextPC
      (PureSpec.execute_BLTU_pure b.input).throws
      (PureSpec.execute_BLTU_pure b.input).success
      (b.ops).imm (b.ops).r1 (b.ops).r2 (b.ops).exec_row :=
  ZiskFv.EquivCore.Promises.BranchPromises.of_aligned_BLTU
    b.input b.h_input_imm b.h_input_r1 b.h_input_r2 b.h_input_pc
    b.h_input_misa b.h_misa_c b.h_target_aligned b.h_exec_len
    b.h_e0_mult b.h_e1_mult b.h_nextPC_matches

end BltuRowBinding

/-- BGEU-specific projection of the named `ProgramBinding` premise. -/
structure BgeuRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.BgeuInput
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misaVal : RegisterType Register.misa
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opLtu
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_set_pc : provenance.extractedRow.setPc = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4
  h_input_imm : input.imm = imm
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_input_misa : state.regs.get? Register.misa = .some misaVal
  h_misa_c : Sail.BitVec.extractLsb misaVal 2 2 = 0#1
  h_target_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_BGEU_pure input).nextPC

namespace BgeuRowBinding

@[reducible]
def ops {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BgeuRowBinding main r_main state) : BranchInstrOperands where
  imm := b.imm
  r1 := b.r1
  r2 := b.r2
  misa_val := b.misaVal
  exec_row := b.execRow

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : BgeuRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.BranchPromises
      state b.input.imm b.input.r1_val b.input.r2_val b.input.PC
      (b.ops).misa_val
      (PureSpec.execute_BGEU_pure b.input).nextPC
      (PureSpec.execute_BGEU_pure b.input).throws
      (PureSpec.execute_BGEU_pure b.input).success
      (b.ops).imm (b.ops).r1 (b.ops).r2 (b.ops).exec_row :=
  ZiskFv.EquivCore.Promises.BranchPromises.of_aligned_BGEU
    b.input b.h_input_imm b.h_input_r1 b.h_input_r2 b.h_input_pc
    b.h_input_misa b.h_misa_c b.h_target_aligned b.h_exec_len
    b.h_e0_mult b.h_e1_mult b.h_nextPC_matches

end BgeuRowBinding

/-- XOR-specific projection of the named `ProgramBinding` premise.

The binding supplies Sail/decode/provenance facts. The namespace below derives
Main's register memory-bus rows and the shared R-type promise bundle from those
facts, instead of accepting those bucket-(a) rows as a caller-supplied envelope
payload. -/
structure XorRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.XorInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opXor
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_xor_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace XorRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XorRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XorRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XorRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XorRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem byteMatchesXor
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XorRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_row_spec : ZiskFv.AirsClean.Binary.Spec row)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_XOR := by
  have h_main_op_xor :
      main.op r_main = ZiskFv.Trusted.OP_XOR :=
    (MainRowProvenance.xorPins_of_extracted_shape
      b.provenance b.h_op b.h_external).main_op
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_XOR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        main.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_XOR, ZiskFv.Trusted.OP_XOR] using
      h_main_op_xor
  obtain ⟨_, h_b_op, h_b_op_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      row h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_XOR
      (.inr (.inr rfl)) h_emit
  exact
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      row (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static)
      ZiskFv.Airs.Tables.BinaryTable.OP_XOR h_b_op h_b_op_or_sext

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XorRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_XOR)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      main row r_main (regidx_to_fin b.r1) b.input.r1_val
      h_matches b.m32Zero b.h_a_lo_t b.h_a_hi_t h_match b.h_input_r1

theorem inputR2Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XorRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_XOR)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
      main row r_main (regidx_to_fin b.r2) b.input.r2_val
      h_matches b.m32Zero b.h_b_lo_t b.h_b_hi_t h_match b.h_input_r2

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XorRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.RTypePromises
      state b.input.r1_val b.input.r2_val b.input.rd b.input.PC
      (PureSpec.execute_RTYPE_xor_pure b.input).nextPC
      b.r1 b.r2 b.rd (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_r2_eq := b.h_input_r2
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end XorRowBinding

/-- AND-specific projection of the named `ProgramBinding` premise. -/
structure AndRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.AndInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opAnd
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_and_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace AndRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem byteMatchesAnd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_row_spec : ZiskFv.AirsClean.Binary.Spec row)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_AND := by
  have h_main_op_and :
      main.op r_main = ZiskFv.Trusted.OP_AND :=
    (MainRowProvenance.andPins_of_extracted_shape
      b.provenance b.h_op b.h_external).main_op
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_AND : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        main.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND, ZiskFv.Trusted.OP_AND] using
      h_main_op_and
  obtain ⟨_, h_b_op, h_b_op_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      row h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_AND
      (.inl rfl) h_emit
  exact
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      row (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static)
      ZiskFv.Airs.Tables.BinaryTable.OP_AND h_b_op h_b_op_or_sext

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_AND)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      main row r_main (regidx_to_fin b.r1) b.input.r1_val
      h_matches b.m32Zero b.h_a_lo_t b.h_a_hi_t h_match b.h_input_r1

theorem inputR2Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_AND)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
      main row r_main (regidx_to_fin b.r2) b.input.r2_val
      h_matches b.m32Zero b.h_b_lo_t b.h_b_hi_t h_match b.h_input_r2

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.RTypePromises
      state b.input.r1_val b.input.r2_val b.input.rd b.input.PC
      (PureSpec.execute_RTYPE_and_pure b.input).nextPC
      b.r1 b.r2 b.rd (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_r2_eq := b.h_input_r2
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end AndRowBinding

/-- OR-specific projection of the named `ProgramBinding` premise. -/
structure OrRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.OrInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opOr
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_or_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace OrRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OrRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OrRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OrRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OrRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem byteMatchesOr
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OrRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_row_spec : ZiskFv.AirsClean.Binary.Spec row)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_OR := by
  have h_main_op_or :
      main.op r_main = ZiskFv.Trusted.OP_OR :=
    (MainRowProvenance.orPins_of_extracted_shape
      b.provenance b.h_op b.h_external).main_op
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_OR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        main.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_OR, ZiskFv.Trusted.OP_OR] using
      h_main_op_or
  obtain ⟨_, h_b_op, h_b_op_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      row h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_OR
      (.inr (.inl rfl)) h_emit
  exact
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      row (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static)
      ZiskFv.Airs.Tables.BinaryTable.OP_OR h_b_op h_b_op_or_sext

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OrRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_OR)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      main row r_main (regidx_to_fin b.r1) b.input.r1_val
      h_matches b.m32Zero b.h_a_lo_t b.h_a_hi_t h_match b.h_input_r1

theorem inputR2Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OrRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_OR)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
      main row r_main (regidx_to_fin b.r2) b.input.r2_val
      h_matches b.m32Zero b.h_b_lo_t b.h_b_hi_t h_match b.h_input_r2

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OrRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.RTypePromises
      state b.input.r1_val b.input.r2_val b.input.rd b.input.PC
      (PureSpec.execute_RTYPE_or_pure b.input).nextPC
      b.r1 b.r2 b.rd (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_r2_eq := b.h_input_r2
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end OrRowBinding

private theorem consumerByteMatchOfChainWf
    {op : Nat} {a b c cin flags pos : FGL}
    (h : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op a b c cin flags pos) :
    ZiskFv.Airs.Binary.consumer_byte_match_wf op a b c := by
  rcases h with ⟨e, h_wf, h_op, h_a, h_b, h_c, _h_cin, _h_flags, _h_pos⟩
  exact ⟨e, h_wf, h_op, h_a, h_b, h_c⟩

private theorem allByteMatchesOfStaticOut64
    {row : ZiskFv.AirsClean.Binary.BinaryRow FGL} {op : Nat}
    (out : ZiskFv.EquivCore.Bridge.Binary.BinaryChainStaticOut64
      (ZiskFv.AirsClean.Binary.validOfRow row) 0 op) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row row op := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf out.chain_0
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf out.chain_1
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf out.chain_2
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf out.chain_3
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf out.chain_4
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf out.chain_5
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf out.chain_6
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf out.chain_7

/-- SLT-specific projection of the named `ProgramBinding` premise. -/
structure SltRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.SltInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opLt
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_slt_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace SltRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem byteMatchesSlt
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_LT := by
  have h_main_op_slt :
      main.op r_main = ZiskFv.Trusted.OP_LT :=
    (MainRowProvenance.ltPins_of_extracted_shape
      b.provenance b.h_op b.h_external).main_op
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        main.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
      h_main_op_slt
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      row h_static ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      row (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static)
      ZiskFv.Airs.Tables.BinaryTable.OP_LT h_core h_row_m32 h_bop
  exact allByteMatchesOfStaticOut64 h_out

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_LT)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      main row r_main (regidx_to_fin b.r1) b.input.r1_val
      h_matches b.m32Zero b.h_a_lo_t b.h_a_hi_t h_match b.h_input_r1

theorem inputR2Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_LT)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
      main row r_main (regidx_to_fin b.r2) b.input.r2_val
      h_matches b.m32Zero b.h_b_lo_t b.h_b_hi_t h_match b.h_input_r2

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.RTypePromises
      state b.input.r1_val b.input.r2_val b.input.rd b.input.PC
      (PureSpec.execute_RTYPE_slt_pure b.input).nextPC
      b.r1 b.r2 b.rd (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_r2_eq := b.h_input_r2
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end SltRowBinding

/-- SLTU-specific projection of the named `ProgramBinding` premise. -/
structure SltuRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.SltuInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opLtu
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sltu_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace SltuRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltuRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltuRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltuRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltuRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem byteMatchesSltu
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltuRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_LTU := by
  have h_main_op_sltu :
      main.op r_main = ZiskFv.Trusted.OP_LTU :=
    (MainRowProvenance.ltuPins_of_extracted_shape
      b.provenance b.h_op b.h_external).main_op
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        main.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU, ZiskFv.Trusted.OP_LTU] using
      h_main_op_sltu
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      row h_static ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      row (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static)
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_row_m32 h_bop
  exact allByteMatchesOfStaticOut64 h_out

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltuRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_LTU)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      main row r_main (regidx_to_fin b.r1) b.input.r1_val
      h_matches b.m32Zero b.h_a_lo_t b.h_a_hi_t h_match b.h_input_r1

theorem inputR2Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltuRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_LTU)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
      main row r_main (regidx_to_fin b.r2) b.input.r2_val
      h_matches b.m32Zero b.h_b_lo_t b.h_b_hi_t h_match b.h_input_r2

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltuRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.RTypePromises
      state b.input.r1_val b.input.r2_val b.input.rd b.input.PC
      (PureSpec.execute_RTYPE_sltu_pure b.input).nextPC
      b.r1 b.r2 b.rd (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_r2_eq := b.h_input_r2
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end SltuRowBinding

/-- ANDI-specific projection of the named `ProgramBinding` premise. -/
structure AndiRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.AndiInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opAnd
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_imm : input.imm = imm
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_ITYPE_andi_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr
  h_imm_subset :
    ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      main r_main input.imm

namespace AndiRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndiRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndiRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndiRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndiRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem byteMatchesAndi
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndiRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_row_spec : ZiskFv.AirsClean.Binary.Spec row)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_AND := by
  have h_main_op_and :
      main.op r_main = ZiskFv.Trusted.OP_AND :=
    (MainRowProvenance.andPins_of_extracted_shape
      b.provenance b.h_op b.h_external).main_op
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_AND : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        main.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND, ZiskFv.Trusted.OP_AND] using
      h_main_op_and
  obtain ⟨_, h_b_op, h_b_op_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      row h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_AND
      (.inl rfl) h_emit
  exact
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      row (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static)
      ZiskFv.Airs.Tables.BinaryTable.OP_AND h_b_op h_b_op_or_sext

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndiRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_AND)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      main row r_main (regidx_to_fin b.r1) b.input.r1_val
      h_matches b.m32Zero b.h_a_lo_t b.h_a_hi_t h_match b.h_input_r1

theorem inputImmRow
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndiRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_AND)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    BitVec.signExtend 64 b.input.imm = ZiskFv.EquivCore.Add.binaryRowB64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
    ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
      main row r_main b.input.imm h_matches b.m32Zero h_match b.h_imm_subset

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AndiRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.ITypePromises
      state b.input.r1_val b.input.imm b.input.rd b.input.PC
      (PureSpec.execute_ITYPE_andi_pure b.input).nextPC
      b.r1 b.rd b.imm (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_imm_eq := b.h_input_imm
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end AndiRowBinding

/-- ORI-specific projection of the named `ProgramBinding` premise. -/
structure OriRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.OriInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opOr
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_imm : input.imm = imm
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_ITYPE_ori_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr
  h_imm_subset :
    ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      main r_main input.imm

namespace OriRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OriRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OriRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OriRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OriRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem byteMatchesOri
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OriRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_row_spec : ZiskFv.AirsClean.Binary.Spec row)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_OR := by
  have h_main_op_or :
      main.op r_main = ZiskFv.Trusted.OP_OR :=
    (MainRowProvenance.orPins_of_extracted_shape
      b.provenance b.h_op b.h_external).main_op
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_OR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        main.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_OR, ZiskFv.Trusted.OP_OR] using
      h_main_op_or
  obtain ⟨_, h_b_op, h_b_op_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      row h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_OR
      (.inr (.inl rfl)) h_emit
  exact
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      row (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static)
      ZiskFv.Airs.Tables.BinaryTable.OP_OR h_b_op h_b_op_or_sext

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OriRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_OR)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      main row r_main (regidx_to_fin b.r1) b.input.r1_val
      h_matches b.m32Zero b.h_a_lo_t b.h_a_hi_t h_match b.h_input_r1

theorem inputImmRow
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OriRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_OR)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    BitVec.signExtend 64 b.input.imm = ZiskFv.EquivCore.Add.binaryRowB64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
    ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
      main row r_main b.input.imm h_matches b.m32Zero h_match b.h_imm_subset

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : OriRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.ITypePromises
      state b.input.r1_val b.input.imm b.input.rd b.input.PC
      (PureSpec.execute_ITYPE_ori_pure b.input).nextPC
      b.r1 b.rd b.imm (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_imm_eq := b.h_input_imm
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end OriRowBinding

/-- XORI-specific projection of the named `ProgramBinding` premise. -/
structure XoriRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.XoriInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opXor
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_imm : input.imm = imm
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_ITYPE_xori_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr
  h_imm_subset :
    ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      main r_main input.imm

namespace XoriRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XoriRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XoriRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XoriRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XoriRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem byteMatchesXori
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XoriRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_row_spec : ZiskFv.AirsClean.Binary.Spec row)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_XOR := by
  have h_main_op_xor :
      main.op r_main = ZiskFv.Trusted.OP_XOR :=
    (MainRowProvenance.xorPins_of_extracted_shape
      b.provenance b.h_op b.h_external).main_op
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_XOR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        main.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_XOR, ZiskFv.Trusted.OP_XOR] using
      h_main_op_xor
  obtain ⟨_, h_b_op, h_b_op_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      row h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_XOR
      (.inr (.inr rfl)) h_emit
  exact
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      row (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static)
      ZiskFv.Airs.Tables.BinaryTable.OP_XOR h_b_op h_b_op_or_sext

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XoriRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_XOR)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      main row r_main (regidx_to_fin b.r1) b.input.r1_val
      h_matches b.m32Zero b.h_a_lo_t b.h_a_hi_t h_match b.h_input_r1

theorem inputImmRow
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XoriRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_XOR)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    BitVec.signExtend 64 b.input.imm = ZiskFv.EquivCore.Add.binaryRowB64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
    ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
      main row r_main b.input.imm h_matches b.m32Zero h_match b.h_imm_subset

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : XoriRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.ITypePromises
      state b.input.r1_val b.input.imm b.input.rd b.input.PC
      (PureSpec.execute_ITYPE_xori_pure b.input).nextPC
      b.r1 b.rd b.imm (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_imm_eq := b.h_input_imm
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end XoriRowBinding

/-- SLTI-specific projection of the named `ProgramBinding` premise. -/
structure SltiRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.SltiInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opLt
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_imm : input.imm = imm
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_ITYPE_slti_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr
  h_imm_subset :
    ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      main r_main input.imm

namespace SltiRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem byteMatchesSlti
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_LT := by
  have h_main_op_slti :
      main.op r_main = ZiskFv.Trusted.OP_LT :=
    (MainRowProvenance.ltPins_of_extracted_shape
      b.provenance b.h_op b.h_external).main_op
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        main.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
      h_main_op_slti
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      row h_static ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      row (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static)
      ZiskFv.Airs.Tables.BinaryTable.OP_LT h_core h_row_m32 h_bop
  exact allByteMatchesOfStaticOut64 h_out

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_LT)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      main row r_main (regidx_to_fin b.r1) b.input.r1_val
      h_matches b.m32Zero b.h_a_lo_t b.h_a_hi_t h_match b.h_input_r1

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.ITypePromises
      state b.input.r1_val b.input.imm b.input.rd b.input.PC
      (PureSpec.execute_ITYPE_slti_pure b.input).nextPC
      b.r1 b.rd b.imm (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_imm_eq := b.h_input_imm
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end SltiRowBinding

/-- SLTIU-specific projection of the named `ProgramBinding` premise. -/
structure SltiuRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.SltiuInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opLtu
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_imm : input.imm = imm
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_ITYPE_sltiu_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr
  h_imm_subset :
    ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      main r_main input.imm

namespace SltiuRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiuRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiuRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiuRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiuRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem byteMatchesSltiu
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiuRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_LTU := by
  have h_main_op_sltiu :
      main.op r_main = ZiskFv.Trusted.OP_LTU :=
    (MainRowProvenance.ltuPins_of_extracted_shape
      b.provenance b.h_op b.h_external).main_op
  have h_emit :
      row.chain.b_op + 16 * row.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        main.op r_main = row.chain.b_op + 16 * row.mode.mode32 := h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU, ZiskFv.Trusted.OP_LTU] using
      h_main_op_sltiu
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      row h_static ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      row (ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts row h_static)
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_row_m32 h_bop
  exact allByteMatchesOfStaticOut64 h_out

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiuRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_matches : ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
      row ZiskFv.Airs.Tables.BinaryTable.OP_LTU)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row := by
  simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
    ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
      main row r_main (regidx_to_fin b.r1) b.input.r1_val
      h_matches b.m32Zero b.h_a_lo_t b.h_a_hi_t h_match b.h_input_r1

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SltiuRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.ITypePromises
      state b.input.r1_val b.input.imm b.input.rd b.input.PC
      (PureSpec.execute_ITYPE_sltiu_pure b.input).nextPC
      b.r1 b.rd b.imm (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_imm_eq := b.h_input_imm
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end SltiuRowBinding

private theorem binaryRowA32_lt_of_static_wf
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row) :
    ZiskFv.EquivCore.Addw.binaryRowA32 row < 2^32 := by
  have ha0 : row.aBytes.free_in_a_0.val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.1
  have ha1 : row.aBytes.free_in_a_1.val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.1
  have ha2 : row.aBytes.free_in_a_2.val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.1
  have ha3 : row.aBytes.free_in_a_3.val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.1
  simp [ZiskFv.EquivCore.Addw.binaryRowA32]
  omega

private theorem binaryRowB32_lt_of_static_wf
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row) :
    ZiskFv.EquivCore.Addw.binaryRowB32 row < 2^32 := by
  have hb0 : row.bBytes.free_in_b_0.val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.2.1
  have hb1 : row.bBytes.free_in_b_1.val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.2.1
  have hb2 : row.bBytes.free_in_b_2.val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.2.1
  have hb3 : row.bBytes.free_in_b_3.val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.2.1
  simp [ZiskFv.EquivCore.Addw.binaryRowB32]
  omega

private theorem inputR1ExtractA32Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r1 : regidx) (r1Val : BitVec 64)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_a_lo_t : main.a_0 r_main =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r1)))
    (h_a_hi_t : main.a_1 r_main =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r1)))
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) state = EStateM.Result.ok r1Val state) :
    (Sail.BitVec.extractLsb r1Val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ZiskFv.EquivCore.Addw.binaryRowA32 row % 2^32 := by
  have h_r1_main :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r1) r1Val (main.a_0 r_main) (main.a_1 r_main)
      h_a_lo_t h_a_hi_t h_input_r1
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_match_v :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_Binary v 0) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_Binary] using h_match
  have h_lane_eqs := h_match_v
  simp only [ZiskFv.Airs.OperationBus.matches_entry,
    ZiskFv.Airs.OperationBus.opBus_row_Main,
    ZiskFv.Airs.OperationBus.opBus_row_Binary] at h_lane_eqs
  obtain ⟨_, _, h_a_lo_m, _, _, _, _, _, _, _, _, _⟩ := h_lane_eqs
  have h_a0_fgl :
      main.a_0 r_main =
        row.aBytes.free_in_a_0 + 256 * row.aBytes.free_in_a_1
          + 65536 * row.aBytes.free_in_a_2
          + 16777216 * row.aBytes.free_in_a_3 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_a_lo_m
  have h_a0_val :
      (main.a_0 r_main).val = ZiskFv.EquivCore.Addw.binaryRowA32 row := by
    rw [h_a0_fgl]
    have h_cast :
        row.aBytes.free_in_a_0 + 256 * row.aBytes.free_in_a_1
          + 65536 * row.aBytes.free_in_a_2
          + 16777216 * row.aBytes.free_in_a_3
          = ((ZiskFv.EquivCore.Addw.binaryRowA32 row : ℕ) : FGL) := by
      simp [ZiskFv.EquivCore.Addw.binaryRowA32]
      ring
    rw [h_cast, Fin.val_natCast]
    exact Nat.mod_eq_of_lt (by
      have hlt := binaryRowA32_lt_of_static_wf row h_facts
      omega)
  rw [h_r1_main]
  have h_extract_eq :
      (Sail.BitVec.extractLsb
        (BitVec.ofNat 64
          ((main.a_0 r_main).val + (main.a_1 r_main).val * 4294967296)) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = ((main.a_0 r_main).val + (main.a_1 r_main).val * 4294967296) % 2^32 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_ofNat]
  rw [h_extract_eq, h_a0_val]
  omega

private theorem inputR2ExtractB32Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r2 : regidx) (r2Val : BitVec 64)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_b_lo_t : main.b_0 r_main =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r2)))
    (h_b_hi_t : main.b_1 r_main =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
          (regidx_to_fin r2)))
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) state = EStateM.Result.ok r2Val state) :
    (Sail.BitVec.extractLsb r2Val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ZiskFv.EquivCore.Addw.binaryRowB32 row % 2^32 := by
  have h_r2_main :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.packed_lane_eq_of_read_xreg
      state (regidx_to_fin r2) r2Val (main.b_0 r_main) (main.b_1 r_main)
      h_b_lo_t h_b_hi_t h_input_r2
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_match_v :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_Binary v 0) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_Binary] using h_match
  have h_lane_eqs := h_match_v
  simp only [ZiskFv.Airs.OperationBus.matches_entry,
    ZiskFv.Airs.OperationBus.opBus_row_Main,
    ZiskFv.Airs.OperationBus.opBus_row_Binary] at h_lane_eqs
  obtain ⟨_, _, _, _, h_b_lo_m, _, _, _, _, _, _, _⟩ := h_lane_eqs
  have h_b0_fgl :
      main.b_0 r_main =
        row.bBytes.free_in_b_0 + 256 * row.bBytes.free_in_b_1
          + 65536 * row.bBytes.free_in_b_2
          + 16777216 * row.bBytes.free_in_b_3 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_b_lo_m
  have h_b0_val :
      (main.b_0 r_main).val = ZiskFv.EquivCore.Addw.binaryRowB32 row := by
    rw [h_b0_fgl]
    have h_cast :
        row.bBytes.free_in_b_0 + 256 * row.bBytes.free_in_b_1
          + 65536 * row.bBytes.free_in_b_2
          + 16777216 * row.bBytes.free_in_b_3
          = ((ZiskFv.EquivCore.Addw.binaryRowB32 row : ℕ) : FGL) := by
      simp [ZiskFv.EquivCore.Addw.binaryRowB32]
      ring
    rw [h_cast, Fin.val_natCast]
    exact Nat.mod_eq_of_lt (by
      have hlt := binaryRowB32_lt_of_static_wf row h_facts
      omega)
  rw [h_r2_main]
  have h_extract_eq :
      (Sail.BitVec.extractLsb
        (BitVec.ofNat 64
          ((main.b_0 r_main).val + (main.b_1 r_main).val * 4294967296)) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = ((main.b_0 r_main).val + (main.b_1 r_main).val * 4294967296) % 2^32 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      BitVec.toNat_ofNat]
  rw [h_extract_eq, h_b0_val]
  omega

/-- ADDW-specific projection of the named `ProgramBinding` premise. -/
structure AddwRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.AddwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opAddW
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = true
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_addw_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace AddwRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddwRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddwRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddwRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem inputR1Extract
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddwRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    (Sail.BitVec.extractLsb b.input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ZiskFv.EquivCore.Addw.binaryRowA32 row % 2^32 :=
  inputR1ExtractA32Row row b.r1 b.input.r1_val h_facts b.h_a_lo_t b.h_a_hi_t
    h_match b.h_input_r1

theorem inputR2Extract
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddwRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    (Sail.BitVec.extractLsb b.input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ZiskFv.EquivCore.Addw.binaryRowB32 row % 2^32 :=
  inputR2ExtractB32Row row b.r2 b.input.r2_val h_facts b.h_b_lo_t b.h_b_hi_t
    h_match b.h_input_r2

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddwRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.RTypePromises
      state b.input.r1_val b.input.r2_val b.input.rd b.input.PC
      (PureSpec.execute_RTYPE_addw_pure b.input).nextPC
      b.r1 b.r2 b.rd (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_r2_eq := b.h_input_r2
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end AddwRowBinding

/-- SUBW-specific projection of the named `ProgramBinding` premise. -/
structure SubwRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.SubwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opSubW
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = true
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_subw_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace SubwRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SubwRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SubwRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SubwRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem inputR1Extract
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SubwRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    (Sail.BitVec.extractLsb b.input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ZiskFv.EquivCore.Addw.binaryRowA32 row % 2^32 :=
  inputR1ExtractA32Row row b.r1 b.input.r1_val h_facts b.h_a_lo_t b.h_a_hi_t
    h_match b.h_input_r1

theorem inputR2Extract
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SubwRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    (Sail.BitVec.extractLsb b.input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ZiskFv.EquivCore.Addw.binaryRowB32 row % 2^32 :=
  inputR2ExtractB32Row row b.r2 b.input.r2_val h_facts b.h_b_lo_t b.h_b_hi_t
    h_match b.h_input_r2

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SubwRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.RTypePromises
      state b.input.r1_val b.input.r2_val b.input.rd b.input.PC
      (PureSpec.execute_RTYPE_subw_pure b.input).nextPC
      b.r1 b.r2 b.rd (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_r2_eq := b.h_input_r2
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end SubwRowBinding

/-- ADDIW-specific projection of the named `ProgramBinding` premise. -/
structure AddiwRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.AddiwInput
  r1 : regidx
  rd : regidx
  imm : BitVec 12
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opAddW
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = true
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_imm : input.imm = imm
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_ITYPE_addiw_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr
  h_imm_subset :
    ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      main r_main input.imm

namespace AddiwRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddiwRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddiwRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddiwRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem inputR1Extract
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddiwRowBinding main r_main state)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    (Sail.BitVec.extractLsb b.input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
      = ZiskFv.EquivCore.Addw.binaryRowA32 row % 2^32 :=
  inputR1ExtractA32Row row b.r1 b.input.r1_val h_facts b.h_a_lo_t b.h_a_hi_t
    h_match b.h_input_r1

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AddiwRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.ITypePromises
      state b.input.r1_val b.input.imm b.input.rd b.input.PC
      (PureSpec.execute_ITYPE_addiw_pure b.input).nextPC
      b.r1 b.rd b.imm (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_imm_eq := b.h_input_imm
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end AddiwRowBinding

theorem binaryExtensionABytesInRangeOfWfs
    {v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL} {row : ℕ}
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v row)
    (h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes) :
    ZiskFv.Airs.BinaryExtension.a_bytes_in_range v row := by
  obtain ⟨_, h0, _, h1, _, h2, _, h3, _, h4, _, h5, _, h6, _, h7⟩ := h_bytes
  exact ⟨
    by simpa [h0.2.2.2.1] using h_wfs.1.1.1,
    by simpa [h1.2.2.2.1] using h_wfs.2.1.1.1,
    by simpa [h2.2.2.2.1] using h_wfs.2.2.1.1.1,
    by simpa [h3.2.2.2.1] using h_wfs.2.2.2.1.1.1,
    by simpa [h4.2.2.2.1] using h_wfs.2.2.2.2.1.1.1,
    by simpa [h5.2.2.2.1] using h_wfs.2.2.2.2.2.1.1.1,
    by simpa [h6.2.2.2.1] using h_wfs.2.2.2.2.2.2.1.1.1,
    by simpa [h7.2.2.2.1] using h_wfs.2.2.2.2.2.2.2.1.1 ⟩

/-- SLL-specific projection of the named `ProgramBinding` premise. -/
structure SllRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.SllInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opSll
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sll_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace SllRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllRowBinding main r_main state)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.AirsClean.BinaryExtension.rowA64 row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using
      h_facts
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main 0 h_match_v
  have h_op_v_eq : v.op 0 = ZiskFv.Trusted.OP_SLL := by
    have h_pins :=
      MainRowProvenance.sllPins_of_extracted_shape
        b.provenance b.h_op b.h_external
    rw [← h_op_fgl, h_pins.main_op]
  have h_op_is_shift : v.op_is_shift 0 = 1 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
      v 0 h_wfs).1 (Or.inl h_op_v_eq)
  have h_a_range :=
    binaryExtensionABytesInRangeOfWfs h_bytes h_wfs
  have h :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.packed_a_eq_of_shift_match_m32_0_of_a_range
      main v r_main 0 (regidx_to_fin b.r1) b.input.r1_val b.m32Zero
      b.h_a_lo_t b.h_a_hi_t b.h_input_r1 h_op_is_shift h_match_v h_a_range
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowA64,
    ZiskFv.AirsClean.BinaryExtension.validA64] using h

theorem shiftPinRow
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllRowBinding main r_main state)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_b0_range : ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact row) :
    b.input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using
      h_facts
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main 0 h_match_v
  have h_op_v_eq : v.op 0 = ZiskFv.Trusted.OP_SLL := by
    have h_pins :=
      MainRowProvenance.sllPins_of_extracted_shape
        b.provenance b.h_op b.h_external
    rw [← h_op_fgl, h_pins.main_op]
  have h_op_is_shift : v.op_is_shift 0 = 1 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
      v 0 h_wfs).1 (Or.inl h_op_v_eq)
  have h :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.shift_pin_eq_of_shift_match_m32_0_of_b0_range
      main v r_main 0 (regidx_to_fin b.r2) b.input.r2_val b.m32Zero
      b.h_b_lo_t b.h_b_hi_t b.h_input_r2 h_op_is_shift h_match_v h_bytes
      h_wfs (by simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
        ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact] using h_b0_range)
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowShiftAmount,
    ZiskFv.AirsClean.BinaryExtension.validShiftAmount] using h

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.RTypePromises
      state b.input.r1_val b.input.r2_val b.input.rd b.input.PC
      (PureSpec.execute_RTYPE_sll_pure b.input).nextPC
      b.r1 b.r2 b.rd (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_r2_eq := b.h_input_r2
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end SllRowBinding

/-- SRL-specific projection of the named `ProgramBinding` premise. -/
structure SrlRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.SrlInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opSrl
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_srl_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace SrlRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SrlRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SrlRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SrlRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SrlRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SrlRowBinding main r_main state)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.AirsClean.BinaryExtension.rowA64 row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using
      h_facts
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main 0 h_match_v
  have h_op_v_eq : v.op 0 = ZiskFv.Trusted.OP_SRL := by
    have h_pins :=
      MainRowProvenance.srlPins_of_extracted_shape
        b.provenance b.h_op b.h_external
    rw [← h_op_fgl, h_pins.main_op]
  have h_op_is_shift : v.op_is_shift 0 = 1 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
      v 0 h_wfs).1 (Or.inr (Or.inl h_op_v_eq))
  have h_a_range :=
    binaryExtensionABytesInRangeOfWfs h_bytes h_wfs
  have h :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.packed_a_eq_of_shift_match_m32_0_of_a_range
      main v r_main 0 (regidx_to_fin b.r1) b.input.r1_val b.m32Zero
      b.h_a_lo_t b.h_a_hi_t b.h_input_r1 h_op_is_shift h_match_v h_a_range
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowA64,
    ZiskFv.AirsClean.BinaryExtension.validA64] using h

theorem shiftPinRow
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SrlRowBinding main r_main state)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_b0_range : ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact row) :
    b.input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using
      h_facts
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main 0 h_match_v
  have h_op_v_eq : v.op 0 = ZiskFv.Trusted.OP_SRL := by
    have h_pins :=
      MainRowProvenance.srlPins_of_extracted_shape
        b.provenance b.h_op b.h_external
    rw [← h_op_fgl, h_pins.main_op]
  have h_op_is_shift : v.op_is_shift 0 = 1 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
      v 0 h_wfs).1 (Or.inr (Or.inl h_op_v_eq))
  have h :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.shift_pin_eq_of_shift_match_m32_0_of_b0_range
      main v r_main 0 (regidx_to_fin b.r2) b.input.r2_val b.m32Zero
      b.h_b_lo_t b.h_b_hi_t b.h_input_r2 h_op_is_shift h_match_v h_bytes
      h_wfs (by simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
        ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact] using h_b0_range)
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowShiftAmount,
    ZiskFv.AirsClean.BinaryExtension.validShiftAmount] using h

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SrlRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.RTypePromises
      state b.input.r1_val b.input.r2_val b.input.rd b.input.PC
      (PureSpec.execute_RTYPE_srl_pure b.input).nextPC
      b.r1 b.r2 b.rd (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_r2_eq := b.h_input_r2
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end SrlRowBinding

/-- SRA-specific projection of the named `ProgramBinding` premise. -/
structure SraRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.SraInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opSra
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = false
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sra_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace SraRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SraRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32Zero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SraRowBinding main r_main state) :
    main.m32 r_main = 0 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SraRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SraRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SraRowBinding main r_main state)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1)) :
    b.input.r1_val = ZiskFv.AirsClean.BinaryExtension.rowA64 row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using
      h_facts
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main 0 h_match_v
  have h_op_v_eq : v.op 0 = ZiskFv.Trusted.OP_SRA := by
    have h_pins :=
      MainRowProvenance.sraPins_of_extracted_shape
        b.provenance b.h_op b.h_external
    rw [← h_op_fgl, h_pins.main_op]
  have h_op_is_shift : v.op_is_shift 0 = 1 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
      v 0 h_wfs).1 (Or.inr (Or.inr (Or.inl h_op_v_eq)))
  have h_a_range :=
    binaryExtensionABytesInRangeOfWfs h_bytes h_wfs
  have h :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.packed_a_eq_of_shift_match_m32_0_of_a_range
      main v r_main 0 (regidx_to_fin b.r1) b.input.r1_val b.m32Zero
      b.h_a_lo_t b.h_a_hi_t b.h_input_r1 h_op_is_shift h_match_v h_a_range
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowA64,
    ZiskFv.AirsClean.BinaryExtension.validA64] using h

theorem shiftPinRow
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SraRowBinding main r_main state)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_b0_range : ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact row) :
    b.input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using
      h_facts
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main 0 h_match_v
  have h_op_v_eq : v.op 0 = ZiskFv.Trusted.OP_SRA := by
    have h_pins :=
      MainRowProvenance.sraPins_of_extracted_shape
        b.provenance b.h_op b.h_external
    rw [← h_op_fgl, h_pins.main_op]
  have h_op_is_shift : v.op_is_shift 0 = 1 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
      v 0 h_wfs).1 (Or.inr (Or.inr (Or.inl h_op_v_eq)))
  have h :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.shift_pin_eq_of_shift_match_m32_0_of_b0_range
      main v r_main 0 (regidx_to_fin b.r2) b.input.r2_val b.m32Zero
      b.h_b_lo_t b.h_b_hi_t b.h_input_r2 h_op_is_shift h_match_v h_bytes
      h_wfs (by simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
        ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact] using h_b0_range)
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowShiftAmount,
    ZiskFv.AirsClean.BinaryExtension.validShiftAmount] using h

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SraRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.RTypePromises
      state b.input.r1_val b.input.r2_val b.input.rd b.input.PC
      (PureSpec.execute_RTYPE_sra_pure b.input).nextPC
      b.r1 b.r2 b.rd (b.bus).exec_row (b.bus).e0 (b.bus).e1 (b.bus).e2 where
  input_r1_eq := b.h_input_r1
  input_r2_eq := b.h_input_r2
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  m0_mult := by rfl
  m0_as := by rfl
  m1_mult := by rfl
  m1_as := by rfl
  m2_mult := by rfl
  m2_as := by rfl
  rd_idx := b.h_rd_idx

end SraRowBinding

/-- SLLW-specific projection of the named `ProgramBinding` premise. -/
structure SllwRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.SllwInput
  r1 : regidx
  r2 : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opSllW
  h_external : provenance.extractedRow.isExternalOp = true
  h_m32 : provenance.extractedRow.m32 = true
  h_store_pc : provenance.extractedRow.storePc = false
  h_a_lo_t : main.a_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_a_hi_t : main.a_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r1))
  h_b_lo_t : main.b_0 r_main =
    ZiskFv.Trusted.lane_lo
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_b_hi_t : main.b_1 r_main =
    ZiskFv.Trusted.lane_hi
      ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg
        (regidx_to_fin r2))
  h_input_r1 :
    read_xreg (regidx_to_fin r1) state = EStateM.Result.ok input.r1_val state
  h_input_r2 :
    read_xreg (regidx_to_fin r2) state = EStateM.Result.ok input.r2_val state
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_RTYPE_sllw_pure input).nextPC
  h_rd_idx :
    input.rd =
      Transpiler.wrap_to_regidx
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage provenance.mainRow) 1 1).ptr

namespace SllwRowBinding

@[reducible]
def bus {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllwRowBinding main r_main state) : BusRows where
  exec_row := b.execRow
  e0 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.aMemMessage b.provenance.mainRow) (-1) 1
  e1 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.bMemMessage b.provenance.mainRow) (-1) 1
  e2 :=
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Main.cMemMessage b.provenance.mainRow) 1 1

theorem m32One
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllwRowBinding main r_main state) :
    main.m32 r_main = 1 := by
  simpa [boolF, b.h_m32] using b.provenance.m32_eq

theorem rowStorePcZero
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllwRowBinding main r_main state) :
    b.provenance.mainRow.core.store_pc = 0 := by
  have h_main :
      main.store_pc r_main = 0 :=
    MainRowProvenance.storePcZero_of_extracted_shape b.provenance b.h_store_pc
  have h_row :
      b.provenance.mainRow.core.store_pc =
        (ZiskFv.AirsClean.Main.rowAt main r_main).store_pc :=
    congrArg (fun row => row.store_pc) b.provenance.row_eq
  exact h_row.trans (by simpa [ZiskFv.AirsClean.Main.rowAt] using h_main)

theorem laneRd
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllwRowBinding main r_main state) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match main r_main (b.bus).e2 := by
  have h :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      b.provenance.mainRow b.rowStorePcZero
  rw [b.provenance.row_eq] at h
  simpa [bus, ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt] using h

theorem inputR1Row
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllwRowBinding main r_main state)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1)) :
    (Sail.BitVec.extractLsb b.input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
      ZiskFv.AirsClean.BinaryExtension.rowA32 row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using
      h_facts
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main 0 h_match_v
  have h_op_v_eq : v.op 0 = ZiskFv.Trusted.OP_SLL_W := by
    have h_pins :=
      MainRowProvenance.sllwPins_of_extracted_shape
        b.provenance b.h_op b.h_external
    rw [← h_op_fgl, h_pins.main_op]
  have h_op_is_shift : v.op_is_shift 0 = 1 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
      v 0 h_wfs).1 (Or.inr (Or.inr (Or.inr (Or.inl h_op_v_eq))))
  have h_a_range :=
    binaryExtensionABytesInRangeOfWfs h_bytes h_wfs
  have h :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.packed_a_lo32_eq_of_shift_match_m32_1_of_a_range
      main v r_main 0 (regidx_to_fin b.r1) b.input.r1_val b.m32One
      b.h_a_lo_t b.h_a_hi_t b.h_input_r1 h_op_is_shift h_match_v h_a_range
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowA32,
    ZiskFv.AirsClean.BinaryExtension.validA32] using h

theorem shiftPinRow
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : SllwRowBinding main r_main state)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_b0_range : ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact row) :
    b.input.r2_val.toNat % 32 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32 row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using
      h_facts
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      main v r_main 0 h_match_v
  have h_op_v_eq : v.op 0 = ZiskFv.Trusted.OP_SLL_W := by
    have h_pins :=
      MainRowProvenance.sllwPins_of_extracted_shape
        b.provenance b.h_op b.h_external
    rw [← h_op_fgl, h_pins.main_op]
  have h_op_is_shift : v.op_is_shift 0 = 1 :=
    (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
      v 0 h_wfs).1 (Or.inr (Or.inr (Or.inr (Or.inl h_op_v_eq))))
  have h_extract :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.shift_pin_w_eq_of_shift_match_of_b0_range
      main v r_main 0 (regidx_to_fin b.r2) b.input.r2_val
      b.h_b_lo_t b.h_b_hi_t b.h_input_r2 h_op_is_shift h_match_v h_bytes
      h_wfs (by simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
        ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact] using h_b0_range)
  have h_mod :
      b.input.r2_val.toNat % 32 =
        (Sail.BitVec.extractLsb b.input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
          % 32 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  exact h_mod.trans (by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32,
      ZiskFv.AirsClean.BinaryExtension.validShiftAmount32] using h_extract)

end SllwRowBinding

/-- FENCE-specific projection of the named `ProgramBinding` premise. -/
structure FenceRowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.FenceInput
  fm : BitVec 4
  pred : BitVec 4
  succBits : BitVec 4
  rs : regidx
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  provenance : MainRowProvenance main r_main
  h_op : provenance.extractedRow.op = ExtractedConst.opFlag
  h_internal : provenance.extractedRow.isExternalOp = false
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_input_priv : state.regs.get? Register.cur_privilege = .some Privilege.Machine
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_FENCE_pure input).nextPC

namespace FenceRowBinding

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : FenceRowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.FencePromises
      state b.input.PC
      (PureSpec.execute_FENCE_pure b.input).nextPC
      b.execRow where
  input_pc_eq := b.h_input_pc
  input_priv_eq := b.h_input_priv
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches

end FenceRowBinding

/-- AUIPC `rd = x0` projection of the named `ProgramBinding` premise. -/
structure AuipcX0RowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.AuipcInput
  imm : BitVec 20
  rd : regidx
  execRow : List (Interaction.ExecutionBusEntry FGL)
  h_input_imm : input.imm = imm
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_input_rd_zero : input.rd = 0
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = (PureSpec.execute_AUIPC_pure input).nextPC

namespace AuipcX0RowBinding

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : AuipcX0RowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.UTypeNoMemPromises
      state b.input.imm b.input.rd b.input.PC
      (PureSpec.execute_AUIPC_pure b.input).nextPC
      b.imm b.rd b.execRow where
  input_imm_eq := b.h_input_imm
  input_rd_eq := b.h_input_rd
  input_pc_eq := b.h_input_pc
  input_rd_zero := b.h_input_rd_zero
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches

end AuipcX0RowBinding

/-- JAL `rd = x0` projection of the named `ProgramBinding` premise. -/
structure JalX0RowBinding
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : Nat)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) where
  input : PureSpec.JalInput
  imm : BitVec 21
  rd : regidx
  misaVal : RegisterType Register.misa
  execRow : List (Interaction.ExecutionBusEntry FGL)
  nextPCVal : BitVec 64
  h_input_rd : input.rd = regidx_to_fin rd
  h_input_rd_zero : input.rd = 0
  h_input_pc : state.regs.get? Register.PC = .some input.PC
  h_input_misa : state.regs.get? Register.misa = .some misaVal
  h_misa_c : Sail.BitVec.extractLsb misaVal 2 2 = 0#1
  h_exec_len : execRow.length = 2
  h_e0_mult : execRow[0]!.multiplicity = -1
  h_e1_mult : execRow[1]!.multiplicity = 1
  h_nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
      = nextPCVal
  h_success : (PureSpec.execute_JAL_pure input).success = true
  h_nextPC_option : (PureSpec.execute_JAL_pure input).nextPC = .some nextPCVal
  h_input_imm : input.imm = imm
  h_not_throws : (PureSpec.execute_JAL_pure input).throws = false

namespace JalX0RowBinding

@[reducible]
def promises {main : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : Nat}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (b : JalX0RowBinding main r_main state) :
    ZiskFv.EquivCore.Promises.JumpNoMemPromises
      state b.input.PC b.input.rd b.misaVal
      (PureSpec.execute_JAL_pure b.input).success
      (PureSpec.execute_JAL_pure b.input).nextPC
      b.rd b.execRow b.nextPCVal where
  input_rd_eq := b.h_input_rd
  input_rd_zero := b.h_input_rd_zero
  input_pc_eq := b.h_input_pc
  input_misa_eq := b.h_input_misa
  misa_c_zero := b.h_misa_c
  exec_len := b.h_exec_len
  e0_mult := b.h_e0_mult
  e1_mult := b.h_e1_mult
  nextPC_matches := b.h_nextPC_matches
  success := b.h_success
  nextPC_option := b.h_nextPC_option

end JalX0RowBinding

/-- The single named program-binding premise for P4 construction.

It supplies the Sail state sequence, the selected Main table, and per-row
decode/provenance projections. Later PRs add projections for the remaining
`ArmTag`s while keeping this as one named premise. -/
structure ProgramBinding (trace : AcceptedTrace) where
  stateAt :
    Fin trace.length →
      PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  mainTable : Air.Flat.Table FGL
  mainTable_mem : mainTable ∈ trace.witness.allTables
  mainTable_component :
    mainTable.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        trace.length trace.program
  mainTable_index : ∀ i : Fin trace.length, i.val < mainTable.table.length
  armTag : Fin trace.length → ArmTag
  beq :
    ∀ i : Fin trace.length, armTag i = ArmTag.beq →
      BeqRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  bne :
    ∀ i : Fin trace.length, armTag i = ArmTag.bne →
      BneRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  blt :
    ∀ i : Fin trace.length, armTag i = ArmTag.blt →
      BltRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  bge :
    ∀ i : Fin trace.length, armTag i = ArmTag.bge →
      BgeRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  bltu :
    ∀ i : Fin trace.length, armTag i = ArmTag.bltu →
      BltuRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  bgeu :
    ∀ i : Fin trace.length, armTag i = ArmTag.bgeu →
      BgeuRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  and :
    ∀ i : Fin trace.length, armTag i = ArmTag.and →
      AndRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  or :
    ∀ i : Fin trace.length, armTag i = ArmTag.or →
      OrRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  xor :
    ∀ i : Fin trace.length, armTag i = ArmTag.xor →
      XorRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  slt :
    ∀ i : Fin trace.length, armTag i = ArmTag.slt →
      SltRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  sltu :
    ∀ i : Fin trace.length, armTag i = ArmTag.sltu →
      SltuRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  slti :
    ∀ i : Fin trace.length, armTag i = ArmTag.slti →
      SltiRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  sltiu :
    ∀ i : Fin trace.length, armTag i = ArmTag.sltiu →
      SltiuRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  andi :
    ∀ i : Fin trace.length, armTag i = ArmTag.andi →
      AndiRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  ori :
    ∀ i : Fin trace.length, armTag i = ArmTag.ori →
      OriRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  xori :
    ∀ i : Fin trace.length, armTag i = ArmTag.xori →
      XoriRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  addw :
    ∀ i : Fin trace.length, armTag i = ArmTag.addw →
      AddwRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  subw :
    ∀ i : Fin trace.length, armTag i = ArmTag.subw →
      SubwRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  addiw :
    ∀ i : Fin trace.length, armTag i = ArmTag.addiw →
      AddiwRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  sll :
    ∀ i : Fin trace.length, armTag i = ArmTag.sll →
      SllRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  srl :
    ∀ i : Fin trace.length, armTag i = ArmTag.srl →
      SrlRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  sra :
    ∀ i : Fin trace.length, armTag i = ArmTag.sra →
      SraRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  sllw :
    ∀ i : Fin trace.length, armTag i = ArmTag.sllw →
      SllwRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  fence :
    ∀ i : Fin trace.length, armTag i = ArmTag.fence →
      FenceRowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  auipc_x0 :
    ∀ i : Fin trace.length, armTag i = ArmTag.auipc_x0 →
      AuipcX0RowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)
  jal_x0 :
    ∀ i : Fin trace.length, armTag i = ArmTag.jal_x0 →
      JalX0RowBinding
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program mainTable)
        i.val
        (stateAt i)

/-- Construct the BEQ envelope arm from an accepted trace plus the named
    program-binding projection for a BEQ row. -/
def construction_beq
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.beq) :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.beq i h_tag
  OpEnvelope.beqOfExtractedShape
    b.input
    b.ops
    b.provenance
    b.h_op
    b.h_external
    b.h_m32
    b.h_set_pc
    b.h_store_pc
    b.h_jmp_offset2
    b.promises

/-- BEQ's Aeneas bridge predicate is derived from the named program-binding
    provenance facts, not supplied as a separate premise. -/
theorem construction_beq_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.beq) :
    (construction_beq trace binding i h_tag).aeneasBridgeTrust := by
  let b := binding.beq i h_tag
  exact
    OpEnvelope.aeneasBridgeTrust_beqOfExtractedShape
      b.input
      b.ops
      b.provenance
      b.h_op
      b.h_external
      b.h_m32
      b.h_set_pc
      b.h_store_pc
      b.h_jmp_offset2
      b.promises

/-- Construct the BNE envelope arm from an accepted trace plus the named
    program-binding projection for a BNE row. -/
def construction_bne
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.bne) :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.bne i h_tag
  OpEnvelope.bneOfExtractedShape
    b.input b.ops b.provenance b.h_op b.h_external b.h_m32 b.h_set_pc
    b.h_store_pc b.h_jmp_offset1 b.promises

theorem construction_bne_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.bne) :
    (construction_bne trace binding i h_tag).aeneasBridgeTrust := by
  let b := binding.bne i h_tag
  exact
    OpEnvelope.aeneasBridgeTrust_bneOfExtractedShape
      b.input b.ops b.provenance b.h_op b.h_external b.h_m32 b.h_set_pc
      b.h_store_pc b.h_jmp_offset1 b.promises

/-- Construct the BLT envelope arm from an accepted trace plus the named
    program-binding projection for a BLT row. -/
def construction_blt
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.blt) :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.blt i h_tag
  OpEnvelope.bltOfExtractedShape
    b.input b.ops b.provenance b.h_op b.h_external b.h_m32 b.h_set_pc
    b.h_store_pc b.h_jmp_offset2 b.promises

theorem construction_blt_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.blt) :
    (construction_blt trace binding i h_tag).aeneasBridgeTrust := by
  let b := binding.blt i h_tag
  exact
    OpEnvelope.aeneasBridgeTrust_bltOfExtractedShape
      b.input b.ops b.provenance b.h_op b.h_external b.h_m32 b.h_set_pc
      b.h_store_pc b.h_jmp_offset2 b.promises

/-- Construct the BGE envelope arm from an accepted trace plus the named
    program-binding projection for a BGE row. -/
def construction_bge
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.bge) :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.bge i h_tag
  OpEnvelope.bgeOfExtractedShape
    b.input b.ops b.provenance b.h_op b.h_external b.h_m32 b.h_set_pc
    b.h_store_pc b.h_jmp_offset1 b.promises

theorem construction_bge_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.bge) :
    (construction_bge trace binding i h_tag).aeneasBridgeTrust := by
  let b := binding.bge i h_tag
  exact
    OpEnvelope.aeneasBridgeTrust_bgeOfExtractedShape
      b.input b.ops b.provenance b.h_op b.h_external b.h_m32 b.h_set_pc
      b.h_store_pc b.h_jmp_offset1 b.promises

/-- Construct the BLTU envelope arm from an accepted trace plus the named
    program-binding projection for a BLTU row. -/
def construction_bltu
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.bltu) :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.bltu i h_tag
  OpEnvelope.bltuOfExtractedShape
    b.input b.ops b.provenance b.h_op b.h_external b.h_m32 b.h_set_pc
    b.h_store_pc b.h_jmp_offset2 b.promises

theorem construction_bltu_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.bltu) :
    (construction_bltu trace binding i h_tag).aeneasBridgeTrust := by
  let b := binding.bltu i h_tag
  exact
    OpEnvelope.aeneasBridgeTrust_bltuOfExtractedShape
      b.input b.ops b.provenance b.h_op b.h_external b.h_m32 b.h_set_pc
      b.h_store_pc b.h_jmp_offset2 b.promises

/-- Construct the BGEU envelope arm from an accepted trace plus the named
    program-binding projection for a BGEU row. -/
def construction_bgeu
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.bgeu) :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.bgeu i h_tag
  OpEnvelope.bgeuOfExtractedShape
    b.input b.ops b.provenance b.h_op b.h_external b.h_m32 b.h_set_pc
    b.h_store_pc b.h_jmp_offset1 b.promises

theorem construction_bgeu_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.bgeu) :
    (construction_bgeu trace binding i h_tag).aeneasBridgeTrust := by
  let b := binding.bgeu i h_tag
  exact
    OpEnvelope.aeneasBridgeTrust_bgeuOfExtractedShape
      b.input b.ops b.provenance b.h_op b.h_external b.h_m32 b.h_set_pc
      b.h_store_pc b.h_jmp_offset1 b.promises

/-- Construct the XOR Binary-provider envelope arm from an accepted trace plus
    the named program-binding projection and provider row facts. -/
def construction_xor
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.xor)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.xor i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesXor providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_r2_row := b.inputR2Row providerInput h_matches h_match_static
  OpEnvelope.xorOfExtractedShape
    b.input b.r1 b.r2 b.rd
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row b.laneRd b.promises

theorem construction_xor_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.xor)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_xor trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.xor i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesXor providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_r2_row := b.inputR2Row providerInput h_matches h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_xorOfExtractedShape
      b.input b.r1 b.r2 b.rd
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_input_r2_row b.laneRd b.promises

def construction_and
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.and)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.and i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesAnd providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_r2_row := b.inputR2Row providerInput h_matches h_match_static
  OpEnvelope.andOfExtractedShape
    b.input b.r1 b.r2 b.rd
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row b.laneRd b.promises

theorem construction_and_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.and)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_and trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.and i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesAnd providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_r2_row := b.inputR2Row providerInput h_matches h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_andOfExtractedShape
      b.input b.r1 b.r2 b.rd
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_input_r2_row b.laneRd b.promises

def construction_or
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.or)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.or i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesOr providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_r2_row := b.inputR2Row providerInput h_matches h_match_static
  OpEnvelope.orOfExtractedShape
    b.input b.r1 b.r2 b.rd
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row b.laneRd b.promises

theorem construction_or_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.or)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_or trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.or i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesOr providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_r2_row := b.inputR2Row providerInput h_matches h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_orOfExtractedShape
      b.input b.r1 b.r2 b.rd
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_input_r2_row b.laneRd b.promises

def construction_slt
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.slt)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.slt i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_core :
      ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow providerInput) 0 :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesSlt providerInput h_core h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_r2_row := b.inputR2Row providerInput h_matches h_match_static
  OpEnvelope.sltOfExtractedShape
    b.input b.r1 b.r2 b.rd
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row b.laneRd b.promises

theorem construction_slt_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.slt)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_slt trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.slt i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_core :
      ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow providerInput) 0 :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesSlt providerInput h_core h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_r2_row := b.inputR2Row providerInput h_matches h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_sltOfExtractedShape
      b.input b.r1 b.r2 b.rd
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_input_r2_row b.laneRd b.promises

def construction_sltu
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sltu)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.sltu i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_core :
      ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow providerInput) 0 :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesSltu providerInput h_core h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_r2_row := b.inputR2Row providerInput h_matches h_match_static
  OpEnvelope.sltuOfExtractedShape
    b.input b.r1 b.r2 b.rd
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row b.laneRd b.promises

theorem construction_sltu_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sltu)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_sltu trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.sltu i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_core :
      ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow providerInput) 0 :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesSltu providerInput h_core h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_r2_row := b.inputR2Row providerInput h_matches h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_sltuOfExtractedShape
      b.input b.r1 b.r2 b.rd
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_input_r2_row b.laneRd b.promises

def construction_slti
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.slti)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.slti i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_core :
      ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow providerInput) 0 :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesSlti providerInput h_core h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  OpEnvelope.sltiOfExtractedShape
    b.input b.r1 b.rd b.imm
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external b.h_m32
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row b.h_imm_subset b.laneRd b.promises

theorem construction_slti_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.slti)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_slti trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.slti i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_core :
      ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow providerInput) 0 :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesSlti providerInput h_core h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_sltiOfExtractedShape
      b.input b.r1 b.rd b.imm
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external b.h_m32
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row b.h_imm_subset b.laneRd b.promises

def construction_sltiu
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sltiu)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.sltiu i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_core :
      ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow providerInput) 0 :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesSltiu providerInput h_core h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  OpEnvelope.sltiuOfExtractedShape
    b.input b.r1 b.rd b.imm
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external b.h_m32
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row b.h_imm_subset b.laneRd b.promises

theorem construction_sltiu_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sltiu)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_sltiu trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.sltiu i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_core :
      ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow providerInput) 0 :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesSltiu providerInput h_core h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_sltiuOfExtractedShape
      b.input b.r1 b.rd b.imm
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external b.h_m32
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row b.h_imm_subset b.laneRd b.promises

def construction_andi
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.andi)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.andi i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesAndi providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_imm_row := b.inputImmRow providerInput h_matches h_match_static
  OpEnvelope.andiOfExtractedShape
    b.input b.r1 b.rd b.imm
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_imm_row b.h_imm_subset b.laneRd b.promises

theorem construction_andi_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.andi)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_andi trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.andi i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesAndi providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_imm_row := b.inputImmRow providerInput h_matches h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_andiOfExtractedShape
      b.input b.r1 b.rd b.imm
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_input_imm_row b.h_imm_subset b.laneRd b.promises

def construction_ori
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.ori)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.ori i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesOri providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_imm_row := b.inputImmRow providerInput h_matches h_match_static
  OpEnvelope.oriOfExtractedShape
    b.input b.r1 b.rd b.imm
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_imm_row b.h_imm_subset b.laneRd b.promises

theorem construction_ori_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.ori)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_ori trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.ori i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesOri providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_imm_row := b.inputImmRow providerInput h_matches h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_oriOfExtractedShape
      b.input b.r1 b.rd b.imm
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_input_imm_row b.h_imm_subset b.laneRd b.promises

def construction_xori
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.xori)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.xori i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesXori providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_imm_row := b.inputImmRow providerInput h_matches h_match_static
  OpEnvelope.xoriOfExtractedShape
    b.input b.r1 b.rd b.imm
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_imm_row b.h_imm_subset b.laneRd b.promises

theorem construction_xori_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.xori)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_xori trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.xori i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  have h_row_spec : ZiskFv.AirsClean.Binary.Spec providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.1
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput := by
    have h := h_component_spec
    rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h
    exact h.2
  have h_matches := b.byteMatchesXori providerInput h_row_spec h_static h_match_static
  have h_input_r1_row := b.inputR1Row providerInput h_matches h_match_static
  have h_input_imm_row := b.inputImmRow providerInput h_matches h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_xoriOfExtractedShape
      b.input b.r1 b.rd b.imm
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_input_imm_row b.h_imm_subset b.laneRd b.promises

/-- Construct the ADDW Binary-provider envelope arm from an accepted trace plus
    the named program-binding projection and provider row facts. -/
def construction_addw
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.addw)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.addw i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_facts :
      ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts providerInput :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).2
  have h_input_r1 := b.inputR1Extract providerInput h_facts h_match_static
  have h_input_r2 := b.inputR2Extract providerInput h_facts h_match_static
  OpEnvelope.addwOfExtractedShape
    b.input b.r1 b.r2 b.rd
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1 h_input_r2 b.laneRd b.promises

theorem construction_addw_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.addw)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_addw trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.addw i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_facts :
      ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts providerInput :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).2
  have h_input_r1 := b.inputR1Extract providerInput h_facts h_match_static
  have h_input_r2 := b.inputR2Extract providerInput h_facts h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_addwOfExtractedShape
      b.input b.r1 b.r2 b.rd
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1 h_input_r2 b.laneRd b.promises

/-- Construct the SUBW Binary-provider envelope arm from an accepted trace plus
    the named program-binding projection and provider row facts. -/
def construction_subw
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.subw)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.subw i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_facts :
      ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts providerInput :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).2
  have h_input_r1 := b.inputR1Extract providerInput h_facts h_match_static
  have h_input_r2 := b.inputR2Extract providerInput h_facts h_match_static
  OpEnvelope.subwOfExtractedShape
    b.input b.r1 b.r2 b.rd
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1 h_input_r2 b.laneRd b.promises

theorem construction_subw_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.subw)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_subw trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.subw i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_facts :
      ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts providerInput :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).2
  have h_input_r1 := b.inputR1Extract providerInput h_facts h_match_static
  have h_input_r2 := b.inputR2Extract providerInput h_facts h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_subwOfExtractedShape
      b.input b.r1 b.r2 b.rd
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1 h_input_r2 b.laneRd b.promises

/-- Construct the ADDIW Binary-provider envelope arm from an accepted trace plus
    the named program-binding projection and provider row facts. -/
def construction_addiw
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.addiw)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.addiw i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_facts :
      ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts providerInput :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).2
  have h_input_r1 := b.inputR1Extract providerInput h_facts h_match_static
  OpEnvelope.addiwOfExtractedShape
    b.input b.r1 b.rd b.imm
    (ZiskFv.AirsClean.Binary.validOfRow providerInput)
    b.bus b.provenance b.h_op b.h_external b.h_imm_subset
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1 b.laneRd b.promises

theorem construction_addiw_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.addiw)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_addiw trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.addiw i h_tag
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_facts :
      ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts providerInput :=
    (ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row).2
  have h_input_r1 := b.inputR1Extract providerInput h_facts h_match_static
  exact
    OpEnvelope.aeneasBridgeTrust_addiwOfExtractedShape
      b.input b.r1 b.rd b.imm
      (ZiskFv.AirsClean.Binary.validOfRow providerInput)
      b.bus b.provenance b.h_op b.h_external b.h_imm_subset
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1 b.laneRd b.promises

/-- Construct the SLL BinaryExtension-provider envelope arm from an accepted
    trace plus the named program-binding projection and provider row facts. -/
def construction_sll
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sll)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component =
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.sll i h_tag
  let providerInput :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_input_r1 := b.inputR1Row providerInput h_shift_facts.1 h_match_static
  have h_shift_pin := b.shiftPinRow providerInput h_shift_facts.1 h_match_static
    h_shift_facts.2
  OpEnvelope.sllOfExtractedShape
    b.input b.r1 b.r2 b.rd providerTable providerRow b.bus
    b.provenance b.h_op b.h_external b.promises
    h_component h_table_spec h_provider_row h_match_static
    h_input_r1 h_shift_pin b.laneRd

theorem construction_sll_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sll)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component =
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_sll trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.sll i h_tag
  let providerInput :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_input_r1 := b.inputR1Row providerInput h_shift_facts.1 h_match_static
  have h_shift_pin := b.shiftPinRow providerInput h_shift_facts.1 h_match_static
    h_shift_facts.2
  exact
    OpEnvelope.aeneasBridgeTrust_sllOfExtractedShape
      b.input b.r1 b.r2 b.rd providerTable providerRow b.bus
      b.provenance b.h_op b.h_external b.promises
      h_component h_table_spec h_provider_row h_match_static
      h_input_r1 h_shift_pin b.laneRd

/-- Construct the SRL BinaryExtension-provider envelope arm from an accepted
    trace plus the named program-binding projection and provider row facts. -/
def construction_srl
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.srl)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component =
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.srl i h_tag
  let providerInput :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_input_r1 := b.inputR1Row providerInput h_shift_facts.1 h_match_static
  have h_shift_pin := b.shiftPinRow providerInput h_shift_facts.1 h_match_static
    h_shift_facts.2
  OpEnvelope.srlOfExtractedShape
    b.input b.r1 b.r2 b.rd providerTable providerRow b.bus
    b.provenance b.h_op b.h_external b.promises
    h_component h_table_spec h_provider_row h_match_static
    h_input_r1 h_shift_pin b.laneRd

theorem construction_srl_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.srl)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component =
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_srl trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.srl i h_tag
  let providerInput :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_input_r1 := b.inputR1Row providerInput h_shift_facts.1 h_match_static
  have h_shift_pin := b.shiftPinRow providerInput h_shift_facts.1 h_match_static
    h_shift_facts.2
  exact
    OpEnvelope.aeneasBridgeTrust_srlOfExtractedShape
      b.input b.r1 b.r2 b.rd providerTable providerRow b.bus
      b.provenance b.h_op b.h_external b.promises
      h_component h_table_spec h_provider_row h_match_static
      h_input_r1 h_shift_pin b.laneRd

/-- Construct the SRA BinaryExtension-provider envelope arm from an accepted
    trace plus the named program-binding projection and provider row facts. -/
def construction_sra
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sra)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component =
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.sra i h_tag
  let providerInput :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_input_r1 := b.inputR1Row providerInput h_shift_facts.1 h_match_static
  have h_shift_pin := b.shiftPinRow providerInput h_shift_facts.1 h_match_static
    h_shift_facts.2
  OpEnvelope.sraOfExtractedShape
    b.input b.r1 b.r2 b.rd providerTable providerRow b.bus
    b.provenance b.h_op b.h_external b.promises
    h_component h_table_spec h_provider_row h_match_static
    h_input_r1 h_shift_pin b.laneRd

theorem construction_sra_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sra)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component =
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_sra trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.sra i h_tag
  let providerInput :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_input_r1 := b.inputR1Row providerInput h_shift_facts.1 h_match_static
  have h_shift_pin := b.shiftPinRow providerInput h_shift_facts.1 h_match_static
    h_shift_facts.2
  exact
    OpEnvelope.aeneasBridgeTrust_sraOfExtractedShape
      b.input b.r1 b.r2 b.rd providerTable providerRow b.bus
      b.provenance b.h_op b.h_external b.promises
      h_component h_table_spec h_provider_row h_match_static
      h_input_r1 h_shift_pin b.laneRd

/-- Construct the SLLW BinaryExtension-provider envelope arm from an accepted
    trace plus the named program-binding projection and provider row facts. -/
def construction_sllw
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sllw)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component =
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.sllw i h_tag
  let providerInput :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_input_r1 := b.inputR1Row providerInput h_shift_facts.1 h_match_static
  have h_shift_pin := b.shiftPinRow providerInput h_shift_facts.1 h_match_static
    h_shift_facts.2
  OpEnvelope.sllwOfExtractedShape
    b.input b.r1 b.r2 b.rd providerTable providerRow b.bus
    b.provenance b.h_op b.h_external b.h_input_r1 b.h_input_r2
    b.h_input_rd b.h_input_pc b.h_exec_len b.h_e0_mult b.h_e1_mult
    b.h_nextPC_matches (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) b.h_rd_idx h_component h_table_spec h_provider_row
    h_match_static h_input_r1 h_shift_pin b.laneRd

theorem construction_sllw_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sllw)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component =
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    :
    (construction_sllw trace binding i h_tag providerTable providerRow h_component
      h_table_spec h_provider_row h_match_static).aeneasBridgeTrust := by
  let b := binding.sllw i h_tag
  let providerInput :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_input_r1 := b.inputR1Row providerInput h_shift_facts.1 h_match_static
  have h_shift_pin := b.shiftPinRow providerInput h_shift_facts.1 h_match_static
    h_shift_facts.2
  exact
    OpEnvelope.aeneasBridgeTrust_sllwOfExtractedShape
      b.input b.r1 b.r2 b.rd providerTable providerRow b.bus
      b.provenance b.h_op b.h_external b.h_input_r1 b.h_input_r2
      b.h_input_rd b.h_input_pc b.h_exec_len b.h_e0_mult b.h_e1_mult
      b.h_nextPC_matches (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) b.h_rd_idx h_component h_table_spec h_provider_row
      h_match_static h_input_r1 h_shift_pin b.laneRd

theorem exists_staticBinary_provider_row_matches_logic_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_AND
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_OR
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_XOR) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_logic_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_staticBinary_provider_row_matches_compare_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_LT
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_LTU) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_compare_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_staticBinary_provider_row_matches_w_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_ADD_W
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SUB_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_w_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_binaryExtension_provider_row_matches_shift_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SLL
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SRL
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SRA
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SLL_W
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SRL_W
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SRA_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component =
            ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.BinaryExtension.opBusMessage
                (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    exists_binaryExtension_provider_row_matches_legacy_main_of_shift_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_construction_xor_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.xor) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.xor i h_tag
  have h_pins :=
    MainRowProvenance.xorPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_pins.main_active (.inr (.inr h_pins.main_op))
  let env :=
    construction_xor trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_xor_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_and_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.and) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.and i h_tag
  have h_pins :=
    MainRowProvenance.andPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_pins.main_active (.inl h_pins.main_op)
  let env :=
    construction_and trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_and_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_or_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.or) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.or i h_tag
  have h_pins :=
    MainRowProvenance.orPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_pins.main_active (.inr (.inl h_pins.main_op))
  let env :=
    construction_or trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_or_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_slt_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.slt) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.slt i h_tag
  have h_pins :=
    MainRowProvenance.ltPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_compare_from_binding
      trace binding i h_pins.main_active (.inl h_pins.main_op)
  let env :=
    construction_slt trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_slt_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_sltu_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sltu) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.sltu i h_tag
  have h_pins :=
    MainRowProvenance.ltuPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_compare_from_binding
      trace binding i h_pins.main_active (.inr h_pins.main_op)
  let env :=
    construction_sltu trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_sltu_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_slti_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.slti) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.slti i h_tag
  have h_pins :=
    MainRowProvenance.ltPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_compare_from_binding
      trace binding i h_pins.main_active (.inl h_pins.main_op)
  let env :=
    construction_slti trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_slti_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_sltiu_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sltiu) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.sltiu i h_tag
  have h_pins :=
    MainRowProvenance.ltuPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_compare_from_binding
      trace binding i h_pins.main_active (.inr h_pins.main_op)
  let env :=
    construction_sltiu trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_sltiu_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_andi_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.andi) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.andi i h_tag
  have h_pins :=
    MainRowProvenance.andPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_pins.main_active (.inl h_pins.main_op)
  let env :=
    construction_andi trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_andi_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_ori_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.ori) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.ori i h_tag
  have h_pins :=
    MainRowProvenance.orPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_pins.main_active (.inr (.inl h_pins.main_op))
  let env :=
    construction_ori trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_ori_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_xori_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.xori) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.xori i h_tag
  have h_pins :=
    MainRowProvenance.xorPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_pins.main_active (.inr (.inr h_pins.main_op))
  let env :=
    construction_xori trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_xori_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_addw_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.addw) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.addw i h_tag
  have h_pins :=
    MainRowProvenance.addwPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_w_from_binding
      trace binding i h_pins.main_active (.inl h_pins.main_op)
  let env :=
    construction_addw trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_addw_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_subw_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.subw) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.subw i h_tag
  have h_pins :=
    MainRowProvenance.subwPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_w_from_binding
      trace binding i h_pins.main_active (.inr h_pins.main_op)
  let env :=
    construction_subw trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_subw_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_addiw_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.addiw) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.addiw i h_tag
  have h_pins :=
    MainRowProvenance.addwPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_w_from_binding
      trace binding i h_pins.main_active (.inl h_pins.main_op)
  let env :=
    construction_addiw trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_addiw_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_sll_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sll) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.sll i h_tag
  have h_pins :=
    MainRowProvenance.sllPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i h_pins.main_active (.inl h_pins.main_op)
  let env :=
    construction_sll trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_sll_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_srl_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.srl) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.srl i h_tag
  have h_pins :=
    MainRowProvenance.srlPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i h_pins.main_active (.inr (.inl h_pins.main_op))
  let env :=
    construction_srl trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_srl_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_sra_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sra) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.sra i h_tag
  have h_pins :=
    MainRowProvenance.sraPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i h_pins.main_active (.inr (.inr (.inl h_pins.main_op)))
  let env :=
    construction_sra trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_sra_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

theorem exists_construction_sllw_from_balance
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.sllw) :
    ∃ env :
      OpEnvelope
        (binding.stateAt i)
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val,
      env.aeneasBridgeTrust := by
  let b := binding.sllw i h_tag
  have h_pins :=
    MainRowProvenance.sllwPins_of_extracted_shape
      b.provenance b.h_op b.h_external
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i h_pins.main_active
      (.inr (.inr (.inr (.inl h_pins.main_op))))
  let env :=
    construction_sllw trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_sllw_aeneasBridgeTrust trace binding i h_tag providerTable
      providerRow h_component h_table_spec h_providerRow h_match_static⟩

/-- Construct the FENCE envelope arm from an accepted trace plus the named
    program-binding projection for a FENCE row. -/
def construction_fence
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.fence) :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.fence i h_tag
  OpEnvelope.fenceOfExtractedShape
    b.input b.fm b.pred b.succBits b.rs b.rd b.execRow
    b.provenance b.h_op b.h_internal b.promises

theorem construction_fence_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.fence) :
    (construction_fence trace binding i h_tag).aeneasBridgeTrust := by
  let b := binding.fence i h_tag
  exact
    OpEnvelope.aeneasBridgeTrust_fenceOfExtractedShape
      b.input b.fm b.pred b.succBits b.rs b.rd b.execRow
      b.provenance b.h_op b.h_internal b.promises

/-- Construct the AUIPC `rd = x0` no-memory envelope arm from the named
    program-binding projection. -/
def construction_auipc_x0
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.auipc_x0) :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.auipc_x0 i h_tag
  OpEnvelope.auipc_x0 b.input b.imm b.rd b.execRow b.promises

theorem construction_auipc_x0_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.auipc_x0) :
    (construction_auipc_x0 trace binding i h_tag).aeneasBridgeTrust := by
  simp [construction_auipc_x0, OpEnvelope.aeneasBridgeTrust]

/-- Construct the JAL `rd = x0` no-memory envelope arm from the named
    program-binding projection. -/
def construction_jal_x0
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.jal_x0) :
    OpEnvelope
      (binding.stateAt i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val :=
  let b := binding.jal_x0 i h_tag
  OpEnvelope.jal_x0
    b.input b.imm b.rd b.misaVal b.execRow b.nextPCVal
    b.promises b.h_input_imm b.h_not_throws

theorem construction_jal_x0_aeneasBridgeTrust
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_tag : binding.armTag i = ArmTag.jal_x0) :
    (construction_jal_x0 trace binding i h_tag).aeneasBridgeTrust := by
  simp [construction_jal_x0, OpEnvelope.aeneasBridgeTrust]

end ZiskFv.Compliance
