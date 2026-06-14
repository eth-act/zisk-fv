import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.Compliance.AeneasBridgeTrust
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.EquivCore.Promises.BranchHelpers
import ZiskFv.EquivCore.Promises.Fence
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
  | xor
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
  xor :
    ∀ i : Fin trace.length, armTag i = ArmTag.xor →
      XorRowBinding
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
  have h_pins :=
    MainRowProvenance.xorPins_of_extracted_shape
      b.provenance b.h_op b.h_external
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
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_pins.main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_table_spec, h_match_static⟩ :=
    exists_staticBinary_provider_row_matches_legacy_main_of_xor_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_pins.main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_pins.main_op
  let env :=
    construction_xor trace binding i h_tag providerTable providerRow
      h_component h_table_spec h_providerRow h_match_static
  exact ⟨env,
    construction_xor_aeneasBridgeTrust trace binding i h_tag providerTable
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
