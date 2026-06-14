import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.Compliance.AeneasBridgeTrust
import ZiskFv.EquivCore.Promises.BranchHelpers

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

/-- Accepted committed trace for the full RV64IM Clean ensemble. -/
structure AcceptedTrace where
  length : Nat
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program length
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble
  constraints : witness.Constraints
  balanced : witness.BalancedChannels

/-- Opcode-family selector exposed by the program binding. PR1 only consumes
    `beq`; later P4 PRs extend the construction dispatcher over all tags. -/
inductive ArmTag where
  | beq
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
  armTag : Fin trace.length → ArmTag
  beq :
    ∀ i : Fin trace.length, armTag i = ArmTag.beq →
      BeqRowBinding
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

end ZiskFv.Compliance
