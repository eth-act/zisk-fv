import ZiskFv.Completeness.Rv64im.Shapes
import ZiskFv.SailSpec.Auxiliaries

/-!
# Sail-derived RV64IM decode domain — core definitions

This part holds the Sail raw-decode/encode domain definitions, the supported
RV64IM constructor-surface predicates, the executable-raw definitions, and the
`*_of_pure` lifting lemmas.  It is the base part of the split
`ZiskFv.Completeness.Rv64im.SailDecode` module.
-/

namespace ZiskFv.Completeness.SailDecode

open ZiskFv.Completeness

abbrev RawInstruction := Rv.RawInstruction
abbrev SailState := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

def SailReturns {α : Type} (action : SailM α) (state : SailState) (value : α) : Prop :=
  action state = EStateM.Result.ok value state

def Rv64imEnabledSailState (state : SailState) : Prop :=
  LeanRV64D.Functions.currentlyEnabled extension.Ext_M state =
    EStateM.Result.ok true state ∧
  LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul state =
    EStateM.Result.ok false state

/-- Sail raw decode, from the generated Sail `ext_decode` entrypoint. -/
def SailDecodesTo (raw : RawInstruction) (inst : instruction) : Prop :=
  LeanRV64D.Functions.ext_decode raw = pure inst

/-- Sail raw encoding, from the generated Sail `encdec_forwards` entrypoint. -/
def SailEncodesTo (inst : instruction) (raw : RawInstruction) : Prop :=
  LeanRV64D.Functions.encdec_forwards inst = pure raw

/-- State-aware Sail raw decode, for generated Sail branches that consult
extension state before returning a decoded constructor. -/
def SailDecodesToIn (state : SailState) (raw : RawInstruction) (inst : instruction) : Prop :=
  SailReturns (LeanRV64D.Functions.ext_decode raw) state inst

/-- State-aware Sail raw encoding, for generated Sail branches that consult
extension state before returning a raw word. -/
def SailEncodesToIn (state : SailState) (inst : instruction) (raw : RawInstruction) : Prop :=
  SailReturns (LeanRV64D.Functions.encdec_forwards inst) state raw

theorem sail_returns_of_pure {α : Type} {action : SailM α} {value : α}
    (h : action = pure value) :
    ∀ state, SailReturns action state value := by
  intro state
  rw [h]
  rfl

theorem sailM_bind_ok {α β : Type} {state : SailState}
    {action : SailM α} {next : α → SailM β} {a : α} {b : β}
    (h_action : action state = EStateM.Result.ok a state)
    (h_next : next a state = EStateM.Result.ok b state) :
    (action >>= next) state = EStateM.Result.ok b state := by
  simp [bind, h_action, h_next]

theorem sail_decodes_to_in_of_pure
    {raw : RawInstruction} {inst : instruction}
    (h : SailDecodesTo raw inst) :
    ∀ state, SailDecodesToIn state raw inst :=
  sail_returns_of_pure h

theorem sail_encodes_to_in_of_pure
    {raw : RawInstruction} {inst : instruction}
    (h : SailEncodesTo inst raw) :
    ∀ state, SailEncodesToIn state inst raw :=
  sail_returns_of_pure h

theorem sailM_pure_injective {α : Type} {a b : α}
    (h : (pure a : SailM α) = pure b) : a = b := by
  have h_app :=
    congrFun h
      (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  simpa [EStateM.pure] using h_app

/-- The Step 3 pilot domain: Sail decodes the raw word to RV64 ADD and the
generated Sail encoder maps that constructor back to the same raw word. -/
def SailAddExecutableRaw (raw : RawInstruction) : Prop :=
  ∃ rs2 rs1 rd,
    let inst := instruction.RTYPE (rs2, rs1, rd, rop.ADD)
    SailDecodesTo raw inst ∧ SailEncodesTo inst raw

/-- Sail RTYPE register-ALU constructor surface. -/
def SailRegisterAluInstruction (inst : instruction) : Prop :=
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.ADD)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.SUB)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.SLL)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.SLT)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.SLTU)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.XOR)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.SRL)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.SRA)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.OR)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.AND))

/-- Sail RTYPEW register-word-ALU constructor surface. -/
def SailRegisterWordAluInstruction (inst : instruction) : Prop :=
  (∃ rs2 rs1 rd, inst = instruction.RTYPEW (rs2, rs1, rd, ropw.ADDW)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPEW (rs2, rs1, rd, ropw.SUBW)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPEW (rs2, rs1, rd, ropw.SLLW)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPEW (rs2, rs1, rd, ropw.SRLW)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPEW (rs2, rs1, rd, ropw.SRAW))

/-- Sail M-extension constructor surface implemented by ZisK RV64IM. -/
def SailMExtensionInstruction (inst : instruction) : Prop :=
  (∃ rs2 rs1 rd,
    inst = instruction.MUL (rs2, rs1, rd,
      { result_part := VectorHalf.Low,
        signed_rs1 := Signedness.Signed,
        signed_rs2 := Signedness.Signed })) ∨
  (∃ rs2 rs1 rd,
    inst = instruction.MUL (rs2, rs1, rd,
      { result_part := VectorHalf.High,
        signed_rs1 := Signedness.Signed,
        signed_rs2 := Signedness.Signed })) ∨
  (∃ rs2 rs1 rd,
    inst = instruction.MUL (rs2, rs1, rd,
      { result_part := VectorHalf.High,
        signed_rs1 := Signedness.Signed,
        signed_rs2 := Signedness.Unsigned })) ∨
  (∃ rs2 rs1 rd,
    inst = instruction.MUL (rs2, rs1, rd,
      { result_part := VectorHalf.High,
        signed_rs1 := Signedness.Unsigned,
        signed_rs2 := Signedness.Unsigned })) ∨
  (∃ rs2 rs1 rd, inst = instruction.MULW (rs2, rs1, rd)) ∨
  (∃ rs2 rs1 rd, inst = instruction.DIV (rs2, rs1, rd, false)) ∨
  (∃ rs2 rs1 rd, inst = instruction.DIV (rs2, rs1, rd, true)) ∨
  (∃ rs2 rs1 rd, inst = instruction.DIVW (rs2, rs1, rd, false)) ∨
  (∃ rs2 rs1 rd, inst = instruction.DIVW (rs2, rs1, rd, true)) ∨
  (∃ rs2 rs1 rd, inst = instruction.REM (rs2, rs1, rd, false)) ∨
  (∃ rs2 rs1 rd, inst = instruction.REM (rs2, rs1, rd, true)) ∨
  (∃ rs2 rs1 rd, inst = instruction.REMW (rs2, rs1, rd, false)) ∨
  (∃ rs2 rs1 rd, inst = instruction.REMW (rs2, rs1, rd, true))

/-- Sail I-type arithmetic/logical immediate constructor surface implemented by
ZisK RV64IM, excluding shift-immediate constructors. -/
def SailImmediateAluInstruction (inst : instruction) : Prop :=
  (∃ imm rs1 rd, inst = instruction.ITYPE (imm, rs1, rd, iop.ADDI)) ∨
  (∃ imm rs1 rd, inst = instruction.ITYPE (imm, rs1, rd, iop.SLTI)) ∨
  (∃ imm rs1 rd, inst = instruction.ITYPE (imm, rs1, rd, iop.SLTIU)) ∨
  (∃ imm rs1 rd, inst = instruction.ITYPE (imm, rs1, rd, iop.XORI)) ∨
  (∃ imm rs1 rd, inst = instruction.ITYPE (imm, rs1, rd, iop.ORI)) ∨
  (∃ imm rs1 rd, inst = instruction.ITYPE (imm, rs1, rd, iop.ANDI))

/-- Sail RV64 shift-immediate constructor surface implemented by ZisK RV64IM. -/
def SailShiftImmediateInstruction (inst : instruction) : Prop :=
  (∃ shamt rs1 rd, inst = instruction.SHIFTIOP (shamt, rs1, rd, sop.SLLI)) ∨
  (∃ shamt rs1 rd, inst = instruction.SHIFTIOP (shamt, rs1, rd, sop.SRLI)) ∨
  (∃ shamt rs1 rd, inst = instruction.SHIFTIOP (shamt, rs1, rd, sop.SRAI))

/-- Sail RV64 word immediate arithmetic/shift constructor surface implemented
by ZisK RV64IM. -/
def SailImmediateWordAluInstruction (inst : instruction) : Prop :=
  (∃ imm rs1 rd, inst = instruction.ADDIW (imm, rs1, rd)) ∨
  (∃ shamt rs1 rd, inst = instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SLLIW)) ∨
  (∃ shamt rs1 rd, inst = instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SRLIW)) ∨
  (∃ shamt rs1 rd, inst = instruction.SHIFTIWOP (shamt, rs1, rd, sopw.SRAIW))

/-- Sail branch constructor surface implemented by ZisK RV64IM. Sail's
encoder accepts only aligned B-type immediates, represented by bit 0 = 0. -/
def SailBranchInstruction (inst : instruction) : Prop :=
  (∃ imm rs2 rs1,
    (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true ∧
    inst = instruction.BTYPE (imm, rs2, rs1, bop.BEQ)) ∨
  (∃ imm rs2 rs1,
    (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true ∧
    inst = instruction.BTYPE (imm, rs2, rs1, bop.BNE)) ∨
  (∃ imm rs2 rs1,
    (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true ∧
    inst = instruction.BTYPE (imm, rs2, rs1, bop.BLT)) ∨
  (∃ imm rs2 rs1,
    (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true ∧
    inst = instruction.BTYPE (imm, rs2, rs1, bop.BGE)) ∨
  (∃ imm rs2 rs1,
    (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true ∧
    inst = instruction.BTYPE (imm, rs2, rs1, bop.BLTU)) ∨
  (∃ imm rs2 rs1,
    (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true ∧
    inst = instruction.BTYPE (imm, rs2, rs1, bop.BGEU))

/-- Sail load constructor surface implemented by ZisK RV64IM. -/
def SailLoadInstruction (inst : instruction) : Prop :=
  (∃ imm rs1 rd, inst = instruction.LOAD (imm, rs1, rd, false, (1 : Int))) ∨
  (∃ imm rs1 rd, inst = instruction.LOAD (imm, rs1, rd, false, (2 : Int))) ∨
  (∃ imm rs1 rd, inst = instruction.LOAD (imm, rs1, rd, false, (4 : Int))) ∨
  (∃ imm rs1 rd, inst = instruction.LOAD (imm, rs1, rd, false, (8 : Int))) ∨
  (∃ imm rs1 rd, inst = instruction.LOAD (imm, rs1, rd, true, (1 : Int))) ∨
  (∃ imm rs1 rd, inst = instruction.LOAD (imm, rs1, rd, true, (2 : Int))) ∨
  (∃ imm rs1 rd, inst = instruction.LOAD (imm, rs1, rd, true, (4 : Int)))

/-- Sail store constructor surface implemented by ZisK RV64IM. -/
def SailStoreInstruction (inst : instruction) : Prop :=
  (∃ imm rs2 rs1, inst = instruction.STORE (imm, rs2, rs1, (1 : Int))) ∨
  (∃ imm rs2 rs1, inst = instruction.STORE (imm, rs2, rs1, (2 : Int))) ∨
  (∃ imm rs2 rs1, inst = instruction.STORE (imm, rs2, rs1, (4 : Int))) ∨
  (∃ imm rs2 rs1, inst = instruction.STORE (imm, rs2, rs1, (8 : Int)))

/-- Sail upper/jump constructor surface implemented by ZisK RV64IM. Sail's JAL
encoder accepts only aligned J-type immediates, represented by bit 0 = 0. -/
def SailUpperJumpInstruction (inst : instruction) : Prop :=
  (∃ imm rd, inst = instruction.UTYPE (imm, rd, uop.LUI)) ∨
  (∃ imm rd, inst = instruction.UTYPE (imm, rd, uop.AUIPC)) ∨
  (∃ imm rd,
    (Sail.BitVec.extractLsb imm 0 0 == (0#1 : BitVec 1)) = true ∧
    inst = instruction.JAL (imm, rd)) ∨
  (∃ imm rs1 rd, inst = instruction.JALR (imm, rs1, rd))

/-- Current production-ZisK FENCE subset: Sail generic FENCE with `fm = 0`,
`rs1 = x0`, and `rd = x0`; only pred/succ vary. -/
def SailSupportedFenceInstruction (inst : instruction) : Prop :=
  ∃ pred succ,
    inst =
      instruction.FENCE
        (0#4, pred, succ, regidx.Regidx 0#5, regidx.Regidx 0#5)

/-- Compatibility name for the already-closed ADD/SUB pilot surface. -/
def SailRegisterPilotInstruction (inst : instruction) : Prop :=
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.ADD)) ∨
  (∃ rs2 rs1 rd, inst = instruction.RTYPE (rs2, rs1, rd, rop.SUB))

/-- RV64IM constructor whitelist.  Later steps should add the remaining
register/immediate/load/store/branch/upper/jump/FENCE constructor families. -/
def SailRv64imInstruction (inst : instruction) : Prop :=
  SailRegisterAluInstruction inst ∨
  SailRegisterWordAluInstruction inst ∨
  SailMExtensionInstruction inst ∨
  SailImmediateAluInstruction inst ∨
  SailShiftImmediateInstruction inst ∨
  SailImmediateWordAluInstruction inst ∨
  SailBranchInstruction inst ∨
  SailLoadInstruction inst ∨
  SailStoreInstruction inst ∨
  SailUpperJumpInstruction inst ∨
  SailSupportedFenceInstruction inst

def SailPureRv64imInstruction (inst : instruction) : Prop :=
  SailRegisterAluInstruction inst ∨
  SailRegisterWordAluInstruction inst

/-- Sail-executable raw word for the currently covered RV64IM pilot surface. -/
def SailRv64imExecutableRaw (raw : RawInstruction) : Prop :=
  ∃ inst, SailDecodesTo raw inst ∧ SailEncodesTo inst raw ∧
    SailPureRv64imInstruction inst

def SailRv64imExecutableRawIn (state : SailState) (raw : RawInstruction) : Prop :=
  ∃ inst, SailDecodesToIn state raw inst ∧ SailEncodesToIn state inst raw ∧
    SailRv64imInstruction inst

theorem sail_rv64im_executable_raw_in_of_pure
    {raw : RawInstruction}
    (h : SailRv64imExecutableRaw raw) :
    ∀ state, SailRv64imExecutableRawIn state raw := by
  intro state
  rcases h with ⟨inst, h_decode, h_encode, h_inst⟩
  exact
    ⟨inst,
      sail_decodes_to_in_of_pure h_decode state,
      sail_encodes_to_in_of_pure h_encode state,
      h_inst.elim (fun h => .inl h) (fun h => .inr (.inl h))⟩

theorem sail_add_executable_implies_rv64im_executable
    {raw : RawInstruction} :
    SailAddExecutableRaw raw → SailRv64imExecutableRaw raw := by
  intro h
  rcases h with ⟨rs2, rs1, rd, h_decode, h_encode⟩
  exact
    ⟨instruction.RTYPE (rs2, rs1, rd, rop.ADD),
      h_decode, h_encode, .inl (.inl ⟨rs2, rs1, rd, rfl⟩)⟩

end ZiskFv.Completeness.SailDecode
