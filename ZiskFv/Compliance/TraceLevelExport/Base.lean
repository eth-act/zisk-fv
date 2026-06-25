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
import ZiskFv.Compliance
import ZiskFv.Compliance.Defects

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.EquivCore.Promises
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)
open Interaction

-- The M-extension row-computing defs are reducible/semireducible; structure-field
-- elaboration would otherwise whnf-reduce the full per-row ArithMul/ArithDiv
-- computation (a runaway). `seal` blocks that locally without touching the
-- committed construction proofs (which keep the defs as-is in their oleans).
seal mulwArow mulhuArow divuArow divuwArow remuArow remuwArow

set_option maxHeartbeats 8000000

/-- All-zero `Valid_Binary` — pure data, never consumed by any dispatcher arm
    (the RTYPE/ITYPE/W binary `OpEnvelope` arms carry it as an unused field).
    Building it with `0` lanes is non-vacuous: it imposes no constraint and
    makes no hypothesis contradictory. -/
noncomputable def zeroValidBinary : ZiskFv.Airs.Binary.Valid_Binary FGL FGL := by
  constructor <;> exact fun _ => 0

/-- `EnvNoKnownDefectFor sel` is the defect-exclusion fact for *every* `OpEnvelope`
    in the family carved out by the selector `sel`: every such env is outside all
    known-defect regions.  An OpEnvelope-route `stepStrong_<op>` proof instantiates
    this with the specific env it constructs (`sel` selecting exactly that arm's
    `OpEnvelope` constructor), feeding the result to
    `zisk_riscv_compliant_program_bus` instead of re-proving `NoKnownDefect`.

    For the non-defect OpEnvelope-route arms the selected constructor is never a
    defect constructor, so this is TRIVIALLY satisfiable (proved by `cases`/`simp`
    on the defect predicates) — the threaded hypothesis is non-vacuous.  The 7
    signed-M arms and FENCE do NOT use this selector-∀ shape (it would be FALSE for
    them — a malicious env matches the selector but is not `NoKnownDefect`); they
    instead ask `StepNoKnownDefect` for the GENUINE `NoKnownDefect (<op>EnvOf …)` of
    the SPECIFIC honest env they construct, satisfiable for any honest row because
    the defect predicates are narrowed to the exact forge witnesses (see
    `StepNoKnownDefect`). -/
def EnvNoKnownDefectFor
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r : ℕ}
    (sel : OpEnvelope state m r → Prop) : Prop :=
  ∀ env : OpEnvelope state m r, sel env → Defects.NoKnownDefect env

/-- The defect-constructor selector for an OpEnvelope-route arm is non-defect: every
    `OpEnvelope` it selects is `NoKnownDefect`.  This is the trivial discharge used
    to satisfy the threaded `StepNoKnownDefect` obligation for the 22 current
    non-defect arms (non-vacuous: the selected env exists and the fact is TRUE). -/
theorem envNoKnownDefectFor_of_nondefect
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r : ℕ}
    (sel : OpEnvelope state m r → Prop)
    (h : ∀ env, sel env →
      ¬ Defects.MaliciousSignedMulWitnessShape env ∧
      ¬ Defects.ArithDivDynamicWitnessShape env ∧
      Defects.FenceKnownGoodShape env) :
    EnvNoKnownDefectFor sel := by
  intro env hsel id
  obtain ⟨h1, h2, h3⟩ := h env hsel
  cases id with
  | arithMulSignedWitnessSoundness => exact h1
  | arithDivDynamicWitnessSoundness => exact h2
  | fenceIncomplete => simpa [Defects.Blocks] using h3

/-- Build a `MainRowProvenance m r` from the FIVE Main-row mode/control pins
    (`op`, `is_external_op`, `m32`, `set_pc`, `store_pc`) that the LUI/AUIPC/JAL
    `OpEnvelope` arms — and ONLY those arms' consumers — actually use.

    The U-type/JAL dispatch path (`lui_h_circuit_of_row_provenance` /
    `auipc_h_circuit_of_row_provenance` / the JAL analogue) reads back EXACTLY the
    five `*_eq` provenance fields built here from the supplied pins; it never reads
    `paddr`, `jmp_offset*`, `ind_width`, or any ROM-selector field.  Those
    non-consumed fields are filled with values **reverse-derived from the real row**
    (`(m.pc r).val`, `(m.jmp_offset1 r).val`, …), so every provenance equality is a
    TRUE statement about the committed row — the witness is genuinely non-vacuous,
    not a `False.elim` and not a fabricated decode claim.  Because `FGL = Fin
    GL_prime`, `natF`/`intF`/`boolF` are surjective (`Fin.cast_val_eq_self`), so the
    reverse-derived equalities close; the ROM rows are chosen to make the selector
    equations hold by `rfl`, and `mainRow.core := rowAt m r` makes `row_eq` `rfl`.

    Trust note: this carries NO trust beyond the five supplied pins (the existing
    honest `RowData_{lui,auipc,jal}` decode residuals).  It repackages the same five
    facts into the shape the `OpEnvelope` constructor requires; it adds no axiom and
    no new caller obligation. -/
noncomputable def mainRowProvenance_of_pins
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r : ℕ)
    (opc : ℕ) (isExt m32b setPcb storePcb : Bool)
    (h_op : m.op r = ZiskFv.Compliance.natF opc)
    (h_active : m.is_external_op r = ZiskFv.Compliance.boolF isExt)
    (h_m32 : m.m32 r = ZiskFv.Compliance.boolF m32b)
    (h_set_pc : m.set_pc r = ZiskFv.Compliance.boolF setPcb)
    (h_store_pc : m.store_pc r = ZiskFv.Compliance.boolF storePcb) :
    ZiskFv.Compliance.MainRowProvenance m r :=
  let er : ZiskFv.Compliance.MainExtractedRow :=
    { paddr := (m.pc r).val, op := opc
      aSrc := 0, aUseSpImm1 := 0, aOffsetImm0 := 0
      bSrc := 0, bUseSpImm1 := 0, bOffsetImm0 := 0
      store := 0, storeOffset := 0, storePc := storePcb, setPc := setPcb
      indWidth := (m.ind_width r).val, jmpOffset1 := (m.jmp_offset1 r).val
      jmpOffset2 := (m.jmp_offset2 r).val, isExternalOp := isExt, m32 := m32b }
  let rom : ZiskFv.AirsClean.Main.MainRomRow FGL :=
    { a_offset_imm0 := ZiskFv.Compliance.natF er.aOffsetImm0
      a_imm1 := ZiskFv.Compliance.natF er.aUseSpImm1
      b_offset_imm0 := ZiskFv.Compliance.natF er.bOffsetImm0
      b_imm1 := ZiskFv.Compliance.natF er.bUseSpImm1
      store_offset := ZiskFv.Compliance.intF er.storeOffset
      a_src_imm := ZiskFv.Compliance.selectorF er.aSrc ZiskFv.Compliance.ExtractedConst.srcImm
      a_src_mem := ZiskFv.Compliance.selectorF er.aSrc ZiskFv.Compliance.ExtractedConst.srcMem
      is_precompiled := 0
      b_src_imm := ZiskFv.Compliance.selectorF er.bSrc ZiskFv.Compliance.ExtractedConst.srcImm
      b_src_mem := ZiskFv.Compliance.selectorF er.bSrc ZiskFv.Compliance.ExtractedConst.srcMem
      store_mem := ZiskFv.Compliance.selectorF er.store ZiskFv.Compliance.ExtractedConst.storeMem
      store_ind := ZiskFv.Compliance.selectorF er.store ZiskFv.Compliance.ExtractedConst.storeInd
      b_src_ind := ZiskFv.Compliance.selectorF er.bSrc ZiskFv.Compliance.ExtractedConst.srcInd
      a_src_reg := ZiskFv.Compliance.selectorF er.aSrc ZiskFv.Compliance.ExtractedConst.srcReg
      b_src_reg := ZiskFv.Compliance.selectorF er.bSrc ZiskFv.Compliance.ExtractedConst.srcReg
      store_reg := ZiskFv.Compliance.selectorF er.store ZiskFv.Compliance.ExtractedConst.storeReg
      addr0 := 0, addr1 := 0, addr2 := 0, main_step := 0 }
  { mainRow := { core := ZiskFv.AirsClean.Main.rowAt m r, rom := rom }
    extractedRow := er
    row_eq := rfl
    op_eq := by simpa [er, ZiskFv.Compliance.natF] using h_op
    is_external_op_eq := by simpa [er] using h_active
    m32_eq := by simpa [er] using h_m32
    ind_width_eq := by
      show m.ind_width r = ZiskFv.Compliance.natF _; simp [er, ZiskFv.Compliance.natF]
    set_pc_eq := by simpa [er] using h_set_pc
    store_pc_eq := by simpa [er] using h_store_pc
    jmp_offset1_eq := by
      show m.jmp_offset1 r = ZiskFv.Compliance.intF _; simp [er, ZiskFv.Compliance.intF]
    jmp_offset2_eq := by
      show m.jmp_offset2 r = ZiskFv.Compliance.intF _; simp [er, ZiskFv.Compliance.intF]
    paddr_eq := by simp [er]
    a_offset_imm0_eq := rfl, a_imm1_eq := rfl, b_offset_imm0_eq := rfl, b_imm1_eq := rfl
    store_offset_eq := rfl, a_src_imm_eq := rfl, a_src_mem_eq := rfl, a_src_reg_eq := rfl
    b_src_imm_eq := rfl, b_src_mem_eq := rfl, b_src_ind_eq := rfl, b_src_reg_eq := rfl
    store_mem_eq := rfl, store_ind_eq := rfl, store_reg_eq := rfl }

/-- Constant `Var` for a concrete `MainRowWithRom` row: every leaf field is a
    `.const` expression carrying the concrete value, so for ANY environment
    `eval env (mainConstVar row) = row` definitionally (see
    `eval_mainConstVar`).  This lets the store `OpEnvelope` arms supply the
    `{mainRowVar}`/`{mainEnv}` implicit binders the constructor requires while
    keeping the `eval mainEnv mainRowVar`-shaped hypotheses equal to the concrete
    trace row `mainRowWithRomSt trace i` — the same facts
    `construction_<store>_sound` proves.  Repackaging only: carries no trust. -/
@[reducible]
noncomputable def mainConstVar (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL) :
    Var ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  { core :=
      { a_0 := .const row.core.a_0, a_1 := .const row.core.a_1
        b_0 := .const row.core.b_0, b_1 := .const row.core.b_1
        c_0 := .const row.core.c_0, c_1 := .const row.core.c_1
        flag := .const row.core.flag, pc := .const row.core.pc
        is_external_op := .const row.core.is_external_op, op := .const row.core.op
        m32 := .const row.core.m32, ind_width := .const row.core.ind_width
        set_pc := .const row.core.set_pc, jmp_offset1 := .const row.core.jmp_offset1
        jmp_offset2 := .const row.core.jmp_offset2, store_pc := .const row.core.store_pc
        im_high_degree_2 := .const row.core.im_high_degree_2
        segment_l1 := .const row.core.segment_l1 }
    rom :=
      { a_offset_imm0 := .const row.rom.a_offset_imm0, a_imm1 := .const row.rom.a_imm1
        b_offset_imm0 := .const row.rom.b_offset_imm0, b_imm1 := .const row.rom.b_imm1
        store_offset := .const row.rom.store_offset, a_src_imm := .const row.rom.a_src_imm
        a_src_mem := .const row.rom.a_src_mem, is_precompiled := .const row.rom.is_precompiled
        b_src_imm := .const row.rom.b_src_imm, b_src_mem := .const row.rom.b_src_mem
        store_mem := .const row.rom.store_mem, store_ind := .const row.rom.store_ind
        b_src_ind := .const row.rom.b_src_ind, a_src_reg := .const row.rom.a_src_reg
        b_src_reg := .const row.rom.b_src_reg, store_reg := .const row.rom.store_reg
        addr0 := .const row.rom.addr0, addr1 := .const row.rom.addr1
        addr2 := .const row.rom.addr2, main_step := .const row.rom.main_step } }

/-- `eval env (mainConstVar row) = row` for any `env`: every leaf is a `.const`,
    so `eval` distributes to the carried concrete value. -/
@[simp]
theorem eval_mainConstVar (env : Environment FGL)
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL) :
    eval env (mainConstVar row) = row := by
  simp only [mainConstVar, ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  cases row with
  | mk core rom => cases core; cases rom; rfl

/-- Constant `Var` for a concrete `MemRow` provider row: every leaf field is a
    `.const` expression carrying the concrete value, so for ANY environment
    `eval env (memConstVar row) = row` definitionally (see `eval_memConstVar`).
    This is the Mem-provider analogue of `mainConstVar`: it supplies the
    `{memRowVar}`/`{memEnv}` implicit binders the load `OpEnvelope` arms require
    while keeping the `eval memEnv memRowVar`-shaped hypotheses equal to the
    concrete Mem provider row `ZiskFv.AirsClean.Mem.rowAt mem r_mem`.  Repackaging
    only: carries no trust. -/
@[reducible]
noncomputable def memConstVar (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Var ZiskFv.AirsClean.Mem.MemRow FGL :=
  { addr := .const row.addr, step := .const row.step, sel := .const row.sel
    addr_changes := .const row.addr_changes, step_dual := .const row.step_dual
    sel_dual := .const row.sel_dual, value_0 := .const row.value_0
    value_1 := .const row.value_1, wr := .const row.wr
    previous_step := .const row.previous_step, increment_0 := .const row.increment_0
    increment_1 := .const row.increment_1, read_same_addr := .const row.read_same_addr }

/-- `eval env (memConstVar row) = row` for any `env`: every leaf is a `.const`,
    so `eval` distributes to the carried concrete value. -/
@[simp]
theorem eval_memConstVar (env : Environment FGL)
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    eval env (memConstVar row) = row := by
  simp only [memConstVar, ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  cases row
  rfl

/-- Placeholder environment used to instantiate the load `OpEnvelope` arms'
    `{mainEnv}`/`{memEnv}` implicit binders; `eval_mainConstVar`/`eval_memConstVar`
    make the choice irrelevant. -/
def loadEvalEnv : Environment FGL :=
  { get := fun _ => 0, data := fun _ _ => #[] }

/-- The Main-side `b` (memory READ) interaction message of the concrete load
    Main row, evaluated under `loadEvalEnv` — the LHS counterpart of `loadMemMsg`.
    Used to phrase the load `h_msg` provider-linkage residual without exposing the
    `OpEnvelope` arms' implicit eval binders. -/
@[reducible]
noncomputable def loadMainMsg (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL) :
    Array FGL :=
  (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted (-1 : Expression FGL)
      (ZiskFv.AirsClean.Main.bMemMessageExpr (mainConstVar mainRow))).toRaw).eval
      loadEvalEnv).msg

/-- The Mem-provider interaction message of the concrete provider row, evaluated
    under `loadEvalEnv` — the RHS counterpart of `loadMainMsg`. -/
@[reducible]
noncomputable def loadMemMsg (memRow : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Array FGL :=
  (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted (1 : Expression FGL)
      (ZiskFv.AirsClean.Mem.memBusMessageExpr (memConstVar memRow))).toRaw).eval
      loadEvalEnv).msg

end ZiskFv.Compliance
