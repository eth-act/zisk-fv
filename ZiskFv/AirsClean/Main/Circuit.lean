import ZiskFv.AirsClean.Main.Constraints
import ZiskFv.AirsClean.Main.Soundness
import ZiskFv.AirsClean.Main.Bridge
import ZiskFv.AirsClean.CompletenessHelpers
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Main Clean Component

Packages the Main AIR's per-row constraints plus its assume-side operation-bus
emission as a Clean `Air.Flat.Component`.

The base `Constraints.main` definition remains the extracted nine F-typed
constraints. This component uses `mainWithOpBus`, which appends the
PIL-faithful operation-bus emission with multiplicity `-is_external_op`.

## Trust note

No axioms. Completeness is a constructibility claim for rows equal to the
honest builders below: the builders choose one of the three Main execution
shapes forced by the local constraints and compute the dependent `flag`,
`is_external_op`, `op`, `c_*`, and `set_pc` columns. The ROM-backed builders
also copy the selected program row into the ROM lookup columns and pack the
instruction flags. Cross-row PC continuity and program semantics remain outside
these row-local proofs.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean (boolF)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program romStaticTable)

/-- Columns of the plain Main row that are unconstrained by the local
    `mainWithOpBus` constraint slice. -/
structure MainFreeCols where
  a_0 : FGL
  a_1 : FGL
  b_0 : FGL
  b_1 : FGL
  pc : FGL
  m32 : FGL
  ind_width : FGL
  jmp_offset1 : FGL
  jmp_offset2 : FGL
  store_pc : FGL
  im_high_degree_2 : FGL
  segment_l1 : FGL

/-- The three Main execution shapes forced by the local internal-op
    constraints. External rows leave `op` and `c_*` free; internal op 0 sets
    the flag and clears `c_*`; internal op 1 clears the flag and copies `b` to
    `c`. -/
inductive MainExecKind
  | external (op : FGL) (flag : Bool) (c_0 c_1 set_pc : FGL)
  | internalFlag
  | internalCopyB (set_pc : FGL)

/-- Honest row for the plain Main circuit. -/
def mainRowOf : MainExecKind → MainFreeCols → MainRow FGL
  | .external op flag c_0 c_1 set_pc, free =>
      { a_0 := free.a_0
        a_1 := free.a_1
        b_0 := free.b_0
        b_1 := free.b_1
        c_0 := c_0
        c_1 := c_1
        flag := boolF flag
        pc := free.pc
        is_external_op := 1
        op := op
        m32 := free.m32
        ind_width := free.ind_width
        set_pc := if flag then 0 else set_pc
        jmp_offset1 := free.jmp_offset1
        jmp_offset2 := free.jmp_offset2
        store_pc := free.store_pc
        im_high_degree_2 := free.im_high_degree_2
        segment_l1 := free.segment_l1 }
  | .internalFlag, free =>
      { a_0 := free.a_0
        a_1 := free.a_1
        b_0 := free.b_0
        b_1 := free.b_1
        c_0 := 0
        c_1 := 0
        flag := 1
        pc := free.pc
        is_external_op := 0
        op := 0
        m32 := free.m32
        ind_width := free.ind_width
        set_pc := 0
        jmp_offset1 := free.jmp_offset1
        jmp_offset2 := free.jmp_offset2
        store_pc := free.store_pc
        im_high_degree_2 := free.im_high_degree_2
        segment_l1 := free.segment_l1 }
  | .internalCopyB set_pc, free =>
      { a_0 := free.a_0
        a_1 := free.a_1
        b_0 := free.b_0
        b_1 := free.b_1
        c_0 := free.b_0
        c_1 := free.b_1
        flag := 0
        pc := free.pc
        is_external_op := 0
        op := 1
        m32 := free.m32
        ind_width := free.ind_width
        set_pc := set_pc
        jmp_offset1 := free.jmp_offset1
        jmp_offset2 := free.jmp_offset2
        store_pc := free.store_pc
        im_high_degree_2 := free.im_high_degree_2
        segment_l1 := free.segment_l1 }

def circuit : GeneralFormalCircuit FGL MainRow unit :=
  { mainWithOpBusElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers rows built from one of the three local Main
    -- execution shapes; unconstrained data columns remain free.
    ProverAssumptions := fun row _ _ =>
      ∃ kind free, row = mainRowOf kind free
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_holds
        exact ⟨ by simpa [sub_eq_add_neg] using h0
              , by simpa [sub_eq_add_neg] using h1
              , by simpa [sub_eq_add_neg] using h2
              , by simpa [sub_eq_add_neg] using h3
              , by simpa [sub_eq_add_neg] using h4
              , by simpa [sub_eq_add_neg] using h5
              , by simpa [sub_eq_add_neg] using h6
              , by simpa [sub_eq_add_neg] using h7
              , by simpa [sub_eq_add_neg] using h8 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start_core
      simp only [mainWithOpBus, main, circuit_norm, opBusMessageExpr,
        OpBusChannel]
      obtain ⟨kind, free, hrow⟩ := h_assumptions
      rw [hrow] at h_input
      simp only [circuit_norm] at h_input
      cases kind with
      | external op flag c_0 c_1 set_pc =>
        simp [mainRowOf, boolF] at h_input ⊢
        obtain ⟨h_a_0, h_a_1, h_b_0, h_b_1, h_c_0, h_c_1, h_flag, h_pc,
          h_is_external_op, h_op, h_m32, h_ind_width, h_set_pc, h_jmp_offset1,
          h_jmp_offset2, h_store_pc, h_im_high_degree_2, h_segment_l1⟩ := h_input
        cases flag <;>
          simp [h_c_0, h_c_1, h_flag, h_is_external_op, h_op, h_set_pc]
      | internalFlag =>
        simp [mainRowOf] at h_input ⊢
        obtain ⟨h_a_0, h_a_1, h_b_0, h_b_1, h_c_0, h_c_1, h_flag, h_pc,
          h_is_external_op, h_op, h_m32, h_ind_width, h_set_pc, h_jmp_offset1,
          h_jmp_offset2, h_store_pc, h_im_high_degree_2, h_segment_l1⟩ := h_input
        simp [h_c_0, h_c_1, h_flag, h_is_external_op, h_op, h_set_pc]
      | internalCopyB set_pc =>
        simp [mainRowOf] at h_input ⊢
        obtain ⟨h_a_0, h_a_1, h_b_0, h_b_1, h_c_0, h_c_1, h_flag, h_pc,
          h_is_external_op, h_op, h_m32, h_ind_width, h_set_pc, h_jmp_offset1,
          h_jmp_offset2, h_store_pc, h_im_high_degree_2, h_segment_l1⟩ := h_input
        simp [h_b_0, h_b_1, h_c_0, h_c_1, h_flag, h_is_external_op, h_op] }

def component : Air.Flat.Component FGL := ⟨ circuit ⟩

/-! ## Main with ROM + memory-bus consumer emissions -/

/-- The 15 instruction-flag bits packed into the ROM `flags` field. -/
structure RomFlagBits where
  a_src_imm : Bool
  a_src_mem : Bool
  is_precompiled : Bool
  b_src_imm : Bool
  b_src_mem : Bool
  is_external_op : Bool
  store_pc : Bool
  store_mem : Bool
  store_ind : Bool
  set_pc : Bool
  m32 : Bool
  b_src_ind : Bool
  a_src_reg : Bool
  b_src_reg : Bool
  store_reg : Bool

/-- Concrete ROM-flag packing, matching `romFlagsExpr`. -/
def packFlags (bits : RomFlagBits) : FGL :=
  1
  + 2 * boolF bits.a_src_imm
  + 4 * boolF bits.a_src_mem
  + 8 * boolF bits.is_precompiled
  + 16 * boolF bits.b_src_imm
  + 32 * boolF bits.b_src_mem
  + 64 * boolF bits.is_external_op
  + 128 * boolF bits.store_pc
  + 256 * boolF bits.store_mem
  + 512 * boolF bits.store_ind
  + 1024 * boolF bits.set_pc
  + 2048 * boolF bits.m32
  + 4096 * boolF bits.b_src_ind
  + 8192 * boolF bits.a_src_reg
  + 16384 * boolF bits.b_src_reg
  + 32768 * boolF bits.store_reg

/-- Free witness columns in the ROM-backed Main row. Program-derived columns
    and flag bits are copied from the selected program row and `RomFlagBits`;
    dependent `c_*`/`flag` columns are selected by `MainRomExecKind`. -/
structure MainRomFreeCols where
  a_0 : FGL
  a_1 : FGL
  b_0 : FGL
  b_1 : FGL
  im_high_degree_2 : FGL
  segment_l1 : FGL
  addr0 : FGL
  addr1 : FGL
  addr2 : FGL
  main_step : FGL

/-- Main execution shapes for rows whose instruction data comes from the ROM
    program row. The operation code itself is copied from the selected ROM
    message, so internal cases require coherence side-conditions on that
    message. -/
inductive MainRomExecKind
  | external (flag : Bool) (c_0 c_1 : FGL)
  | internalFlag
  | internalCopyB

namespace MainRomExecKind

/-- Semantic coherence between the ROM flag bits, the selected program row, and
    the local Main execution shape. -/
@[reducible]
def Coherent (msg : ZiskFv.Channels.ZiskRomBus.ZiskRomMessage FGL)
    (bits : RomFlagBits) : MainRomExecKind → Prop
  | external flag _ _ =>
      bits.is_external_op = true ∧ (flag = true → bits.set_pc = false)
  | internalFlag =>
      bits.is_external_op = false ∧ msg.op = 0 ∧ bits.set_pc = false
  | internalCopyB =>
      bits.is_external_op = false ∧ msg.op = 1

end MainRomExecKind

/-- Honest row for the ROM-backed Main circuits. The ROM lookup fields copy the
    selected program message; runtime operand/address columns remain free. -/
def mainRomRowOf (msg : ZiskFv.Channels.ZiskRomBus.ZiskRomMessage FGL)
    (bits : RomFlagBits) (kind : MainRomExecKind) (free : MainRomFreeCols) :
    MainRowWithRom FGL :=
  { core :=
      { a_0 := free.a_0
        a_1 := free.a_1
        b_0 := free.b_0
        b_1 := free.b_1
        c_0 :=
          match kind with
          | .external _ c_0 _ => c_0
          | .internalFlag => 0
          | .internalCopyB => free.b_0
        c_1 :=
          match kind with
          | .external _ _ c_1 => c_1
          | .internalFlag => 0
          | .internalCopyB => free.b_1
        flag :=
          match kind with
          | .external flag _ _ => boolF flag
          | .internalFlag => 1
          | .internalCopyB => 0
        pc := msg.line
        is_external_op := boolF bits.is_external_op
        op := msg.op
        m32 := boolF bits.m32
        ind_width := msg.ind_width
        set_pc := boolF bits.set_pc
        jmp_offset1 := msg.jmp_offset1
        jmp_offset2 := msg.jmp_offset2
        store_pc := boolF bits.store_pc
        im_high_degree_2 := free.im_high_degree_2
        segment_l1 := free.segment_l1 }
    rom :=
      { a_offset_imm0 := msg.a_offset_imm0
        a_imm1 := msg.a_imm1
        b_offset_imm0 := msg.b_offset_imm0
        b_imm1 := msg.b_imm1
        store_offset := msg.store_offset
        a_src_imm := boolF bits.a_src_imm
        a_src_mem := boolF bits.a_src_mem
        is_precompiled := boolF bits.is_precompiled
        b_src_imm := boolF bits.b_src_imm
        b_src_mem := boolF bits.b_src_mem
        store_mem := boolF bits.store_mem
        store_ind := boolF bits.store_ind
        b_src_ind := boolF bits.b_src_ind
        a_src_reg := boolF bits.a_src_reg
        b_src_reg := boolF bits.b_src_reg
        store_reg := boolF bits.store_reg
        addr0 := free.addr0
        addr1 := free.addr1
        addr2 := free.addr2
        main_step := free.main_step } }

/-- The extra boolean obligations introduced by `mainWithRom`, beyond the
    original nine Main constraints. These are not part of Main's per-row
    soundness `Spec`; a future honest-prover completeness project may consume
    them separately. -/
@[reducible]
def RomBoolSpec (row : MainRowWithRom FGL) : Prop :=
  row.core.m32 * (1 + -row.core.m32) = 0
  ∧ row.core.set_pc * (1 + -row.core.set_pc) = 0
  ∧ row.core.store_pc * (1 + -row.core.store_pc) = 0
  ∧ row.rom.a_src_imm * (1 + -row.rom.a_src_imm) = 0
  ∧ row.rom.a_src_mem * (1 + -row.rom.a_src_mem) = 0
  ∧ row.rom.is_precompiled * (1 + -row.rom.is_precompiled) = 0
  ∧ row.rom.b_src_imm * (1 + -row.rom.b_src_imm) = 0
  ∧ row.rom.b_src_mem * (1 + -row.rom.b_src_mem) = 0
  ∧ row.rom.store_mem * (1 + -row.rom.store_mem) = 0
  ∧ row.rom.store_ind * (1 + -row.rom.store_ind) = 0
  ∧ row.rom.b_src_ind * (1 + -row.rom.b_src_ind) = 0
  ∧ row.rom.a_src_reg * (1 + -row.rom.a_src_reg) = 0
  ∧ row.rom.b_src_reg * (1 + -row.rom.b_src_reg) = 0
  ∧ row.rom.store_reg * (1 + -row.rom.store_reg) = 0

/-- Soundness wrapper for Main plus ROM lookup plus memory-bus consumer
    emissions. -/
theorem mainWithRomAndMemBus_soundness (length : ℕ) (program : Program length) :
    GeneralFormalCircuit.Soundness FGL
      (mainWithRomAndMemBusElaborated length program)
      (fun _ _ => True)
      (fun row _ _ => Spec row.core) := by
  circuit_proof_start
  refine ⟨?_, ?_⟩
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, _h_m32, _h_set_pc,
      _h_store_pc, _h_a_src_imm, _h_a_src_mem, _h_is_precompiled,
      _h_b_src_imm, _h_b_src_mem, _h_store_mem, _h_store_ind, _h_b_src_ind,
      _h_a_src_reg, _h_b_src_reg, _h_store_reg, _h_rom⟩ := h_holds
    exact ⟨ by simpa [sub_eq_add_neg] using h0
          , by simpa [sub_eq_add_neg] using h1
          , by simpa [sub_eq_add_neg] using h2
          , by simpa [sub_eq_add_neg] using h3
          , by simpa [sub_eq_add_neg] using h4
          , by simpa [sub_eq_add_neg] using h5
          , by simpa [sub_eq_add_neg] using h6
          , by simpa [sub_eq_add_neg] using h7
          , by simpa [sub_eq_add_neg] using h8 ⟩
  · simp only [MemBusChannel, circuit_norm]

/-! ### Structural ROM projections for T4

These lemmas expose obligations already asserted by
`mainWithRomAndMemBus`. They are intentionally narrower than a
"well-formed program" promise: the ROM lookup conclusion is exact
membership in the program-parameterised `romStaticTable`, and the boolean
facts are only the per-row flag boolean assertions present in `main.pil`.
-/

theorem romBoolSpec_of_mainWithRomAndMemBus_constraints
    (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env
        ((mainWithRomAndMemBus length program row).operations offset)) :
    env (row.core.m32 * (1 - row.core.m32)) = 0
  ∧ env (row.core.set_pc * (1 - row.core.set_pc)) = 0
  ∧ env (row.core.store_pc * (1 - row.core.store_pc)) = 0
  ∧ env (row.rom.a_src_imm * (1 - row.rom.a_src_imm)) = 0
  ∧ env (row.rom.a_src_mem * (1 - row.rom.a_src_mem)) = 0
  ∧ env (row.rom.is_precompiled * (1 - row.rom.is_precompiled)) = 0
  ∧ env (row.rom.b_src_imm * (1 - row.rom.b_src_imm)) = 0
  ∧ env (row.rom.b_src_mem * (1 - row.rom.b_src_mem)) = 0
  ∧ env (row.rom.store_mem * (1 - row.rom.store_mem)) = 0
  ∧ env (row.rom.store_ind * (1 - row.rom.store_ind)) = 0
  ∧ env (row.rom.b_src_ind * (1 - row.rom.b_src_ind)) = 0
  ∧ env (row.rom.a_src_reg * (1 - row.rom.a_src_reg)) = 0
  ∧ env (row.rom.b_src_reg * (1 - row.rom.b_src_reg)) = 0
  ∧ env (row.rom.store_reg * (1 - row.rom.store_reg)) = 0 := by
  simp only [mainWithRomAndMemBus, mainWithRom, main, circuit_norm] at h_holds
  exact ⟨ h_holds.1 (row.core.m32 * (1 - row.core.m32)) (by simp)
        , h_holds.1 (row.core.set_pc * (1 - row.core.set_pc)) (by simp)
        , h_holds.1 (row.core.store_pc * (1 - row.core.store_pc)) (by simp)
        , h_holds.1 (row.rom.a_src_imm * (1 - row.rom.a_src_imm)) (by simp)
        , h_holds.1 (row.rom.a_src_mem * (1 - row.rom.a_src_mem)) (by simp)
        , h_holds.1 (row.rom.is_precompiled * (1 - row.rom.is_precompiled)) (by simp)
        , h_holds.1 (row.rom.b_src_imm * (1 - row.rom.b_src_imm)) (by simp)
        , h_holds.1 (row.rom.b_src_mem * (1 - row.rom.b_src_mem)) (by simp)
        , h_holds.1 (row.rom.store_mem * (1 - row.rom.store_mem)) (by simp)
        , h_holds.1 (row.rom.store_ind * (1 - row.rom.store_ind)) (by simp)
        , h_holds.1 (row.rom.b_src_ind * (1 - row.rom.b_src_ind)) (by simp)
        , h_holds.1 (row.rom.a_src_reg * (1 - row.rom.a_src_reg)) (by simp)
        , h_holds.1 (row.rom.b_src_reg * (1 - row.rom.b_src_reg)) (by simp)
        , h_holds.1 (row.rom.store_reg * (1 - row.rom.store_reg)) (by simp) ⟩

/-- Project the ROM lookup carried by `mainWithRomAndMemBus` constraints to
    exact program-ROM membership for the evaluated row message. -/
theorem romSpec_of_mainWithRomAndMemBus_constraints
    (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env
        ((mainWithRomAndMemBus length program row).operations offset)) :
    (romStaticTable length program).Spec (eval env (romMessageExpr row)) := by
  simp only [mainWithRomAndMemBus, mainWithRom, main, circuit_norm] at h_holds
  let table := Table.fromStatic (romStaticTable length program)
  let lookup : Lookup FGL := { table := table.toRaw, entry := toElements (romMessageExpr row) }
  have h_contains : lookup.Contains env := by
    simpa [lookup, table] using h_holds.2
  have h_sound : lookup.Soundness env :=
    lookup.table.imply_soundness _ _ h_contains
  have h_table_sound :
      table.Soundness (env.data.getTable table) (eval env (romMessageExpr row)) := by
    exact (Lookup.soundess_def table env (romMessageExpr row)).mp h_sound
  simpa [table, Table.fromStatic, StaticTable.toTable] using h_table_sound

/-- Completeness for Main plus ROM lookup and memory-bus emissions. Rows are
    constructible when they select a concrete program entry, provide flag bits
    whose packed value equals that entry's ROM `flags`, choose a coherent local
    Main execution shape, and otherwise fill only unconstrained runtime columns. -/
theorem mainWithRomAndMemBus_completeness (length : ℕ) (program : Program length) :
    GeneralFormalCircuit.Completeness FGL
      (mainWithRomAndMemBusElaborated length program)
      (fun row _ _ =>
        ∃ i bits kind free,
          (program i).flags = packFlags bits
          ∧ MainRomExecKind.Coherent (program i) bits kind
          ∧ row = mainRomRowOf (program i) bits kind free)
      (fun _ _ _ => True) := by
  circuit_proof_start_core
  simp only [mainWithRomAndMemBus, mainWithRom, main, circuit_norm,
    romMessageExpr, romFlagsExpr, aMemMessageExpr, bMemMessageExpr,
    cMemMessageExpr, aMemOpExpr, bMemOpExpr, cMemOpExpr, storeValueLoExpr,
    storeValueHiExpr, MemBusChannel, Lookup.completeness_def]
  obtain ⟨i, bits, kind, free, h_flags, h_coherent, hrow⟩ := h_assumptions
  rw [hrow] at h_input
  simp only [circuit_norm] at h_input
  cases kind with
  | external flag c_0 c_1 =>
    rcases h_coherent with ⟨h_ext, h_setpc⟩
    cases flag
    · simp_all [mainRomRowOf, packFlags, romStaticTable, boolF]
      exact ⟨i, by
        rw [ZiskFv.Channels.ZiskRomBus.ZiskRomMessage.mk.injEq]
        simp [h_flags]⟩
    · have h_setpc_false : bits.set_pc = false := h_setpc rfl
      simp_all [mainRomRowOf, packFlags, romStaticTable, boolF]
      exact ⟨i, by
        rw [ZiskFv.Channels.ZiskRomBus.ZiskRomMessage.mk.injEq]
        simp [h_flags]⟩
  | internalFlag =>
    rcases h_coherent with ⟨h_ext, h_op, h_setpc⟩
    simp_all [mainRomRowOf, packFlags, romStaticTable, boolF]
    exact ⟨i, by
      rw [ZiskFv.Channels.ZiskRomBus.ZiskRomMessage.mk.injEq]
      simp [h_flags, h_op]⟩
  | internalCopyB =>
    rcases h_coherent with ⟨h_ext, h_op⟩
    simp_all [mainRomRowOf, packFlags, romStaticTable, boolF]
    exact ⟨i, by
      rw [ZiskFv.Channels.ZiskRomBus.ZiskRomMessage.mk.injEq]
      simp [h_flags, h_op]⟩

/-- Main as a Clean `GeneralFormalCircuit` exposing the ROM lookup and
    the 3 memory-bus consumer emissions. Completeness covers rows built from a
    selected program entry, coherent ROM flag bits, and one local Main execution
    shape. -/
def circuitWithRomAndMemBus
    (length : ℕ) (program : Program length) :
    GeneralFormalCircuit FGL MainRowWithRom unit :=
  { mainWithRomAndMemBusElaborated length program with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row.core
    -- Completeness covers rows whose ROM lookup columns are copied from a
    -- concrete program entry and whose packed flag bits match that entry.
    ProverAssumptions := fun row _ _ =>
      ∃ i bits kind free,
        (program i).flags = packFlags bits
        ∧ MainRomExecKind.Coherent (program i) bits kind
        ∧ row = mainRomRowOf (program i) bits kind free
    ProverSpec := fun _ _ _ => True
    soundness := mainWithRomAndMemBus_soundness length program
    completeness := mainWithRomAndMemBus_completeness length program }

/-- Main as a Clean `Air.Flat.Component` exposing the ROM lookup and
    the 3 memory-bus consumer interactions. Used by the full Clean
    ensemble assembly. -/
def componentWithRomAndMemBus
    (length : ℕ) (program : Program length) :
    Air.Flat.Component FGL :=
  ⟨ circuitWithRomAndMemBus length program ⟩

/-! ### Unified Main component for the full T7 ensemble -/

/-- Soundness wrapper for the unified Main component. The added
    operation-bus emission is an exposed channel interaction, not a new
    Main constraint; the row-local Main/ROM/memory soundness is inherited
    from `mainWithRomAndMemBus_soundness`. -/
theorem mainWithRomMemAndOpBus_soundness (length : ℕ) (program : Program length) :
    GeneralFormalCircuit.Soundness FGL
      (mainWithRomMemAndOpBusElaborated length program)
      (fun _ _ => True)
      (fun row _ _ => Spec row.core) := by
  intro offset env input_var input h_input h_assumptions h_holds
  have h_mem :
      ConstraintsHold.Soundness env
        ((mainWithRomAndMemBus length program input_var).operations offset) := by
    simpa [mainWithRomMemAndOpBus, circuit_norm] using h_holds
  have h_sound :=
    mainWithRomAndMemBus_soundness length program
      offset env input_var input h_input h_assumptions h_mem
  simpa [mainWithRomMemAndOpBus, circuit_norm, OpBusChannel, MemBusChannel] using h_sound

/-- Completeness wrapper for the unified ROM/memory/op-bus Main component.
    The added operation-bus emission has a trivial channel guarantee, so the
    ROM/memory constructibility theorem supplies the row-local work. -/
theorem mainWithRomMemAndOpBus_completeness (length : ℕ) (program : Program length) :
    GeneralFormalCircuit.Completeness FGL
      (mainWithRomMemAndOpBusElaborated length program)
      (fun row _ _ =>
        ∃ i bits kind free,
          (program i).flags = packFlags bits
          ∧ MainRomExecKind.Coherent (program i) bits kind
          ∧ row = mainRomRowOf (program i) bits kind free)
      (fun _ _ _ => True) := by
  intro offset env input_var h_env input h_input h_assumptions
  have h_base :=
    mainWithRomAndMemBus_completeness length program offset env input_var
      (by
        simp [mainWithRomMemAndOpBus, circuit_norm] at h_env
        exact h_env)
      input h_input h_assumptions
  simpa [mainWithRomMemAndOpBus, circuit_norm, OpBusChannel, MemBusChannel] using h_base

/-- Main as one Clean `GeneralFormalCircuit` exposing both Main channel
    surfaces from the same `MainRowWithRom`: the operation-bus consumer
    interaction and the ROM/memory-bus consumer interactions. -/
def circuitWithRomMemAndOpBus
    (length : ℕ) (program : Program length) :
    GeneralFormalCircuit FGL MainRowWithRom unit :=
  { mainWithRomMemAndOpBusElaborated length program with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row.core
    -- Completeness uses the same ROM-backed honest-row predicate as
    -- `circuitWithRomAndMemBus`; the added op-bus emission is structural.
    ProverAssumptions := fun row _ _ =>
      ∃ i bits kind free,
        (program i).flags = packFlags bits
        ∧ MainRomExecKind.Coherent (program i) bits kind
        ∧ row = mainRomRowOf (program i) bits kind free
    ProverSpec := fun _ _ _ => True
    soundness := mainWithRomMemAndOpBus_soundness length program
    completeness := mainWithRomMemAndOpBus_completeness length program }

/-- Unified Main component used by the T7 full ensemble. -/
def componentWithRomMemAndOpBus
    (length : ℕ) (program : Program length) :
    Air.Flat.Component FGL :=
  ⟨ circuitWithRomMemAndOpBus length program ⟩

/-- Project the generic Clean component `Spec` for the unified
    ROM/memory/op-bus Main component to the concrete Main-row `Spec`. -/
theorem componentWithRomMemAndOpBus_spec
    (length : ℕ) (program : Program length) (env : Environment FGL) :
    (componentWithRomMemAndOpBus length program).Spec env =
      Spec ((componentWithRomMemAndOpBus length program).rowInput env).core := by
  rfl

theorem componentWithRomMemAndOpBus_interactionsWith_memBus
    (length : ℕ) (program : Program length) :
    (componentWithRomMemAndOpBus length program).operations.interactionsWith
        MemBusChannel.toRaw =
      [ ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_reg))
            (aMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_ind
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_reg))
            (bMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.store_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_ind
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_reg))
            (cMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw,
      [ ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_reg))
            (aMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_ind
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_reg))
            (bMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.store_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_ind
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_reg))
            (cMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw) ]⟩ ∈
    (componentWithRomMemAndOpBus length program).exposedChannels
  simp [componentWithRomMemAndOpBus, circuitWithRomMemAndOpBus,
    mainWithRomMemAndOpBusElaborated, Component.exposedChannels, expose,
    List.map_cons, List.map_nil]

theorem componentWithRomMemAndOpBus_interactionsWith_opBus
    (length : ℕ) (program : Program length) :
    (componentWithRomMemAndOpBus length program).operations.interactionsWith
        OpBusChannel.toRaw =
      [((OpBusChannel.emitted
          (-(componentWithRomMemAndOpBus length program).rowInputVar.core.is_external_op)
          (opBusMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar.core)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.emitted
          (-(componentWithRomMemAndOpBus length program).rowInputVar.core.is_external_op)
          (opBusMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar.core)).toRaw)]⟩ ∈
    (componentWithRomMemAndOpBus length program).exposedChannels
  simp [componentWithRomMemAndOpBus, circuitWithRomMemAndOpBus,
    mainWithRomMemAndOpBusElaborated, Component.exposedChannels, expose,
    List.map_cons, List.map_nil]

theorem is_external_op_boolean_of_mainWithRomMemAndOpBus_constraints
    (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env
        ((mainWithRomMemAndOpBus length program row).operations offset)) :
    env (row.core.is_external_op * (1 - row.core.is_external_op)) = 0 := by
  simp only [mainWithRomMemAndOpBus, mainWithRomAndMemBus, mainWithRom,
    main, circuit_norm] at h_holds
  exact h_holds.1 (row.core.is_external_op * (1 - row.core.is_external_op))
    (Or.inr (Or.inl rfl))

/-- Project the ROM lookup carried by unified Main row constraints to exact
    program-ROM membership for the evaluated row message. -/
theorem romSpec_of_mainWithRomMemAndOpBus_constraints
    (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env
        ((mainWithRomMemAndOpBus length program row).operations offset)) :
    (romStaticTable length program).Spec (eval env (romMessageExpr row)) := by
  exact romSpec_of_mainWithRomAndMemBus_constraints length program row offset env (by
    simpa only [mainWithRomMemAndOpBus] using h_holds)

theorem is_external_op_boolean_of_componentWithRomMemAndOpBus_constraints
    (length : ℕ) (program : Program length)
    (env : Environment FGL)
    (h_holds :
      (componentWithRomMemAndOpBus length program).operations.ConstraintsHold env) :
    env ((componentWithRomMemAndOpBus length program).rowInputVar.core.is_external_op
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.core.is_external_op)) = 0 := by
  have h_row :
      (componentWithRomMemAndOpBus length program).rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff
      (component := componentWithRomMemAndOpBus length program) env).mp h_holds
  exact is_external_op_boolean_of_mainWithRomMemAndOpBus_constraints
    length program
    (componentWithRomMemAndOpBus length program).rowInputVar
    (componentWithRomMemAndOpBus length program).rowOffset env (by
      simpa only [componentWithRomMemAndOpBus, circuitWithRomMemAndOpBus,
        Component.rowOperations] using h_row)

theorem romBoolSpec_of_componentWithRomAndMemBus_constraints
    (length : ℕ) (program : Program length)
    (env : Environment FGL)
    (h_holds :
      (componentWithRomAndMemBus length program).operations.ConstraintsHold env) :
    env ((componentWithRomAndMemBus length program).rowInputVar.core.m32
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.core.m32)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.core.set_pc
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.core.set_pc)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.core.store_pc
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.core.store_pc)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.a_src_imm
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.a_src_imm)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.a_src_mem
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.a_src_mem)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.is_precompiled
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.is_precompiled)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_imm
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_imm)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_mem
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_mem)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.store_mem
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.store_mem)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.store_ind
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.store_ind)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_ind
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_ind)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.a_src_reg
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.a_src_reg)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_reg
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_reg)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.store_reg
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.store_reg)) = 0 := by
  have h_row :
      (componentWithRomAndMemBus length program).rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff
      (component := componentWithRomAndMemBus length program) env).mp h_holds
  exact romBoolSpec_of_mainWithRomAndMemBus_constraints
    length program
    (componentWithRomAndMemBus length program).rowInputVar
    (componentWithRomAndMemBus length program).rowOffset env (by
      simpa only [componentWithRomAndMemBus, circuitWithRomAndMemBus,
        Component.rowOperations] using h_row)

/-- Project the ROM lookup carried by the unified Main component's row
    constraints to exact program-ROM membership for the evaluated row message. -/
theorem romSpec_of_componentWithRomMemAndOpBus_constraints
    (length : ℕ) (program : Program length)
    (env : Environment FGL)
    (h_holds :
      (componentWithRomMemAndOpBus length program).operations.ConstraintsHold env) :
    (romStaticTable length program).Spec
      (eval env
        (romMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar)) := by
  have h_row :
      (componentWithRomMemAndOpBus length program).rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff
      (component := componentWithRomMemAndOpBus length program) env).mp h_holds
  exact
    romSpec_of_mainWithRomMemAndOpBus_constraints
      length program
      (componentWithRomMemAndOpBus length program).rowInputVar
      (componentWithRomMemAndOpBus length program).rowOffset env
      (by
        simpa only [componentWithRomMemAndOpBus, circuitWithRomMemAndOpBus,
          Component.rowOperations] using h_row)

theorem componentWithRomAndMemBus_interactionsWith_memBus
    (length : ℕ) (program : Program length) :
    (componentWithRomAndMemBus length program).operations.interactionsWith
        MemBusChannel.toRaw =
      [ ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.a_src_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.a_src_reg))
            (aMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_ind
              + (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_reg))
            (bMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.store_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.store_ind
              + (componentWithRomAndMemBus length program).rowInputVar.rom.store_reg))
            (cMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw,
      [ ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.a_src_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.a_src_reg))
            (aMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_ind
              + (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_reg))
            (bMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.store_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.store_ind
              + (componentWithRomAndMemBus length program).rowInputVar.rom.store_reg))
            (cMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw) ]⟩ ∈
    (componentWithRomAndMemBus length program).exposedChannels
  simp only [componentWithRomAndMemBus, circuitWithRomAndMemBus,
    mainWithRomAndMemBusElaborated, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

theorem component_eval_opBusMessageExpr
    (env : Environment FGL) :
    eval env (opBusMessageExpr component.rowInputVar) =
      opBusMessage (component.rowInput env) := by
  rw [eval_opBusMessageExpr]
  exact congrArg opBusMessage
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset component.Input 0 env))

/-- The Main component exposes exactly its one operation-bus interaction.
    This keeps later C7 balance projections from unfolding the nine local
    constraints just to recover the channel message. -/
theorem component_interactionsWith_opBus :
    component.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.emitted (-component.rowInputVar.is_external_op)
          (opBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.emitted (-component.rowInputVar.is_external_op)
          (opBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, mainWithOpBusElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil]

/-- Project the `is_external_op` boolean assertion from the concrete
    `mainWithOpBus` operations without unfolding the whole Component `Spec`.

This is the local Main-side fact C7 needs to prove that Main op-bus
interactions have only multiplicity `-1` or `0`. -/
theorem is_external_op_boolean_of_mainWithOpBus_constraints
    (row : Var MainRow FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds : Operations.ConstraintsHold env ((mainWithOpBus row).operations offset)) :
    env (row.is_external_op * (1 - row.is_external_op)) = 0 := by
  simp only [mainWithOpBus, main, circuit_norm] at h_holds
  exact h_holds (row.is_external_op * (1 - row.is_external_op)) (Or.inr (Or.inl rfl))

/-- Component-level adapter for the Main `is_external_op` boolean assertion.

This is the Clean-flat idiom: first project `component.operations` to the
per-row `rowOperations` via `Component.constraintsHold_iff`, then unfold only
the local Main component wrapper. -/
theorem is_external_op_boolean_of_component_constraints
    (env : Environment FGL)
    (h_holds : component.operations.ConstraintsHold env) :
    env (component.rowInputVar.is_external_op * (1 - component.rowInputVar.is_external_op)) = 0 := by
  have h_row : component.rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff (component := component) env).mp h_holds
  exact is_external_op_boolean_of_mainWithOpBus_constraints
    component.rowInputVar component.rowOffset env (by
      simpa only [component, circuit, Component.rowOperations] using h_row)

theorem spec_via_component (row : MainRow FGL)
    (_h_assumptions : Assumptions row)
    (h_constraints : Spec row) :
    Spec row := by
  exact h_constraints

end ZiskFv.AirsClean.Main
