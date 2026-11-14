import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement

namespace ZiskFv.Compliance

variable {n : ℕ}

/-- Architectural x0 is constant; all other values come from the ZisK register file. -/
private noncomputable def pureInputRegValue {trace : AcceptedZiskTrace n}
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i)) (j : ℕ) (k : Fin 32) : BitVec 64 :=
  if k = 0 then 0 else ziskRegFile steps rowDecodes j k

private theorem read_pureInputRegValue {trace : AcceptedZiskTrace n}
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val) (k : Fin 32) :
    read_xreg k (chainedSailTrace steps init i) =
      EStateM.Result.ok (pureInputRegValue steps rowDecodes i.val k)
        (chainedSailTrace steps init i) := by
  by_cases hk : k = 0
  · subst k
    simp [pureInputRegValue, read_xreg]
  · simpa [pureInputRegValue, hk, chainedSailTrace] using
      read_xreg_of_regAgree steps rowDecodes init i.val k hk h_reg

private theorem store_rX_from_read
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r : regidx)
    (h_read : ∃ value : BitVec 64,
      read_xreg (regidx_to_fin r) state = EStateM.Result.ok value state) :
    LeanRV64D.Functions.rX_bits (regidx.Regidx (storeRegBits r)) state =
      EStateM.Result.ok (Classical.choose h_read) state := by
  rw [storeRegBits_roundtrip,
    rX_read_xreg_equiv state r (regidx_to_fin r)
      (by cases r <;> simp [regidx_to_fin])]
  exact Classical.choose_spec h_read

/-- Reconstruct30 pure ALU inputs from decoded operands and current register/PC
agreement. Four store families also reconstruct successful-read witnesses. Seven
loads consume complete-old-surface certificates, retaining their existing byte,
range/alignment, lane, provider and platform obligations on the unchanged domain.

No public aggregate premise is removed here. The other22 families pass through
unchanged. The construction uses current, never all-step, soundness. -/
noncomputable def pureInputsOfRegAgree {trace : AcceptedZiskTrace n}
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsAgreeCore trace (chainedSailTrace steps init) i (steps i)) :
    InputsAgreeCore trace (chainedSailTrace steps init) i (steps i) :=
  match steps i, ia with
  | .sub c, _ => {
      sub_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .and c, _ => {
      and_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .or c, _ => {
      or_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .xor c, _ => {
      xor_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .slt c, _ => {
      slt_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .sltu c, _ => {
      sltu_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .andi c, _ => {
      andi_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .ori c, _ => {
      ori_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .xori c, _ => {
      xori_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .slti c, _ => {
      slti_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .sltiu c, _ => {
      sltiu_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .sll c, _ => {
      sll_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .srl c, _ => {
      srl_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .sra c, _ => {
      sra_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .slli c, _ => {
      slli_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        shamt := c.shamt
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_shamt := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .srli c, _ => {
      srli_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        shamt := c.shamt
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_shamt := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .srai c, _ => {
      srai_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        shamt := c.shamt
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_shamt := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .add c, _ => {
      add_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .addi c, _ => {
      addi_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .subw c, _ => {
      subw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .addw c, _ => {
      addw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .addiw c, _ => {
      addiw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .sllw c, _ => {
      sllw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .srlw c, _ => {
      srlw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .sraw c, _ => {
      sraw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := hpc }
  | .slliw c, _ => {
      h_input_r1 := ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      h_input_pc := ⟨pc, hpc⟩ }
  | .srliw c, _ => {
      h_input_r1 := ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      h_input_pc := ⟨pc, hpc⟩ }
  | .sraiw c, _ => {
      h_input_r1 := ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      h_input_pc := ⟨pc, hpc⟩ }
  | .mul _, ia => ia
  | .mulh _, ia => ia
  | .mulhsu _, ia => ia
  | .mulw _, ia => ia
  | .mulhu _, ia => ia
  | .div _, ia => ia
  | .rem _, ia => ia
  | .divw _, ia => ia
  | .remw _, ia => ia
  | .divu _, ia => ia
  | .divuw _, ia => ia
  | .remu _, ia => ia
  | .remuw _, ia => ia
  | .beq _, ia => ia
  | .bne _, ia => ia
  | .blt _, ia => ia
  | .bge _, ia => ia
  | .bltu _, ia => ia
  | .bgeu _, ia => ia
  | .lui c, _ => {
      lui_input := {
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .auipc c, _ => {
      auipc_input := {
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := pc }
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := hpc }
  | .jal _, ia => ia
  | .jalr _, ia => ia
  | .sb c, ia => by
      let h_r1 : ∃ value : BitVec 64,
          read_xreg (regidx_to_fin c.r1) (chainedSailTrace steps init i) =
            EStateM.Result.ok value (chainedSailTrace steps init i) :=
        ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      let h_r2 : ∃ value : BitVec 64,
          read_xreg (regidx_to_fin c.r2) (chainedSailTrace steps init i) =
            EStateM.Result.ok value (chainedSailTrace steps init i) :=
        ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      let h_pc : ∃ pc : BitVec 64,
          (chainedSailTrace steps init i).regs.get? Register.PC = some pc :=
        ⟨pc, hpc⟩
      exact {
        h_input_r1 := h_r1
        h_input_r2 := h_r2
        h_input_pc := h_pc
        regs := ia.regs
        h_opcode_assumptions := ⟨Classical.choose_spec h_pc,
          store_rX_from_read _ c.r1 h_r1, store_rX_from_read _ c.r2 h_r2,
          ia.h_opcode_assumptions.2.2.2⟩
        h_a0_value := ia.h_a0_value
        h_a1_value := ia.h_a1_value
        h_b0_value := ia.h_b0_value
        h_b1_value := ia.h_b1_value
        h_risc_v_assumptions := ia.h_risc_v_assumptions }
  | .sh c, ia => by
      let h_r1 : ∃ value : BitVec 64,
          read_xreg (regidx_to_fin c.r1) (chainedSailTrace steps init i) =
            EStateM.Result.ok value (chainedSailTrace steps init i) :=
        ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      let h_r2 : ∃ value : BitVec 64,
          read_xreg (regidx_to_fin c.r2) (chainedSailTrace steps init i) =
            EStateM.Result.ok value (chainedSailTrace steps init i) :=
        ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      let h_pc : ∃ pc : BitVec 64,
          (chainedSailTrace steps init i).regs.get? Register.PC = some pc :=
        ⟨pc, hpc⟩
      exact {
        h_input_r1 := h_r1
        h_input_r2 := h_r2
        h_input_pc := h_pc
        regs := ia.regs
        h_opcode_assumptions := ⟨Classical.choose_spec h_pc,
          store_rX_from_read _ c.r1 h_r1, store_rX_from_read _ c.r2 h_r2,
          ia.h_opcode_assumptions.2.2.2⟩
        h_a0_value := ia.h_a0_value
        h_a1_value := ia.h_a1_value
        h_b0_value := ia.h_b0_value
        h_b1_value := ia.h_b1_value
        h_risc_v_assumptions := ia.h_risc_v_assumptions }
  | .sw c, ia => by
      let h_r1 : ∃ value : BitVec 64,
          read_xreg (regidx_to_fin c.r1) (chainedSailTrace steps init i) =
            EStateM.Result.ok value (chainedSailTrace steps init i) :=
        ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      let h_r2 : ∃ value : BitVec 64,
          read_xreg (regidx_to_fin c.r2) (chainedSailTrace steps init i) =
            EStateM.Result.ok value (chainedSailTrace steps init i) :=
        ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      let h_pc : ∃ pc : BitVec 64,
          (chainedSailTrace steps init i).regs.get? Register.PC = some pc :=
        ⟨pc, hpc⟩
      exact {
        h_input_r1 := h_r1
        h_input_r2 := h_r2
        h_input_pc := h_pc
        regs := ia.regs
        h_opcode_assumptions := ⟨Classical.choose_spec h_pc,
          store_rX_from_read _ c.r1 h_r1, store_rX_from_read _ c.r2 h_r2,
          ia.h_opcode_assumptions.2.2.2⟩
        h_a0_value := ia.h_a0_value
        h_a1_value := ia.h_a1_value
        h_b0_value := ia.h_b0_value
        h_b1_value := ia.h_b1_value
        h_risc_v_assumptions := ia.h_risc_v_assumptions }
  | .sd c, ia => by
      let h_r1 : ∃ value : BitVec 64,
          read_xreg (regidx_to_fin c.r1) (chainedSailTrace steps init i) =
            EStateM.Result.ok value (chainedSailTrace steps init i) :=
        ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      let h_r2 : ∃ value : BitVec 64,
          read_xreg (regidx_to_fin c.r2) (chainedSailTrace steps init i) =
            EStateM.Result.ok value (chainedSailTrace steps init i) :=
        ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
      let h_pc : ∃ pc : BitVec 64,
          (chainedSailTrace steps init i).regs.get? Register.PC = some pc :=
        ⟨pc, hpc⟩
      exact {
        h_input_r1 := h_r1
        h_input_r2 := h_r2
        h_input_pc := h_pc
        regs := ia.regs
        h_opcode_assumptions := ⟨Classical.choose_spec h_pc,
          store_rX_from_read _ c.r1 h_r1, store_rX_from_read _ c.r2 h_r2,
          ia.h_opcode_assumptions.2.2.2⟩
        h_a0_value := ia.h_a0_value
        h_a1_value := ia.h_a1_value
        h_b0_value := ia.h_b0_value
        h_b1_value := ia.h_b1_value
        h_risc_v_assumptions := ia.h_risc_v_assumptions }
  | .ld c, ia => by
      rcases c with ⟨r1, rd, imm⟩
      cases r1 with
      | Regidx r1 =>
        cases rd with
        | Regidx rd =>
          let construction := InputsCore_ld.of_state_assumptions i ia.input
            ia.regs ia.mem ia.r_mem ia.h_opcode_assumptions ia.h_a0_value
            ia.h_risc_v_assumptions ia.h_msg ia.h_mem_sel ia.h_mem_wr
          exact { construction.val with
            h_input_r1 := ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
            h_input_pc := ⟨pc, hpc⟩
            h_opcode_assumptions := by
              change PureSpec.ld_state_assumptions construction.val.input
                (chainedSailTrace steps init i)
              rw [construction.property]
              exact ia.h_opcode_assumptions }
  | .lbu c, ia => by
      rcases c with ⟨r1, rd, imm⟩
      cases r1 with
      | Regidx r1 =>
        cases rd with
        | Regidx rd =>
          let construction := InputsCore_lbu.of_state_assumptions i ia.input
            ia.regs ia.mem ia.r_mem ia.align ia.h_opcode_assumptions ia.h_a0_value
            ia.h_risc_v_assumptions ia.h_msg ia.h_mem_sel ia.h_mem_wr
          exact { construction.val with
            h_input_r1 := ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
            h_input_pc := ⟨pc, hpc⟩
            h_opcode_assumptions := by
              change PureSpec.lbu_state_assumptions construction.val.input
                (chainedSailTrace steps init i)
              rw [construction.property]
              exact ia.h_opcode_assumptions }
  | .lhu c, ia => by
      rcases c with ⟨r1, rd, imm⟩
      cases r1 with
      | Regidx r1 =>
        cases rd with
        | Regidx rd =>
          let construction := InputsCore_lhu.of_state_assumptions i ia.input
            ia.regs ia.mem ia.r_mem ia.align ia.h_opcode_assumptions ia.h_a0_value
            ia.h_risc_v_assumptions ia.h_msg ia.h_mem_sel ia.h_mem_wr
          exact { construction.val with
            h_input_r1 := ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
            h_input_pc := ⟨pc, hpc⟩
            h_opcode_assumptions := by
              change PureSpec.lhu_state_assumptions construction.val.input
                (chainedSailTrace steps init i)
              rw [construction.property]
              exact ia.h_opcode_assumptions }
  | .lwu c, ia => by
      rcases c with ⟨r1, rd, imm⟩
      cases r1 with
      | Regidx r1 =>
        cases rd with
        | Regidx rd =>
          let construction := InputsCore_lwu.of_state_assumptions i ia.input
            ia.regs ia.mem ia.r_mem ia.align ia.h_opcode_assumptions ia.h_a0_value
            ia.h_risc_v_assumptions ia.h_msg ia.h_mem_sel ia.h_mem_wr
          exact { construction.val with
            h_input_r1 := ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
            h_input_pc := ⟨pc, hpc⟩
            h_opcode_assumptions := by
              change PureSpec.lwu_state_assumptions construction.val.input
                (chainedSailTrace steps init i)
              rw [construction.property]
              exact ia.h_opcode_assumptions }
  | .lb c, ia => by
      rcases c with ⟨r1, rd, imm⟩
      cases r1 with
      | Regidx r1 =>
        cases rd with
        | Regidx rd =>
          let construction := InputsCore_lb.of_state_assumptions i ia.input
            ia.regs ia.mem ia.r_mem ia.h_opcode_assumptions ia.h_a0_value
            ia.h_risc_v_assumptions ia.h_msg ia.h_mem_sel ia.h_mem_wr
          exact { construction.val with
            h_input_r1 := ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
            h_input_pc := ⟨pc, hpc⟩
            h_opcode_assumptions := by
              change PureSpec.lb_state_assumptions construction.val.input
                (chainedSailTrace steps init i)
              rw [construction.property]
              exact ia.h_opcode_assumptions }
  | .lh c, ia => by
      rcases c with ⟨r1, rd, imm⟩
      cases r1 with
      | Regidx r1 =>
        cases rd with
        | Regidx rd =>
          let construction := InputsCore_lh.of_state_assumptions i ia.input
            ia.regs ia.mem ia.r_mem ia.h_opcode_assumptions ia.h_a0_value
            ia.h_risc_v_assumptions ia.h_msg ia.h_mem_sel ia.h_mem_wr
          exact { construction.val with
            h_input_r1 := ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
            h_input_pc := ⟨pc, hpc⟩
            h_opcode_assumptions := by
              change PureSpec.lh_state_assumptions construction.val.input
                (chainedSailTrace steps init i)
              rw [construction.property]
              exact ia.h_opcode_assumptions }
  | .lw c, ia => by
      rcases c with ⟨r1, rd, imm⟩
      cases r1 with
      | Regidx r1 =>
        cases rd with
        | Regidx rd =>
          let construction := InputsCore_lw.of_state_assumptions i ia.input
            ia.regs ia.mem ia.r_mem ia.h_opcode_assumptions ia.h_a0_value
            ia.h_risc_v_assumptions ia.h_msg ia.h_mem_sel ia.h_mem_wr
          exact { construction.val with
            h_input_r1 := ⟨_, read_pureInputRegValue steps rowDecodes init i h_reg _⟩
            h_input_pc := ⟨pc, hpc⟩
            h_opcode_assumptions := by
              change PureSpec.lw_state_assumptions construction.val.input
                (chainedSailTrace steps init i)
              rw [construction.property]
              exact ia.h_opcode_assumptions }
  | .fence _, ia => ia

end ZiskFv.Compliance
