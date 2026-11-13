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

/-- Reconstruct the 30 pure ALU inputs from decoded operands and the current
register agreement, not from the caller's operand values or operand proofs.

The PC and its presence equality are provided by the current induction
invariant. None of these arms reads the old input record. No public input field
is removed here. The other 33 families pass through unchanged and are not discharged. This
constructor uses the current induction invariant, not all-step soundness. -/
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
  | .sb _, ia => ia
  | .sh _, ia => ia
  | .sw _, ia => ia
  | .sd _, ia => ia
  | .ld _, ia => ia
  | .lbu _, ia => ia
  | .lhu _, ia => ia
  | .lwu _, ia => ia
  | .lb _, ia => ia
  | .lh _, ia => ia
  | .lw _, ia => ia
  | .fence _, ia => ia

end ZiskFv.Compliance
