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

/-- Reconstruct the 27 simple ALU inputs from decoded operands and the current
register agreement, not from the caller's operand values or operand proofs.

Only the existing PC value and its presence equality are retained in these arms:
PC presence is still a boot-state residue, and no public input field is removed
here. The other 36 families pass through unchanged and are not discharged. This
constructor uses the current induction invariant, not all-step soundness. -/
noncomputable def pureInputsOfRegAgree {trace : AcceptedZiskTrace n}
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (ia : InputsAgreeCore trace (chainedSailTrace steps init) i (steps i)) :
    InputsAgreeCore trace (chainedSailTrace steps init) i (steps i) :=
  match steps i, ia with
  | .sub c, ia => {
      sub_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.sub_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .and c, ia => {
      and_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.and_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .or c, ia => {
      or_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.or_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .xor c, ia => {
      xor_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.xor_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .slt c, ia => {
      slt_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.slt_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .sltu c, ia => {
      sltu_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.sltu_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .andi c, ia => {
      andi_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := ia.andi_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .ori c, ia => {
      ori_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := ia.ori_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .xori c, ia => {
      xori_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := ia.xori_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .slti c, ia => {
      slti_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := ia.slti_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .sltiu c, ia => {
      sltiu_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := ia.sltiu_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .sll c, ia => {
      sll_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.sll_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .srl c, ia => {
      srl_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.srl_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .sra c, ia => {
      sra_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.sra_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .slli c, ia => {
      slli_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        shamt := c.shamt
        rd := regidx_to_fin c.rd
        PC := ia.slli_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_shamt := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .srli c, ia => {
      srli_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        shamt := c.shamt
        rd := regidx_to_fin c.rd
        PC := ia.srli_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_shamt := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .srai c, ia => {
      srai_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        shamt := c.shamt
        rd := regidx_to_fin c.rd
        PC := ia.srai_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_shamt := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .add c, ia => {
      add_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.add_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .addi c, ia => {
      addi_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := ia.addi_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .subw c, ia => {
      subw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.subw_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .addw c, ia => {
      addw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.addw_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .addiw c, ia => {
      addiw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := ia.addiw_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .sllw c, ia => {
      sllw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.sllw_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .srlw c, ia => {
      srlw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.srlw_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .sraw c, ia => {
      sraw_input := {
        r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
        r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
        rd := regidx_to_fin c.rd
        PC := ia.sraw_input.PC }
      h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .slliw _, ia => ia
  | .srliw _, ia => ia
  | .sraiw _, ia => ia
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
  | .lui c, ia => {
      lui_input := {
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := ia.lui_input.PC }
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
  | .auipc c, ia => {
      auipc_input := {
        imm := c.imm
        rd := regidx_to_fin c.rd
        PC := ia.auipc_input.PC }
      h_input_imm := rfl
      h_input_rd := rfl
      h_input_pc := ia.h_input_pc }
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
