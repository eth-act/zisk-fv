import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement
import ZiskFv.Compliance.TraceLevelExport.PureMMulInputs
import ZiskFv.Compliance.TraceLevelExport.PureMDivInputs
import ZiskFv.Compliance.TraceLevelExport.PureControlInputs

namespace ZiskFv.Compliance

variable {n : ℕ}

/-- Reconstruct all63 pure runtime input families from decoded fields and current
register/PC agreement, not caller operand values or operand proofs. The13 M
factories retain every provider, range, remainder, forge and ISA fact. Four store
and seven load families reconstruct successful-read witnesses and consume
complete-old-domain constructors AND whole-input equality certificates.
The nine control factories preserve the complete old branch/jump/fence inputs,
including JALR's genuine source-row bridge, success, misa, privilege and mseccfg.

No public aggregate premise or opcode-domain condition is removed here.
The construction uses current, never all-step, soundness. -/
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
  | .mul c, ia =>
      canonicalMulInputsCore steps rowDecodes init i h_reg c pc hpc ia
  | .mulh c, ia =>
      canonicalMulhInputsCore steps rowDecodes init i h_reg c pc hpc ia
  | .mulhsu c, ia =>
      canonicalMulhsuInputsCore steps rowDecodes init i h_reg c pc hpc ia
  | .mulw c, ia =>
      canonicalMulwInputsCore steps rowDecodes init i h_reg c pc hpc ia
  | .mulhu c, ia =>
      canonicalMulhuInputsCore steps rowDecodes init i h_reg c pc hpc ia
  | .div c, ia =>
      divInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia
  | .rem c, ia =>
      remInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia
  | .divw c, ia =>
      divwInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia
  | .remw c, ia =>
      remwInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia
  | .divu c, ia =>
      divuInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia
  | .divuw c, ia =>
      divuwInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia
  | .remu c, ia =>
      remuInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia
  | .remuw c, ia =>
      remuwInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia
  | .beq c, ia =>
      canonicalBeqInputsCore steps rowDecodes init i h_reg c pc hpc ia
  | .bne c, ia =>
      canonicalBneInputsCore steps rowDecodes init i h_reg c pc hpc ia
  | .blt c, ia =>
      canonicalBltInputsCore steps rowDecodes init i h_reg c pc hpc ia
  | .bge c, ia =>
      canonicalBgeInputsCore steps rowDecodes init i h_reg c pc hpc ia
  | .bltu c, ia =>
      canonicalBltuInputsCore steps rowDecodes init i h_reg c pc hpc ia
  | .bgeu c, ia =>
      canonicalBgeuInputsCore steps rowDecodes init i h_reg c pc hpc ia
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
  | .jal c, ia =>
      canonicalJalInputsCore steps init i c pc hpc ia
  | .jalr c, ia =>
      canonicalJalrInputsCore steps rowDecodes init i h_reg c pc hpc ia
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
      rcases c with ⟨⟨r1⟩, ⟨r2⟩, imm⟩
      let construction := InputsCore_sb.of_state_assumptions i ia.input ia.regs
        ia.h_opcode_assumptions ia.h_a0_value ia.h_a1_value
        ia.h_b0_value ia.h_b1_value ia.h_risc_v_assumptions
      have h_old_domain : PureSpec.sb_state_assumptions construction.val.input
          (chainedSailTrace steps init i) := by
        rw [construction.property]
        exact ia.h_opcode_assumptions
      exact { construction.val with
        h_input_r1 := h_r1
        h_input_r2 := h_r2
        h_input_pc := h_pc
        h_opcode_assumptions := h_old_domain }
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
      rcases c with ⟨⟨r1⟩, ⟨r2⟩, imm⟩
      let construction := InputsCore_sh.of_state_assumptions i ia.input ia.regs
        ia.h_opcode_assumptions ia.h_a0_value ia.h_a1_value
        ia.h_b0_value ia.h_b1_value ia.h_risc_v_assumptions
      have h_old_domain : PureSpec.sh_state_assumptions construction.val.input
          (chainedSailTrace steps init i) := by
        rw [construction.property]
        exact ia.h_opcode_assumptions
      exact { construction.val with
        h_input_r1 := h_r1
        h_input_r2 := h_r2
        h_input_pc := h_pc
        h_opcode_assumptions := h_old_domain }
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
      rcases c with ⟨⟨r1⟩, ⟨r2⟩, imm⟩
      let construction := InputsCore_sw.of_state_assumptions i ia.input ia.regs
        ia.h_opcode_assumptions ia.h_a0_value ia.h_a1_value
        ia.h_b0_value ia.h_b1_value ia.h_risc_v_assumptions
      have h_old_domain : PureSpec.sw_state_assumptions construction.val.input
          (chainedSailTrace steps init i) := by
        rw [construction.property]
        exact ia.h_opcode_assumptions
      exact { construction.val with
        h_input_r1 := h_r1
        h_input_r2 := h_r2
        h_input_pc := h_pc
        h_opcode_assumptions := h_old_domain }
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
      rcases c with ⟨⟨r1⟩, ⟨r2⟩, imm⟩
      let construction := InputsCore_sd.of_state_assumptions i ia.input ia.regs
        ia.h_opcode_assumptions ia.h_a0_value ia.h_a1_value
        ia.h_b0_value ia.h_b1_value ia.h_risc_v_assumptions
      have h_old_domain : PureSpec.sd_state_assumptions construction.val.input
          (chainedSailTrace steps init i) := by
        rw [construction.property]
        exact ia.h_opcode_assumptions
      exact { construction.val with
        h_input_r1 := h_r1
        h_input_r2 := h_r2
        h_input_pc := h_pc
        h_opcode_assumptions := h_old_domain }
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
  | .fence c, ia =>
      canonicalFenceInputsCore steps init i c pc hpc ia

end ZiskFv.Compliance
