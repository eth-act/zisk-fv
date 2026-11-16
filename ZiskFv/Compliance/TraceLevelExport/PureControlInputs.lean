import ZiskFv.Compliance.TraceLevelExport.PureInputRegisters
import ZiskFv.Compliance.TraceLevelExport.RowDataControl

namespace ZiskFv.Compliance

variable {n : ℕ} {trace : AcceptedZiskTrace n}

/-- Runtime BEQ operands come from the current register file and decoded fields. -/
noncomputable def canonicalBeqInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_beq trace i) (pc : BitVec 64) : PureSpec.BeqInput where
  imm := c.imm
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  PC := pc

/-- Existing successful reads and current PC determine the complete old input. -/
theorem beqInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_beq trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_beq trace (chainedSailTrace steps init) i c) :
    ia.beq_input = canonicalBeqInput steps rowDecodes i c pc := by
  have hr1 : ia.beq_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.beq_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hPC : ia.beq_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  change PureSpec.BeqInput.mk ia.beq_input.imm ia.beq_input.r1_val
    ia.beq_input.r2_val ia.beq_input.PC = _
  simp only [canonicalBeqInput, ia.h_input_imm, hr1, hr2, hPC]

/-- Preserve all old architectural/success facts at the same whole canonical input. -/
noncomputable def canonicalBeqInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_beq trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_beq trace (chainedSailTrace steps init) i c) :
    InputsCore_beq trace (chainedSailTrace steps init) i c := by
  have heq := beqInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    beq_input := canonicalBeqInput steps rowDecodes i c pc
    misa_val := ia.misa_val
    h_input_imm := rfl
    h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_pc := hpc
    h_input_misa := ia.h_input_misa
    h_misa_c := ia.h_misa_c
    h_success := by simpa only [← heq] using ia.h_success
  }

theorem canonicalBeqInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_beq trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_beq trace (chainedSailTrace steps init) i c) :
    (canonicalBeqInputsCore steps rowDecodes init i h_reg c pc hpc ia).beq_input =
      canonicalBeqInput steps rowDecodes i c pc := rfl

theorem canonicalBeqInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_beq trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_beq trace (chainedSailTrace steps init) i c) :
    (canonicalBeqInputsCore steps rowDecodes init i h_reg c pc hpc ia).beq_input = ia.beq_input :=
  (canonicalBeqInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (beqInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- Runtime BNE operands come from the current register file and decoded fields. -/
noncomputable def canonicalBneInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_bne trace i) (pc : BitVec 64) : PureSpec.BneInput where
  imm := c.imm
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  PC := pc

/-- Existing successful reads and current PC determine the complete old input. -/
theorem bneInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bne trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bne trace (chainedSailTrace steps init) i c) :
    ia.bne_input = canonicalBneInput steps rowDecodes i c pc := by
  have hr1 : ia.bne_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.bne_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hPC : ia.bne_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  change PureSpec.BneInput.mk ia.bne_input.imm ia.bne_input.r1_val
    ia.bne_input.r2_val ia.bne_input.PC = _
  simp only [canonicalBneInput, ia.h_input_imm, hr1, hr2, hPC]

/-- Preserve all old architectural/success facts at the same whole canonical input. -/
noncomputable def canonicalBneInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bne trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bne trace (chainedSailTrace steps init) i c) :
    InputsCore_bne trace (chainedSailTrace steps init) i c := by
  have heq := bneInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    bne_input := canonicalBneInput steps rowDecodes i c pc
    misa_val := ia.misa_val
    h_input_imm := rfl
    h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_pc := hpc
    h_input_misa := ia.h_input_misa
    h_misa_c := ia.h_misa_c
    h_success := by simpa only [← heq] using ia.h_success
  }

theorem canonicalBneInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bne trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bne trace (chainedSailTrace steps init) i c) :
    (canonicalBneInputsCore steps rowDecodes init i h_reg c pc hpc ia).bne_input =
      canonicalBneInput steps rowDecodes i c pc := rfl

theorem canonicalBneInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bne trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bne trace (chainedSailTrace steps init) i c) :
    (canonicalBneInputsCore steps rowDecodes init i h_reg c pc hpc ia).bne_input = ia.bne_input :=
  (canonicalBneInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (bneInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- Runtime BLT operands come from the current register file and decoded fields. -/
noncomputable def canonicalBltInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_blt trace i) (pc : BitVec 64) : PureSpec.BltInput where
  imm := c.imm
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  PC := pc

/-- Existing successful reads and current PC determine the complete old input. -/
theorem bltInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_blt trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_blt trace (chainedSailTrace steps init) i c) :
    ia.blt_input = canonicalBltInput steps rowDecodes i c pc := by
  have hr1 : ia.blt_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.blt_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hPC : ia.blt_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  change PureSpec.BltInput.mk ia.blt_input.imm ia.blt_input.r1_val
    ia.blt_input.r2_val ia.blt_input.PC = _
  simp only [canonicalBltInput, ia.h_input_imm, hr1, hr2, hPC]

/-- Preserve all old architectural/success facts at the same whole canonical input. -/
noncomputable def canonicalBltInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_blt trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_blt trace (chainedSailTrace steps init) i c) :
    InputsCore_blt trace (chainedSailTrace steps init) i c := by
  have heq := bltInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    blt_input := canonicalBltInput steps rowDecodes i c pc
    misa_val := ia.misa_val
    h_input_imm := rfl
    h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_pc := hpc
    h_input_misa := ia.h_input_misa
    h_misa_c := ia.h_misa_c
    h_success := by simpa only [← heq] using ia.h_success
  }

theorem canonicalBltInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_blt trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_blt trace (chainedSailTrace steps init) i c) :
    (canonicalBltInputsCore steps rowDecodes init i h_reg c pc hpc ia).blt_input =
      canonicalBltInput steps rowDecodes i c pc := rfl

theorem canonicalBltInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_blt trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_blt trace (chainedSailTrace steps init) i c) :
    (canonicalBltInputsCore steps rowDecodes init i h_reg c pc hpc ia).blt_input = ia.blt_input :=
  (canonicalBltInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (bltInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- Runtime BGE operands come from the current register file and decoded fields. -/
noncomputable def canonicalBgeInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_bge trace i) (pc : BitVec 64) : PureSpec.BgeInput where
  imm := c.imm
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  PC := pc

/-- Existing successful reads and current PC determine the complete old input. -/
theorem bgeInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bge trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bge trace (chainedSailTrace steps init) i c) :
    ia.bge_input = canonicalBgeInput steps rowDecodes i c pc := by
  have hr1 : ia.bge_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.bge_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hPC : ia.bge_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  change PureSpec.BgeInput.mk ia.bge_input.imm ia.bge_input.r1_val
    ia.bge_input.r2_val ia.bge_input.PC = _
  simp only [canonicalBgeInput, ia.h_input_imm, hr1, hr2, hPC]

/-- Preserve all old architectural/success facts at the same whole canonical input. -/
noncomputable def canonicalBgeInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bge trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bge trace (chainedSailTrace steps init) i c) :
    InputsCore_bge trace (chainedSailTrace steps init) i c := by
  have heq := bgeInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    bge_input := canonicalBgeInput steps rowDecodes i c pc
    misa_val := ia.misa_val
    h_input_imm := rfl
    h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_pc := hpc
    h_input_misa := ia.h_input_misa
    h_misa_c := ia.h_misa_c
    h_success := by simpa only [← heq] using ia.h_success
  }

theorem canonicalBgeInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bge trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bge trace (chainedSailTrace steps init) i c) :
    (canonicalBgeInputsCore steps rowDecodes init i h_reg c pc hpc ia).bge_input =
      canonicalBgeInput steps rowDecodes i c pc := rfl

theorem canonicalBgeInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bge trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bge trace (chainedSailTrace steps init) i c) :
    (canonicalBgeInputsCore steps rowDecodes init i h_reg c pc hpc ia).bge_input = ia.bge_input :=
  (canonicalBgeInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (bgeInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- Runtime BLTU operands come from the current register file and decoded fields. -/
noncomputable def canonicalBltuInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_bltu trace i) (pc : BitVec 64) : PureSpec.BltuInput where
  imm := c.imm
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  PC := pc

/-- Existing successful reads and current PC determine the complete old input. -/
theorem bltuInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bltu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bltu trace (chainedSailTrace steps init) i c) :
    ia.bltu_input = canonicalBltuInput steps rowDecodes i c pc := by
  have hr1 : ia.bltu_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.bltu_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hPC : ia.bltu_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  change PureSpec.BltuInput.mk ia.bltu_input.imm ia.bltu_input.r1_val
    ia.bltu_input.r2_val ia.bltu_input.PC = _
  simp only [canonicalBltuInput, ia.h_input_imm, hr1, hr2, hPC]

/-- Preserve all old architectural/success facts at the same whole canonical input. -/
noncomputable def canonicalBltuInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bltu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bltu trace (chainedSailTrace steps init) i c) :
    InputsCore_bltu trace (chainedSailTrace steps init) i c := by
  have heq := bltuInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    bltu_input := canonicalBltuInput steps rowDecodes i c pc
    misa_val := ia.misa_val
    h_input_imm := rfl
    h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_pc := hpc
    h_input_misa := ia.h_input_misa
    h_misa_c := ia.h_misa_c
    h_success := by simpa only [← heq] using ia.h_success
  }

theorem canonicalBltuInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bltu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bltu trace (chainedSailTrace steps init) i c) :
    (canonicalBltuInputsCore steps rowDecodes init i h_reg c pc hpc ia).bltu_input =
      canonicalBltuInput steps rowDecodes i c pc := rfl

theorem canonicalBltuInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bltu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bltu trace (chainedSailTrace steps init) i c) :
    (canonicalBltuInputsCore steps rowDecodes init i h_reg c pc hpc ia).bltu_input = ia.bltu_input :=
  (canonicalBltuInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (bltuInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- Runtime BGEU operands come from the current register file and decoded fields. -/
noncomputable def canonicalBgeuInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_bgeu trace i) (pc : BitVec 64) : PureSpec.BgeuInput where
  imm := c.imm
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  PC := pc

/-- Existing successful reads and current PC determine the complete old input. -/
theorem bgeuInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bgeu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bgeu trace (chainedSailTrace steps init) i c) :
    ia.bgeu_input = canonicalBgeuInput steps rowDecodes i c pc := by
  have hr1 : ia.bgeu_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.bgeu_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hPC : ia.bgeu_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  change PureSpec.BgeuInput.mk ia.bgeu_input.imm ia.bgeu_input.r1_val
    ia.bgeu_input.r2_val ia.bgeu_input.PC = _
  simp only [canonicalBgeuInput, ia.h_input_imm, hr1, hr2, hPC]

/-- Preserve all old architectural/success facts at the same whole canonical input. -/
noncomputable def canonicalBgeuInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bgeu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bgeu trace (chainedSailTrace steps init) i c) :
    InputsCore_bgeu trace (chainedSailTrace steps init) i c := by
  have heq := bgeuInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    bgeu_input := canonicalBgeuInput steps rowDecodes i c pc
    misa_val := ia.misa_val
    h_input_imm := rfl
    h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_pc := hpc
    h_input_misa := ia.h_input_misa
    h_misa_c := ia.h_misa_c
    h_success := by simpa only [← heq] using ia.h_success
  }

theorem canonicalBgeuInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bgeu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bgeu trace (chainedSailTrace steps init) i c) :
    (canonicalBgeuInputsCore steps rowDecodes init i h_reg c pc hpc ia).bgeu_input =
      canonicalBgeuInput steps rowDecodes i c pc := rfl

theorem canonicalBgeuInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_bgeu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_bgeu trace (chainedSailTrace steps init) i c) :
    (canonicalBgeuInputsCore steps rowDecodes init i h_reg c pc hpc ia).bgeu_input = ia.bgeu_input :=
  (canonicalBgeuInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (bgeuInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- JAL's decoded destination/immediate and current PC are its complete runtime input. -/
def canonicalJalInput {i : Fin n} (c : Claim_jal trace i) (pc : BitVec 64) :
    PureSpec.JalInput where
  imm := c.imm
  rd := regidx_to_fin c.rd
  PC := pc

theorem jalInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (c : Claim_jal trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_jal trace (chainedSailTrace steps init) i c) :
    ia.jal_input = canonicalJalInput c pc := by
  have hPC : ia.jal_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  change PureSpec.JalInput.mk ia.jal_input.imm ia.jal_input.rd ia.jal_input.PC = _
  simp only [canonicalJalInput, ia.h_input_imm, ia.h_input_rd, hPC]

noncomputable def canonicalJalInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (c : Claim_jal trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_jal trace (chainedSailTrace steps init) i c) :
    InputsCore_jal trace (chainedSailTrace steps init) i c := by
  have heq := jalInput_eq_canonical steps init i c pc hpc ia
  exact {
    jal_input := canonicalJalInput c pc
    misa_val := ia.misa_val
    h_input_rd := rfl
    h_input_pc := hpc
    h_input_misa := ia.h_input_misa
    h_misa_c := ia.h_misa_c
    h_success := by simpa only [← heq] using ia.h_success
    h_input_imm := rfl
  }

theorem canonicalJalInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (c : Claim_jal trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_jal trace (chainedSailTrace steps init) i c) :
    (canonicalJalInputsCore steps init i c pc hpc ia).jal_input =
      canonicalJalInput c pc := rfl

theorem canonicalJalInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (c : Claim_jal trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_jal trace (chainedSailTrace steps init) i c) :
    (canonicalJalInputsCore steps init i c pc hpc ia).jal_input = ia.jal_input :=
  (canonicalJalInputsCore_input steps init i c pc hpc ia).trans
    (jalInput_eq_canonical steps init i c pc hpc ia).symm

/-- JALR reads the actual current rs1; no lowering-row or operand agreement is invented. -/
noncomputable def canonicalJalrInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_jalr trace i) (pc : BitVec 64) : PureSpec.JalrInput where
  imm := c.imm
  rs1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.rs1)
  rd := regidx_to_fin c.rd
  PC := pc

theorem jalrInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_jalr trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_jalr trace (chainedSailTrace steps init) i c) :
    ia.jalr_input = canonicalJalrInput steps rowDecodes i c pc := by
  have hr1 : ia.jalr_input.rs1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.rs1) := by
    have h := ia.h_input_rs1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.rs1))
    injection h with hval
  have hPC : ia.jalr_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  change PureSpec.JalrInput.mk ia.jalr_input.imm ia.jalr_input.rs1_val
    ia.jalr_input.rd ia.jalr_input.PC = _
  simp only [canonicalJalrInput, ia.h_input_imm, hr1, ia.h_input_rd, hPC]

/-- The genuine source-row bridge and all privilege/mseccfg facts remain original. -/
noncomputable def canonicalJalrInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_jalr trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_jalr trace (chainedSailTrace steps init) i c) :
    InputsCore_jalr trace (chainedSailTrace steps init) i c := by
  have heq := jalrInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    jalr_input := canonicalJalrInput steps rowDecodes i c pc
    misa_val := ia.misa_val
    mseccfg := ia.mseccfg
    h_rs1_start := by simpa only [← heq] using ia.h_rs1_start
    h_input_rd := rfl
    h_input_pc := hpc
    h_input_misa := ia.h_input_misa
    h_misa_c := ia.h_misa_c
    h_success := by simpa only [← heq] using ia.h_success
    h_input_imm := rfl
    h_input_rs1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_cur_privilege := ia.h_cur_privilege
    h_mseccfg := ia.h_mseccfg
  }

theorem canonicalJalrInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_jalr trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_jalr trace (chainedSailTrace steps init) i c) :
    (canonicalJalrInputsCore steps rowDecodes init i h_reg c pc hpc ia).jalr_input =
      canonicalJalrInput steps rowDecodes i c pc := rfl

theorem canonicalJalrInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_jalr trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_jalr trace (chainedSailTrace steps init) i c) :
    (canonicalJalrInputsCore steps rowDecodes init i h_reg c pc hpc ia).jalr_input =
      ia.jalr_input :=
  (canonicalJalrInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (jalrInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- FENCE's pure runtime record has only PC; decoded fence fields stay in Claim/Decode. -/
def canonicalFenceInput (pc : BitVec 64) : PureSpec.FenceInput where
  PC := pc

theorem fenceInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (c : Claim_fence trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_fence trace (chainedSailTrace steps init) i c) :
    ia.fence_input = canonicalFenceInput pc := by
  have hPC : ia.fence_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  change PureSpec.FenceInput.mk ia.fence_input.PC = _
  simp only [canonicalFenceInput, hPC]

noncomputable def canonicalFenceInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (c : Claim_fence trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_fence trace (chainedSailTrace steps init) i c) :
    InputsCore_fence trace (chainedSailTrace steps init) i c where
  fence_input := canonicalFenceInput pc
  h_input_pc := hpc
  h_input_priv := ia.h_input_priv

theorem canonicalFenceInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (c : Claim_fence trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_fence trace (chainedSailTrace steps init) i c) :
    (canonicalFenceInputsCore steps init i c pc hpc ia).fence_input =
      canonicalFenceInput pc := rfl

theorem canonicalFenceInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (c : Claim_fence trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_fence trace (chainedSailTrace steps init) i c) :
    (canonicalFenceInputsCore steps init i c pc hpc ia).fence_input = ia.fence_input :=
  (canonicalFenceInputsCore_input steps init i c pc hpc ia).trans
    (fenceInput_eq_canonical steps init i c pc hpc ia).symm

end ZiskFv.Compliance
