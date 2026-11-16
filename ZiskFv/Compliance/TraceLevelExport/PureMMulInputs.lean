import ZiskFv.Compliance.TraceLevelExport.PureInputRegisters
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem

namespace ZiskFv.Compliance

-- Keep imported arithmetic row computations opaque during record elaboration.
seal mulwArow mulhuArow

variable {n : ℕ} {trace : AcceptedZiskTrace n}

/-- Runtime MUL input from the current register file and decoded registers.
The supplied PC is the existing current-state PC, not an operand from the old input. -/
noncomputable def canonicalMulInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_mul trace i) (pc : BitVec 64) : PureSpec.MulInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- Successful reads uniquely determine the entire old MUL input,
including both full-width operands, destination and PC. -/
theorem mulInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mul trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mul trace (chainedSailTrace steps init) i c) :
    ia.mul_input = canonicalMulInput steps rowDecodes i c pc := by
  have hr1 : ia.mul_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.promises.input_r1_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.mul_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.promises.input_r2_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hrd : ia.mul_input.rd = regidx_to_fin c.rd := ia.promises.input_rd_eq
  have hPC : ia.mul_input.PC = pc := by
    exact Option.some.inj (ia.promises.input_pc_eq.symm.trans hpc)
  cases hinput : ia.mul_input
  simp_all [canonicalMulInput]

/-- Rebuild MUL's actual core with canonical runtime data. Whole-input
uniqueness transports every dependent fact; all provider, arithmetic and forge
witnesses remain those of the original core. -/
noncomputable def canonicalMulInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mul trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mul trace (chainedSailTrace steps init) i c) :
    InputsCore_mul trace (chainedSailTrace steps init) i c := by
  have heq := mulInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    mul_input := canonicalMulInput steps rowDecodes i c pc
    v := ia.v
    r_a := ia.r_a
    h_match_primary := ia.h_match_primary
    promises := by simpa only [← heq] using ia.promises
    h_row_constraints := ia.h_row_constraints
    arith_table := ia.arith_table
    arith_chunk_ranges := ia.arith_chunk_ranges
    arith_carry_ranges := ia.arith_carry_ranges
    h_rs1_value := by simpa only [← heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [← heq] using ia.h_rs2_value
    h_not_forge := ia.h_not_forge
  }

/-- Exact runtime projection for later dispatcher integration. -/
theorem canonicalMulInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mul trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mul trace (chainedSailTrace steps init) i c) :
    (canonicalMulInputsCore steps rowDecodes init i h_reg c pc hpc ia).mul_input =
      canonicalMulInput steps rowDecodes i c pc := rfl

/-- The factory preserves the whole original runtime input, not just used bits. -/
theorem canonicalMulInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mul trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mul trace (chainedSailTrace steps init) i c) :
    (canonicalMulInputsCore steps rowDecodes init i h_reg c pc hpc ia).mul_input =
      ia.mul_input :=
  (canonicalMulInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (mulInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- Runtime MULH input from the current register file and decoded registers.
The supplied PC is the existing current-state PC, not an operand from the old input. -/
noncomputable def canonicalMulhInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_mulh trace i) (pc : BitVec 64) : PureSpec.MulhInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- Successful reads uniquely determine the entire old MULH input,
including both full-width operands, destination and PC. -/
theorem mulhInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulh trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulh trace (chainedSailTrace steps init) i c) :
    ia.mulh_input = canonicalMulhInput steps rowDecodes i c pc := by
  have hr1 : ia.mulh_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.promises.input_r1_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.mulh_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.promises.input_r2_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hrd : ia.mulh_input.rd = regidx_to_fin c.rd := ia.promises.input_rd_eq
  have hPC : ia.mulh_input.PC = pc := by
    exact Option.some.inj (ia.promises.input_pc_eq.symm.trans hpc)
  cases hinput : ia.mulh_input
  simp_all [canonicalMulhInput]

/-- Rebuild MULH's actual core with canonical runtime data. Whole-input
uniqueness transports every dependent fact; all provider, arithmetic and forge
witnesses remain those of the original core. -/
noncomputable def canonicalMulhInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulh trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulh trace (chainedSailTrace steps init) i c) :
    InputsCore_mulh trace (chainedSailTrace steps init) i c := by
  have heq := mulhInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    mulh_input := canonicalMulhInput steps rowDecodes i c pc
    v := ia.v
    r_a := ia.r_a
    h_match_secondary := ia.h_match_secondary
    promises := by simpa only [← heq] using ia.promises
    h_row_constraints := ia.h_row_constraints
    arith_table := ia.arith_table
    arith_chunk_ranges := ia.arith_chunk_ranges
    arith_carry_ranges := ia.arith_carry_ranges
    h_rs1_value := by simpa only [← heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [← heq] using ia.h_rs2_value
    h_not_forge := ia.h_not_forge
  }

/-- Exact runtime projection for later dispatcher integration. -/
theorem canonicalMulhInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulh trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulh trace (chainedSailTrace steps init) i c) :
    (canonicalMulhInputsCore steps rowDecodes init i h_reg c pc hpc ia).mulh_input =
      canonicalMulhInput steps rowDecodes i c pc := rfl

/-- The factory preserves the whole original runtime input, not just used bits. -/
theorem canonicalMulhInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulh trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulh trace (chainedSailTrace steps init) i c) :
    (canonicalMulhInputsCore steps rowDecodes init i h_reg c pc hpc ia).mulh_input =
      ia.mulh_input :=
  (canonicalMulhInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (mulhInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- Runtime MULHSU input from the current register file and decoded registers.
The supplied PC is the existing current-state PC, not an operand from the old input. -/
noncomputable def canonicalMulhsuInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_mulhsu trace i) (pc : BitVec 64) : PureSpec.MulhsuInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- Successful reads uniquely determine the entire old MULHSU input,
including both full-width operands, destination and PC. -/
theorem mulhsuInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulhsu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulhsu trace (chainedSailTrace steps init) i c) :
    ia.mulhsu_input = canonicalMulhsuInput steps rowDecodes i c pc := by
  have hr1 : ia.mulhsu_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.promises.input_r1_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.mulhsu_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.promises.input_r2_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hrd : ia.mulhsu_input.rd = regidx_to_fin c.rd := ia.promises.input_rd_eq
  have hPC : ia.mulhsu_input.PC = pc := by
    exact Option.some.inj (ia.promises.input_pc_eq.symm.trans hpc)
  cases hinput : ia.mulhsu_input
  simp_all [canonicalMulhsuInput]

/-- Rebuild MULHSU's actual core with canonical runtime data. Whole-input
uniqueness transports every dependent fact; all provider, arithmetic and forge
witnesses remain those of the original core. -/
noncomputable def canonicalMulhsuInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulhsu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulhsu trace (chainedSailTrace steps init) i c) :
    InputsCore_mulhsu trace (chainedSailTrace steps init) i c := by
  have heq := mulhsuInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    mulhsu_input := canonicalMulhsuInput steps rowDecodes i c pc
    v := ia.v
    r_a := ia.r_a
    h_match_secondary := ia.h_match_secondary
    promises := by simpa only [← heq] using ia.promises
    h_row_constraints := ia.h_row_constraints
    arith_table := ia.arith_table
    arith_chunk_ranges := ia.arith_chunk_ranges
    arith_carry_ranges := ia.arith_carry_ranges
    h_rs1_value := by simpa only [← heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [← heq] using ia.h_rs2_value
    h_not_forge := ia.h_not_forge
  }

/-- Exact runtime projection for later dispatcher integration. -/
theorem canonicalMulhsuInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulhsu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulhsu trace (chainedSailTrace steps init) i c) :
    (canonicalMulhsuInputsCore steps rowDecodes init i h_reg c pc hpc ia).mulhsu_input =
      canonicalMulhsuInput steps rowDecodes i c pc := rfl

/-- The factory preserves the whole original runtime input, not just used bits. -/
theorem canonicalMulhsuInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulhsu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulhsu trace (chainedSailTrace steps init) i c) :
    (canonicalMulhsuInputsCore steps rowDecodes init i h_reg c pc hpc ia).mulhsu_input =
      ia.mulhsu_input :=
  (canonicalMulhsuInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (mulhsuInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- Runtime MULHU input from the current register file and decoded registers.
The supplied PC is the existing current-state PC, not an operand from the old input. -/
noncomputable def canonicalMulhuInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_mulhu trace i) (pc : BitVec 64) : PureSpec.MulhuInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- Successful reads uniquely determine the entire old MULHU input,
including both full-width operands, destination and PC. -/
theorem mulhuInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulhu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulhu trace (chainedSailTrace steps init) i c) :
    ia.mulhu_input = canonicalMulhuInput steps rowDecodes i c pc := by
  have hr1 : ia.mulhu_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.mulhu_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hrd : ia.mulhu_input.rd = regidx_to_fin c.rd := ia.h_input_rd
  have hPC : ia.mulhu_input.PC = pc := by
    exact Option.some.inj (ia.h_input_pc.symm.trans hpc)
  cases hinput : ia.mulhu_input
  simp_all [canonicalMulhuInput]

/-- Rebuild MULHU's actual core with canonical runtime data. Whole-input
uniqueness transports every dependent fact; all provider, arithmetic and forge
witnesses remain those of the original core. -/
noncomputable def canonicalMulhuInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulhu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulhu trace (chainedSailTrace steps init) i c) :
    InputsCore_mulhu trace (chainedSailTrace steps init) i c := by
  have heq := mulhuInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    mulhu_input := canonicalMulhuInput steps rowDecodes i c pc
    h_input_r1 := by simpa only [← heq] using ia.h_input_r1
    h_input_r2 := by simpa only [← heq] using ia.h_input_r2
    h_input_pc := by simpa only [← heq] using ia.h_input_pc
    h_input_rd := by simpa only [← heq] using ia.h_input_rd
    h_rs1_value := by simpa only [← heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [← heq] using ia.h_rs2_value
  }

/-- Exact runtime projection for later dispatcher integration. -/
theorem canonicalMulhuInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulhu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulhu trace (chainedSailTrace steps init) i c) :
    (canonicalMulhuInputsCore steps rowDecodes init i h_reg c pc hpc ia).mulhu_input =
      canonicalMulhuInput steps rowDecodes i c pc := rfl

/-- The factory preserves the whole original runtime input, not just used bits. -/
theorem canonicalMulhuInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulhu trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulhu trace (chainedSailTrace steps init) i c) :
    (canonicalMulhuInputsCore steps rowDecodes init i h_reg c pc hpc ia).mulhu_input =
      ia.mulhu_input :=
  (canonicalMulhuInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (mulhuInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

/-- Runtime MULW input from the current register file and decoded registers.
The supplied PC is the existing current-state PC, not an operand from the old input. -/
noncomputable def canonicalMulwInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_mulw trace i) (pc : BitVec 64) : PureSpec.MulwInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- Successful reads uniquely determine the entire old MULW input,
including both full-width operands, destination and PC. -/
theorem mulwInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulw trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulw trace (chainedSailTrace steps init) i c) :
    ia.mulw_input = canonicalMulwInput steps rowDecodes i c pc := by
  have hr1 : ia.mulw_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h with hval
  have hr2 : ia.mulw_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h with hval
  have hrd : ia.mulw_input.rd = regidx_to_fin c.rd := ia.h_input_rd
  have hPC : ia.mulw_input.PC = pc := by
    exact Option.some.inj (ia.h_input_pc.symm.trans hpc)
  cases hinput : ia.mulw_input
  simp_all [canonicalMulwInput]

/-- Rebuild MULW's actual core with canonical runtime data. Whole-input
uniqueness transports every dependent fact; all provider, arithmetic and forge
witnesses remain those of the original core. -/
noncomputable def canonicalMulwInputsCore
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulw trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulw trace (chainedSailTrace steps init) i c) :
    InputsCore_mulw trace (chainedSailTrace steps init) i c := by
  have heq := mulwInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia
  exact {
    mulw_input := canonicalMulwInput steps rowDecodes i c pc
    h_input_r1 := by simpa only [← heq] using ia.h_input_r1
    h_input_r2 := by simpa only [← heq] using ia.h_input_r2
    h_input_pc := by simpa only [← heq] using ia.h_input_pc
    h_input_rd := by simpa only [← heq] using ia.h_input_rd
    h_a23 := ia.h_a23
    h_b23 := ia.h_b23
    h_sext_choice := ia.h_sext_choice
    h_rs1_value := by simpa only [← heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [← heq] using ia.h_rs2_value
  }

/-- Exact runtime projection for later dispatcher integration. -/
theorem canonicalMulwInputsCore_input
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulw trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulw trace (chainedSailTrace steps init) i c) :
    (canonicalMulwInputsCore steps rowDecodes init i h_reg c pc hpc ia).mulw_input =
      canonicalMulwInput steps rowDecodes i c pc := rfl

/-- The factory preserves the whole original runtime input, not just used bits. -/
theorem canonicalMulwInputsCore_input_eq_original
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (c : Claim_mulw trace i) (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (ia : InputsCore_mulw trace (chainedSailTrace steps init) i c) :
    (canonicalMulwInputsCore steps rowDecodes init i h_reg c pc hpc ia).mulw_input =
      ia.mulw_input :=
  (canonicalMulwInputsCore_input steps rowDecodes init i h_reg c pc hpc ia).trans
    (mulwInput_eq_canonical steps rowDecodes init i h_reg c pc hpc ia).symm

end ZiskFv.Compliance
