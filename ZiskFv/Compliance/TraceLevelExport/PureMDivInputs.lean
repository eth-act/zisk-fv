import ZiskFv.Compliance.TraceLevelExport.PureInputRegisters
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem

namespace ZiskFv.Compliance

-- Keep provider computations opaque when rebuilding their dependent witnesses.
seal divuArow divuwArow remuArow remuwArow

variable {n : ℕ} {trace : AcceptedZiskTrace n}

/-!
Canonical DIV/REM runtime inputs use the decoded registers and current register
agreement, with the current PC supplied by its existing presence witness. The
whole-input certificates follow from uniqueness of the two successful reads,
the decoded destination, and PC presence. Core reconstruction retains the exact
provider, row, range, partial-constraint, remainder-bound and forge witnesses;
in particular no remainder or multiplicity is normalized.
-/

/-- Rebuild the entire DIV runtime input from current registers and decoded indices. -/
noncomputable def canonicalDivInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_div trace i) (pc : BitVec 64) : PureSpec.DivInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- The original whole DIV input is forced by its actual successful reads. -/
theorem divInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_div trace i)
    (ia : InputsCore_div trace (chainedSailTrace steps init) i c) :
    ia.div_input = canonicalDivInput steps rowDecodes i c pc := by
  have hr1 : ia.div_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.promises.input_r1_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h
  have hr2 : ia.div_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.promises.input_r2_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h
  have hp : ia.div_input.PC = pc :=
    Option.some.inj (ia.promises.input_pc_eq.symm.trans hpc)
  have hrd := ia.promises.input_rd_eq
  cases hinput : ia.div_input
  simp_all [canonicalDivInput]

/-- Construct a canonical DIV core, retaining every existing arithmetic witness. -/
noncomputable def divInputsCoreOfRegAgree
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_div trace i)
    (ia : InputsCore_div trace (chainedSailTrace steps init) i c) :
    InputsCore_div trace (chainedSailTrace steps init) i c := by
  have heq := divInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia
  exact {
    ia with
    div_input := canonicalDivInput steps rowDecodes i c pc
    promises := {
      ia.promises with
      input_r1_eq := read_pureInputRegValue steps rowDecodes init i h_reg _
      input_r2_eq := read_pureInputRegValue steps rowDecodes init i h_reg _
      input_rd_eq := rfl
      input_pc_eq := hpc }
    h_rs1_value := by simpa only [heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [heq] using ia.h_rs2_value
  }

/-- Exact whole-input certificate for replacing the DIV PureInputs case. -/
theorem divInputsCoreOfRegAgree_input_eq
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_div trace i)
    (ia : InputsCore_div trace (chainedSailTrace steps init) i c) :
    ia.div_input =
      (divInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia).div_input := by
  change ia.div_input = canonicalDivInput steps rowDecodes i c pc
  exact divInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia

/-- Rebuild the entire REM runtime input from current registers and decoded indices. -/
noncomputable def canonicalRemInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_rem trace i) (pc : BitVec 64) : PureSpec.RemInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- The original whole REM input is forced by its actual successful reads. -/
theorem remInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_rem trace i)
    (ia : InputsCore_rem trace (chainedSailTrace steps init) i c) :
    ia.rem_input = canonicalRemInput steps rowDecodes i c pc := by
  have hr1 : ia.rem_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.promises.input_r1_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h
  have hr2 : ia.rem_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.promises.input_r2_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h
  have hp : ia.rem_input.PC = pc :=
    Option.some.inj (ia.promises.input_pc_eq.symm.trans hpc)
  have hrd := ia.promises.input_rd_eq
  cases hinput : ia.rem_input
  simp_all [canonicalRemInput]

/-- Construct a canonical REM core, retaining every existing arithmetic witness. -/
noncomputable def remInputsCoreOfRegAgree
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_rem trace i)
    (ia : InputsCore_rem trace (chainedSailTrace steps init) i c) :
    InputsCore_rem trace (chainedSailTrace steps init) i c := by
  have heq := remInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia
  exact {
    ia with
    rem_input := canonicalRemInput steps rowDecodes i c pc
    promises := {
      ia.promises with
      input_r1_eq := read_pureInputRegValue steps rowDecodes init i h_reg _
      input_r2_eq := read_pureInputRegValue steps rowDecodes init i h_reg _
      input_rd_eq := rfl
      input_pc_eq := hpc }
    h_rs1_value := by simpa only [heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [heq] using ia.h_rs2_value
    h_r_le := by simpa only [heq] using ia.h_r_le
    h_r_sign := by simpa only [heq] using ia.h_r_sign
    h_not_forge := by simpa only [heq] using ia.h_not_forge
  }

/-- Exact whole-input certificate for replacing the REM PureInputs case. -/
theorem remInputsCoreOfRegAgree_input_eq
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_rem trace i)
    (ia : InputsCore_rem trace (chainedSailTrace steps init) i c) :
    ia.rem_input =
      (remInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia).rem_input := by
  change ia.rem_input = canonicalRemInput steps rowDecodes i c pc
  exact remInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia

/-- Rebuild the entire DIVW runtime input from current registers and decoded indices. -/
noncomputable def canonicalDivwInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_divw trace i) (pc : BitVec 64) : PureSpec.DivwInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- The original whole DIVW input is forced by its actual successful reads. -/
theorem divwInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_divw trace i)
    (ia : InputsCore_divw trace (chainedSailTrace steps init) i c) :
    ia.divw_input = canonicalDivwInput steps rowDecodes i c pc := by
  have hr1 : ia.divw_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.promises.input_r1_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h
  have hr2 : ia.divw_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.promises.input_r2_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h
  have hp : ia.divw_input.PC = pc :=
    Option.some.inj (ia.promises.input_pc_eq.symm.trans hpc)
  have hrd := ia.promises.input_rd_eq
  cases hinput : ia.divw_input
  simp_all [canonicalDivwInput]

/-- Construct a canonical DIVW core, retaining every existing arithmetic witness. -/
noncomputable def divwInputsCoreOfRegAgree
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_divw trace i)
    (ia : InputsCore_divw trace (chainedSailTrace steps init) i c) :
    InputsCore_divw trace (chainedSailTrace steps init) i c := by
  have heq := divwInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia
  exact {
    ia with
    divw_input := canonicalDivwInput steps rowDecodes i c pc
    promises := {
      ia.promises with
      input_r1_eq := read_pureInputRegValue steps rowDecodes init i h_reg _
      input_r2_eq := read_pureInputRegValue steps rowDecodes init i h_reg _
      input_rd_eq := rfl
      input_pc_eq := hpc }
    h_rs1_value := by simpa only [heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [heq] using ia.h_rs2_value
    h_r_le := by simpa only [heq] using ia.h_r_le
    h_r_sign := by simpa only [heq] using ia.h_r_sign
    h_not_forge := by simpa only [heq] using ia.h_not_forge
  }

/-- Exact whole-input certificate for replacing the DIVW PureInputs case. -/
theorem divwInputsCoreOfRegAgree_input_eq
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_divw trace i)
    (ia : InputsCore_divw trace (chainedSailTrace steps init) i c) :
    ia.divw_input =
      (divwInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia).divw_input := by
  change ia.divw_input = canonicalDivwInput steps rowDecodes i c pc
  exact divwInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia

/-- Rebuild the entire REMW runtime input from current registers and decoded indices. -/
noncomputable def canonicalRemwInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_remw trace i) (pc : BitVec 64) : PureSpec.RemwInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- The original whole REMW input is forced by its actual successful reads. -/
theorem remwInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_remw trace i)
    (ia : InputsCore_remw trace (chainedSailTrace steps init) i c) :
    ia.remw_input = canonicalRemwInput steps rowDecodes i c pc := by
  have hr1 : ia.remw_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.promises.input_r1_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h
  have hr2 : ia.remw_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.promises.input_r2_eq.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h
  have hp : ia.remw_input.PC = pc :=
    Option.some.inj (ia.promises.input_pc_eq.symm.trans hpc)
  have hrd := ia.promises.input_rd_eq
  cases hinput : ia.remw_input
  simp_all [canonicalRemwInput]

/-- Construct a canonical REMW core, retaining every existing arithmetic witness. -/
noncomputable def remwInputsCoreOfRegAgree
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_remw trace i)
    (ia : InputsCore_remw trace (chainedSailTrace steps init) i c) :
    InputsCore_remw trace (chainedSailTrace steps init) i c := by
  have heq := remwInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia
  exact {
    ia with
    remw_input := canonicalRemwInput steps rowDecodes i c pc
    promises := {
      ia.promises with
      input_r1_eq := read_pureInputRegValue steps rowDecodes init i h_reg _
      input_r2_eq := read_pureInputRegValue steps rowDecodes init i h_reg _
      input_rd_eq := rfl
      input_pc_eq := hpc }
    h_rs1_value := by simpa only [heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [heq] using ia.h_rs2_value
    h_r_le := by simpa only [heq] using ia.h_r_le
    h_r_sign := by simpa only [heq] using ia.h_r_sign
    h_not_forge := by simpa only [heq] using ia.h_not_forge
  }

/-- Exact whole-input certificate for replacing the REMW PureInputs case. -/
theorem remwInputsCoreOfRegAgree_input_eq
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_remw trace i)
    (ia : InputsCore_remw trace (chainedSailTrace steps init) i c) :
    ia.remw_input =
      (remwInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia).remw_input := by
  change ia.remw_input = canonicalRemwInput steps rowDecodes i c pc
  exact remwInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia

/-- Rebuild the entire DIVU runtime input from current registers and decoded indices. -/
noncomputable def canonicalDivuInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_divu trace i) (pc : BitVec 64) : PureSpec.DivuInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- The original whole DIVU input is forced by its actual successful reads. -/
theorem divuInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_divu trace i)
    (ia : InputsCore_divu trace (chainedSailTrace steps init) i c) :
    ia.divu_input = canonicalDivuInput steps rowDecodes i c pc := by
  have hr1 : ia.divu_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h
  have hr2 : ia.divu_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h
  have hp : ia.divu_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  have hrd := ia.h_input_rd
  cases hinput : ia.divu_input
  simp_all [canonicalDivuInput]

/-- Construct a canonical DIVU core, retaining every existing arithmetic witness. -/
noncomputable def divuInputsCoreOfRegAgree
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_divu trace i)
    (ia : InputsCore_divu trace (chainedSailTrace steps init) i c) :
    InputsCore_divu trace (chainedSailTrace steps init) i c := by
  have heq := divuInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia
  exact {
    ia with
    divu_input := canonicalDivuInput steps rowDecodes i c pc
    h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_rd := rfl
    h_input_pc := hpc
    h_rs1_value := by simpa only [heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [heq] using ia.h_rs2_value
  }

/-- Exact whole-input certificate for replacing the DIVU PureInputs case. -/
theorem divuInputsCoreOfRegAgree_input_eq
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_divu trace i)
    (ia : InputsCore_divu trace (chainedSailTrace steps init) i c) :
    ia.divu_input =
      (divuInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia).divu_input := by
  change ia.divu_input = canonicalDivuInput steps rowDecodes i c pc
  exact divuInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia

/-- Rebuild the entire DIVUW runtime input from current registers and decoded indices. -/
noncomputable def canonicalDivuwInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_divuw trace i) (pc : BitVec 64) : PureSpec.DivuwInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- The original whole DIVUW input is forced by its actual successful reads. -/
theorem divuwInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_divuw trace i)
    (ia : InputsCore_divuw trace (chainedSailTrace steps init) i c) :
    ia.divuw_input = canonicalDivuwInput steps rowDecodes i c pc := by
  have hr1 : ia.divuw_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h
  have hr2 : ia.divuw_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h
  have hp : ia.divuw_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  have hrd := ia.h_input_rd
  cases hinput : ia.divuw_input
  simp_all [canonicalDivuwInput]

/-- Construct a canonical DIVUW core, retaining every existing arithmetic witness. -/
noncomputable def divuwInputsCoreOfRegAgree
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_divuw trace i)
    (ia : InputsCore_divuw trace (chainedSailTrace steps init) i c) :
    InputsCore_divuw trace (chainedSailTrace steps init) i c := by
  have heq := divuwInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia
  exact {
    ia with
    divuw_input := canonicalDivuwInput steps rowDecodes i c pc
    h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_rd := rfl
    h_input_pc := hpc
    h_rs1_value := by simpa only [heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [heq] using ia.h_rs2_value
  }

/-- Exact whole-input certificate for replacing the DIVUW PureInputs case. -/
theorem divuwInputsCoreOfRegAgree_input_eq
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_divuw trace i)
    (ia : InputsCore_divuw trace (chainedSailTrace steps init) i c) :
    ia.divuw_input =
      (divuwInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia).divuw_input := by
  change ia.divuw_input = canonicalDivuwInput steps rowDecodes i c pc
  exact divuwInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia

/-- Rebuild the entire REMU runtime input from current registers and decoded indices. -/
noncomputable def canonicalRemuInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_remu trace i) (pc : BitVec 64) : PureSpec.RemuInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- The original whole REMU input is forced by its actual successful reads. -/
theorem remuInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_remu trace i)
    (ia : InputsCore_remu trace (chainedSailTrace steps init) i c) :
    ia.remu_input = canonicalRemuInput steps rowDecodes i c pc := by
  have hr1 : ia.remu_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h
  have hr2 : ia.remu_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h
  have hp : ia.remu_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  have hrd := ia.h_input_rd
  cases hinput : ia.remu_input
  simp_all [canonicalRemuInput]

/-- Construct a canonical REMU core, retaining every existing arithmetic witness. -/
noncomputable def remuInputsCoreOfRegAgree
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_remu trace i)
    (ia : InputsCore_remu trace (chainedSailTrace steps init) i c) :
    InputsCore_remu trace (chainedSailTrace steps init) i c := by
  have heq := remuInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia
  exact {
    ia with
    remu_input := canonicalRemuInput steps rowDecodes i c pc
    h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_rd := rfl
    h_input_pc := hpc
    h_rs1_value := by simpa only [heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [heq] using ia.h_rs2_value
  }

/-- Exact whole-input certificate for replacing the REMU PureInputs case. -/
theorem remuInputsCoreOfRegAgree_input_eq
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_remu trace i)
    (ia : InputsCore_remu trace (chainedSailTrace steps init) i c) :
    ia.remu_input =
      (remuInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia).remu_input := by
  change ia.remu_input = canonicalRemuInput steps rowDecodes i c pc
  exact remuInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia

/-- Rebuild the entire REMUW runtime input from current registers and decoded indices. -/
noncomputable def canonicalRemuwInput
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (i : Fin n) (c : Claim_remuw trace i) (pc : BitVec 64) : PureSpec.RemuwInput where
  r1_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1)
  r2_val := pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2)
  rd := regidx_to_fin c.rd
  PC := pc

/-- The original whole REMUW input is forced by its actual successful reads. -/
theorem remuwInput_eq_canonical
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_remuw trace i)
    (ia : InputsCore_remuw trace (chainedSailTrace steps init) i c) :
    ia.remuw_input = canonicalRemuwInput steps rowDecodes i c pc := by
  have hr1 : ia.remuw_input.r1_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r1) := by
    have h := ia.h_input_r1.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r1))
    injection h
  have hr2 : ia.remuw_input.r2_val =
      pureInputRegValue steps rowDecodes i.val (regidx_to_fin c.r2) := by
    have h := ia.h_input_r2.symm.trans
      (read_pureInputRegValue steps rowDecodes init i h_reg (regidx_to_fin c.r2))
    injection h
  have hp : ia.remuw_input.PC = pc :=
    Option.some.inj (ia.h_input_pc.symm.trans hpc)
  have hrd := ia.h_input_rd
  cases hinput : ia.remuw_input
  simp_all [canonicalRemuwInput]

/-- Construct a canonical REMUW core, retaining every existing arithmetic witness. -/
noncomputable def remuwInputsCoreOfRegAgree
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_remuw trace i)
    (ia : InputsCore_remuw trace (chainedSailTrace steps init) i c) :
    InputsCore_remuw trace (chainedSailTrace steps init) i c := by
  have heq := remuwInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia
  exact {
    ia with
    remuw_input := canonicalRemuwInput steps rowDecodes i c pc
    h_input_r1 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_r2 := read_pureInputRegValue steps rowDecodes init i h_reg _
    h_input_rd := rfl
    h_input_pc := hpc
    h_rs1_value := by simpa only [heq] using ia.h_rs1_value
    h_rs2_value := by simpa only [heq] using ia.h_rs2_value
  }

/-- Exact whole-input certificate for replacing the REMUW PureInputs case. -/
theorem remuwInputsCoreOfRegAgree_input_eq
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val)
    (pc : BitVec 64)
    (hpc : (chainedSailTrace steps init i).regs.get? Register.PC = some pc)
    (c : Claim_remuw trace i)
    (ia : InputsCore_remuw trace (chainedSailTrace steps init) i c) :
    ia.remuw_input =
      (remuwInputsCoreOfRegAgree steps rowDecodes init i h_reg pc hpc c ia).remuw_input := by
  change ia.remuw_input = canonicalRemuwInput steps rowDecodes i c pc
  exact remuwInput_eq_canonical steps rowDecodes init i h_reg pc hpc c ia

end ZiskFv.Compliance
