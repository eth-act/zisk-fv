import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Sltiu
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.sltiu
import ZiskFv.RV64D.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype

/-!
End-to-end theorem for RV64 SLTIU (Phase 3C T-IT). Consumes
`PureSpec.execute_ITYPE_sltiu_pure_equiv` directly (C8 retired by
Phase 4 T-SLT).
-/

namespace ZiskFv.Equivalence.Sltiu

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Sltiu
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SLTIU
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : sltiu_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  sltiu_compositional m r_main bus_entry h_circuit

theorem equiv_SLTIU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltiu_input.r1_val state)
    (h_input_imm : sltiu_input.imm = imm)
    (h_input_rd : sltiu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltiu_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = let sltiu_output := PureSpec.execute_ITYPE_sltiu_pure sltiu_input
        (do
          Sail.writeReg Register.nextPC sltiu_output.nextPC
          match sltiu_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_ITYPE_sltiu_pure_equiv (state := state) (imm := imm)
    sltiu_input r1 rd h_input_r1 h_input_imm h_input_rd h_input_pc

theorem equiv_SLTIU_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltiu_input.r1_val state)
    (h_input_imm : sltiu_input.imm = imm)
    (h_input_rd : sltiu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltiu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_match :
      (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
        (pure () : SailM Unit)
      else
        let val := U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                                e2.x4, e2.x5, e2.x6, e2.x7]
        let reg_idx : Finset.Icc 1 31 :=
          ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
        write_xreg reg_idx val)
      =
      (match (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SLTIU_sail state sltiu_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.Sltiu
