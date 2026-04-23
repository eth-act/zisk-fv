import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Sltu
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.SltEquivHelper
import ZiskFv.RV64D.BusEffect
import ZiskFv.Tactics.ALURTypeArchetype

/-!
End-to-end theorem for RV64 SLTU (Phase 3C T-RT5). Mirrors
`Equivalence.Slt` shape with `OP_LT → OP_LTU` and
`rop.SLT → rop.SLTU`.

Same escape-hatch note as `Equivalence.Slt` — the Phase 3B
`execute_RTYPE_sltu_pure_equiv` in `ZiskFv/RV64D/sltu.lean` has the
same BitVec-setWidth-bridge gap as SLT; this module consumes
`PureSpec.sltu_pure_equiv_axiom` from
`ZiskFv/RV64D/SltEquivHelper.lean` (catalogued as C6).
-/

namespace ZiskFv.Equivalence.Sltu

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Sltu
open ZiskFv.Tactics.ALURTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SLTU
    (_rs1 _rs2 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : sltu_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  sltu_compositional m r_main bus_entry h_circuit

theorem equiv_SLTU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltu_input : PureSpec.SltuInput')
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sltu_input.r2_val state)
    (h_input_rd : sltu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltu_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
      = let sltu_output := PureSpec.sltu_pure sltu_input
        (do
          Sail.writeReg Register.nextPC sltu_output.nextPC
          match sltu_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.sltu_pure_equiv_axiom
    sltu_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

theorem equiv_SLTU_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltu_input : PureSpec.SltuInput')
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sltu_input.r2_val state)
    (h_input_rd : sltu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.sltu_pure sltu_input).nextPC)
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
      (match (PureSpec.sltu_pure sltu_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SLTU_sail state sltu_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.sltu_pure sltu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.sltu_pure sltu_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.Sltu
