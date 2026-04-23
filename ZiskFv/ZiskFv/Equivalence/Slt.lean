import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Slt
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.SltEquivHelper
import ZiskFv.RV64D.BusEffect
import ZiskFv.Tactics.ALURTypeArchetype

/-!
End-to-end theorem for RV64 SLT (Phase 3C T-RT4). Mirrors
`Equivalence.Sub` shape with `OP_SUB → OP_LT` and `rop.SUB → rop.SLT`.

**Escape-hatch note.** Phase 3B shipped `ZiskFv/RV64D/slt.lean` with
a `execute_RTYPE_slt_pure_equiv` lemma whose proof fails to discharge
the final `BitVec.setWidth 64 (if .toInt < then 1#1 else 0#1)` /
`if .slt then 1#64 else 0#64` equivalence (see
`ZiskFv/RV64D/SltEquivHelper.lean` docstring). This module does not
import the broken upstream file; it consumes the narrow escape-hatch
axiom `PureSpec.slt_pure_equiv_axiom` (catalogued as C5 in
`docs/fv/trusted-base.md`) from the helper.

The archetype / circuit-level piece (`equiv_SLT`) is unaffected and
closes from `slt_compositional` verbatim.
-/

namespace ZiskFv.Equivalence.Slt

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Slt
open ZiskFv.Tactics.ALURTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SLT
    (_rs1 _rs2 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : slt_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  slt_compositional m r_main bus_entry h_circuit

theorem equiv_SLT_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slt_input : PureSpec.SltInput')
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok slt_input.r2_val state)
    (h_input_rd : slt_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slt_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
      = let slt_output := PureSpec.slt_pure slt_input
        (do
          Sail.writeReg Register.nextPC slt_output.nextPC
          match slt_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.slt_pure_equiv_axiom
    slt_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

theorem equiv_SLT_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slt_input : PureSpec.SltInput')
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok slt_input.r2_val state)
    (h_input_rd : slt_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slt_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.slt_pure slt_input).nextPC)
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
      (match (PureSpec.slt_pure slt_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SLT_sail state slt_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.slt_pure slt_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.slt_pure slt_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.Slt
