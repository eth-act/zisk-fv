import ZiskFv.Vm.Probe_Mul

/-!
# `equiv_MULW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for MULW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding Probe theorem `ZiskFv.Vm.Probe.equiv_MULW_v2`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/Equivalence_v1/MulW.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Vm.Probe.equiv_MULW_v2`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.ArithMul (Valid_ArithMul)
open ZiskFv.Airs.OperationBus (matches_entry opBus_row_Main)
open ZiskFv.Airs.ArithMul (opBus_row_Arith opBus_row_ArithMulSecondary)
open ZiskFv.Trusted (OP_MUL OP_MULH OP_MULU OP_MULUH OP_MULSUH OP_MUL_W)

namespace ZiskFv.Equivalence.MulW


theorem equiv_MULW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MUL_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main) (opBus_row_Arith v r_a))
    (promises : ZiskFv.Equivalence_v1.Promises.RTypePromises
        state mulw_input.r1_val mulw_input.r2_val mulw_input.rd mulw_input.PC
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints : ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (h_sext_choice :
      ((bus.e2.x4.val = 0 ∧ bus.e2.x5.val = 0 ∧ bus.e2.x6.val = 0 ∧ bus.e2.x7.val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      ((bus.e2.x4.val = 255 ∧ bus.e2.x5.val = 255 ∧ bus.e2.x6.val = 255 ∧ bus.e2.x7.val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ) - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ) - (v.nb r_a).val * (2:ℤ)^32)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.MULW (r2, r1, rd))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state :=
  ZiskFv.Vm.Probe.equiv_MULW_v2 state mulw_input r1 r2 rd bus m r_main v r_a pins h_match_primary promises h_row_constraints h_sext_choice h_rs1_value h_rs2_value

end ZiskFv.Equivalence.MulW
