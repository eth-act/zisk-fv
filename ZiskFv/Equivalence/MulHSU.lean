import ZiskFv.Compliance.Wrappers.MulHSU
import ZiskFv.Vm.StateEffect

/-!
# `equiv_MULHSU` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for MULHSU. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_MULHSU`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/MulHSU.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_MULHSU`'s closure exactly.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.ArithMul (Valid_ArithMul)
open ZiskFv.Airs.OperationBus (matches_entry opBus_row_Main)
open ZiskFv.Airs.ArithMul (opBus_row_Arith opBus_row_ArithMulSecondary)
open ZiskFv.Trusted (OP_MUL OP_MULH OP_MULU OP_MULUH OP_MULSUH OP_MUL_W)

namespace ZiskFv.Equivalence.MulHSU


theorem equiv_MULHSU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhsu_input : PureSpec.MulhsuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULSUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main) (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints : ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := .Signed, signed_rs2 := .Unsigned }))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Vm.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_MULHSU state mulhsu_input r1 r2 rd bus m r_main v r_a pins h_match_secondary promises h_row_constraints

end ZiskFv.Equivalence.MulHSU
