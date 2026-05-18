import Mathlib

import ZiskFv.Equivalence.Xori
import ZiskFv.Equivalence.Promises.IType
import ZiskFv.Equivalence.Promises.BinaryHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_XORI` Compliance wrapper — Binary mode-pin ITYPE shape

Refactored to consume per-AIR helpers from
`Equivalence/Promises/BinaryHelpers.lean`. Trust footprint unchanged.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.Equivalence.Promises

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_XORI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xori_input : PureSpec.XoriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (h_xori_subset : itype_imm_subset_holds_main m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_xori⟩ := pins
  have h_op_disj := binary_op_disj_of_eq m r_main 16 h_main_op_xori (by tauto)
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_bop_or_sext :=
    binary_h_bop_or_sext_via_axiom h_match h_main_op_xori
      (binary_b_op_or_sext_eq_OP_XOR v r_binary)
  exact ZiskFv.Equivalence.Xori.equiv_XORI
    state xori_input r1 rd imm m v r_main r_binary
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h_main_active, h_main_op_xori⟩
    h_match h_bop_or_sext h_lane_rd h_xori_subset

end ZiskFv.Compliance
