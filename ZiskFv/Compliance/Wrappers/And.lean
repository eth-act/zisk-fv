import Mathlib

import ZiskFv.EquivCore.And
import ZiskFv.Compliance.ParametricStaticBinary
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.AirsClean.Binary.Trace
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_AND` Compliance wrapper — Binary mode-pin shape

Canonical wrapper delegates to the Clean/static provider core. Trust footprint is tracked by the regenerated caller-burden and axiom-closure ledgers.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.AirsClean.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


lemma equiv_AND
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (and_input : PureSpec.AndInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (evidence : ZiskFv.Compliance.StaticBinaryRTypeEvidence
      m r_main bus OP_AND and_input.r1_val and_input.r2_val)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state and_input.r1_val and_input.r2_val and_input.rd and_input.PC
        (PureSpec.execute_RTYPE_and_pure and_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.AND))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  apply ZiskFv.Compliance.ParametricStaticBinary.dischargeRType evidence
  intro row pins h_match h_row_spec h_core h_static_specs h_facts
    h_input_r1_row h_input_r2_row h_lane_rd
  exact ZiskFv.EquivCore.And.equiv_AND_of_static_row
    state and_input r1 r2 rd m row r_main bus promises pins
    h_match h_row_spec h_core h_static_specs h_facts
    h_input_r1_row
    h_input_r2_row
    h_lane_rd

end ZiskFv.Compliance
