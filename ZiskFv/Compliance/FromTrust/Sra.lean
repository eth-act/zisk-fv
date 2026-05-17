import Mathlib

import ZiskFv.Equivalence.Sra
import ZiskFv.Equivalence.Promises.RType
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Compliance.SharedBundles

/-! `equiv_SRA` Compliance wrapper — BinaryExtension (signed shift,
    OP_SRA = 0x23). RTYPE form. The signed-vs-unsigned distinction
    is handled inside the canonical theorem via the BinaryExtension
    AIR's op-routed semantics; no extra sign-witness pin needed at
    the wrapper level — `op_bus_perm_sound_BinaryExtension`'s
    disjunction member is enough. -/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SRA_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sra_input : PureSpec.SraInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state sra_input.r1_val sra_input.r2_val sra_input.rd sra_input.PC
        (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  -- OP_SRA = 0x23: disjunction member #3.
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryExtension m v r_main h_main_active
      (Or.inr (Or.inr (Or.inl h_main_op)))
  exact ZiskFv.Equivalence.Sra.equiv_SRA state sra_input r1 r2 rd
    m v r_main r_binary
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h_main_active, h_main_op⟩
    h_match h_lane_rd

end ZiskFv.Compliance
