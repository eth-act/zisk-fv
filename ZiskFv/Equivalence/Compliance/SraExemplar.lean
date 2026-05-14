import Mathlib

import ZiskFv.Equivalence.Sra
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension

/-! `equiv_SRA` Compliance wrapper — BinaryExtension (signed shift,
    OP_SRA = 0x23). RTYPE form. The signed-vs-unsigned distinction
    is handled inside the canonical theorem via the BinaryExtension
    AIR's op-routed semantics; no extra sign-witness pin needed at
    the wrapper level — `op_bus_perm_sound_BinaryExtension`'s
    disjunction member is enough. -/

namespace ZiskFv.Equivalence.Compliance

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
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sra_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sra_input.r2_val state)
    (h_input_rd : sra_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sra_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sra_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- OP_SRA = 0x23: disjunction member #3.
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryExtension m v r_main h_main_active
      (Or.inr (Or.inr (Or.inl h_main_op)))
  exact ZiskFv.Equivalence.Sra.equiv_SRA state sra_input r1 r2 rd
    m v r_main r_binary exec_row e0 e1 e2
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_match h_lane_rd

end ZiskFv.Equivalence.Compliance
