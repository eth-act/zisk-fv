import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Sltiu
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.sltiu
import ZiskFv.Sail.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.RdValDerivation.BinaryCompare

/-!
End-to-end theorem for RV64 SLTIU. Consumes
`PureSpec.execute_ITYPE_sltiu_pure_equiv` directly (C8 retired by
-/

namespace ZiskFv.Equivalence.Sltiu

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Sltiu
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
    (h_rd_idx : sltiu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = if sltiu_input.r1_val < (BitVec.signExtend 64 sltiu_input.imm)
        then 1#64 else 0#64) :
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
  simp only [PureSpec.execute_ITYPE_sltiu_pure, h_rd_idx]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · simp only [h_rd_zero, ↓reduceDIte]
  · simp only [h_rd_zero, ↓reduceDIte]
    rw [h_rd_val]

/-- **Tier-1: SLTIU without `h_rd_val` parameter**. -/
theorem equiv_SLTIU_metaplan_tier1
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
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
    (h_rd_idx : sltiu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : ZiskFv.Airs.Binary.consumer_byte_match_chain
      ZiskFv.Airs.BinaryTable.OP_LTU a7 b7 c7 cin7 fl7 pi7)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (ha4 : a4.val < 256) (ha5 : a5.val < 256) (ha6 : a6.val < 256) (ha7 : a7.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hb4 : b4.val < 256) (hb5 : b5.val < 256) (hb6 : b6.val < 256) (hb7 : b7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2)
    (h_match_clo : m.c_0 r_main = fl7)
    (h_match_chi : m.c_1 r_main = 0)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_fl7_lt_2 : fl7.val < 2)
    (h_input_r1_circuit : sltiu_input.r1_val
      = BitVec.ofNat 64
          (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
            + a4.val * 4294967296 + a5.val * 1099511627776
            + a6.val * 281474976710656 + a7.val * 72057594037927936))
    (h_input_imm_circuit : BitVec.signExtend 64 sltiu_input.imm
      = BitVec.ofNat 64
          (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
            + b4.val * 4294967296 + b5.val * 1099511627776
            + b6.val * 281474976710656 + b7.val * 72057594037927936)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_rd_val_bv :=
    ZiskFv.Equivalence.RdValDerivation.BinaryCompare.h_rd_val_compare_sltiu
      m r_main e2 sltiu_input.r1_val sltiu_input.imm
      a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7
      c0 c1 c2 c3 c4 c5 c6 c7
      cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
      fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
      pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7
      h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      h_cin0 h_cin1 h_cin2 h_cin3 h_cin4 h_cin5 h_cin6 h_cin7
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_fl7_lt_2 h_input_r1_circuit h_input_imm_circuit
  -- Bridge ult/<
  have h_iff : (sltiu_input.r1_val.ult (BitVec.signExtend 64 sltiu_input.imm) = true)
      ↔ (sltiu_input.r1_val < BitVec.signExtend 64 sltiu_input.imm) := by
    constructor
    · intro h
      rw [BitVec.lt_def]
      exact BitVec.ult_iff_lt.mp h
    · intro h
      rw [BitVec.lt_def] at h
      exact BitVec.ult_iff_lt.mpr h
  have h_rd_val :
      U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                  (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = if sltiu_input.r1_val < BitVec.signExtend 64 sltiu_input.imm
        then 1#64 else 0#64 := by
    rw [h_rd_val_bv]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd (h_iff.mp h₁) h₂
    · exact absurd (h_iff.mpr h₂) h₁
    · rfl
  exact equiv_SLTIU_metaplan state sltiu_input r1 rd imm exec_row e0 e1 e2
    h_input_r1 h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_rd_idx h_rd_val


/-- **Bus-precondition companion.** Drops `h_input_r1` / `h_input_r2` /
    `h_input_pc` / `h_input_rd` in favor of a single `h_bus :
    (bus_effect ...).1` plus ptr/value match hypotheses.
    Delegates to `equiv_SLTIU_metaplan` after chip_bus_hyps + match composition.  -/
theorem equiv_SLTIU_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_imm : sltiu_input.imm = imm)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r1_val : sltiu_input.r1_val
      = U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                    e0.x4, e0.x5, e0.x6, e0.x7])
    (h_pc : sltiu_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_idx : sltiu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = if sltiu_input.r1_val < (BitVec.signExtend 64 sltiu_input.imm)
        then 1#64 else 0#64) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = (bus_effect exec_row [e0, e1, e2] state).2
    := by
  obtain ⟨h_pc_read, h_rs1_read, h_rs2_read⟩ :=
    ZiskFv.Airs.BusHypotheses.chip_bus_hyps_alu_rrw
      state exec_row e0 e1 e2
      h_exec_len h_e0_mult h_e1_mult
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
      h_bus
  have h_input_r1 :
      read_xreg (regidx_to_fin r1) state
        = EStateM.Result.ok sltiu_input.r1_val state := by
    rw [h_r1_ptr, h_r1_val]; exact h_rs1_read
  have h_input_rd : sltiu_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some sltiu_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_SLTIU_metaplan state sltiu_input r1 rd imm exec_row e0 e1 e2 h_input_r1 h_input_imm h_input_rd h_input_pc h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_rd_val


/-- Constructor: build a `PureSpec.SltiuInput` from bus entries + imm. -/
def SltiuInput_of_bus
    (e0 e2 : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (imm : BitVec 12) :
    PureSpec.SltiuInput :=
  { r1_val := U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                          e0.x4, e0.x5, e0.x6, e0.x7]
    imm := imm
    rd := Transpiler.wrap_to_regidx e2.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Bus-self form for SLTIU.** Eliminates value-level match hyps via `SltiuInput_of_bus`. -/
theorem equiv_SLTIU_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 rd : regidx) (imm : BitVec 12)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_sltiu_pure (SltiuInput_of_bus e0 e2 exec_row imm)).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = if (SltiuInput_of_bus e0 e2 exec_row imm).r1_val < (BitVec.signExtend 64 (SltiuInput_of_bus e0 e2 exec_row imm).imm)
        then 1#64 else 0#64) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = (bus_effect exec_row [e0, e1, e2] state).2

    := by
  exact equiv_SLTIU_metaplan_from_bus state
    (SltiuInput_of_bus e0 e2 exec_row imm)
    r1 rd imm exec_row e0 e1 e2
    rfl
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_bus h_r1_ptr rfl rfl h_rd_ptr
    rfl h_rd_val

/-- **Op-bus companion for SLTIU.** Op-bus companion to
    `equiv_SLTIU_metaplan`: drops `h_input_r1` in favour of an op-bus
    precondition. Mirrors `equiv_ADD_metaplan_op_bus`. -/
theorem equiv_SLTIU_metaplan_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (op_entry : OperationBusEntry FGL)
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin r1) (regidx_to_fin r1)).1)
    (h_a_match :
      sltiu_input.r1_val = Goldilocks.lanes_to_bv64 op_entry.a_lo op_entry.a_hi)
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
    (h_rd_idx : sltiu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = if sltiu_input.r1_val < (BitVec.signExtend 64 sltiu_input.imm)
        then 1#64 else 0#64) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_r1_read := (ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_alu
      state op_entry (regidx_to_fin r1) (regidx_to_fin r1) h_op_mult h_op_bus).1
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltiu_input.r1_val state := by
    rw [h_a_match]; exact h_r1_read
  exact equiv_SLTIU_metaplan state sltiu_input r1 rd imm exec_row e0 e1 e2 h_input_r1 h_input_imm h_input_rd h_input_pc h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_rd_val

end ZiskFv.Equivalence.Sltiu
