import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Mul
import ZiskFv.Circuit.Remu
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.remu
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned

/-!
End-to-end theorem for RV64 **REMU**. REMU is the
**secondary** lane on an unsigned-DIV Arith row. Differs from
`Equivalence.Rem` only in the opcode literal (185 vs 187), the pure
spec (`execute_DIVREM_remu_pure` / `_equiv`), and the Sail instruction
payload (`instruction.REM (r2, r1, rd, true)`).

Three canonical theorems: `equiv_REMU`, `equiv_REMU_sail`,
`equiv_REMU_metaplan`. Arith-internal correctness (carry chains →
unsigned 64-bit remainder) is delegated to future audit.
-/

namespace ZiskFv.Equivalence.Remu

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Mul
open ZiskFv.Circuit.Remu
open ZiskFv.Tactics.ArithSMArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level REMU theorem.** Main's packed `c` equals Arith's
    packed remainder (`d[]`) under the REMU circuit-holds hypothesis.
    Wraps `Spec.Remu.remu_compositional`. -/
theorem equiv_REMU
    (_rs1 _rs2 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (v : Valid_ArithDiv C FGL FGL)
    (r_main r_arith : ℕ)
    (h_circuit : remu_circuit_holds m v r_main r_arith) :
    main_c_packed m r_main = arith_remainder_packed v r_arith :=
  remu_compositional m v r_main r_arith h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 REMU reduces to the pure-function block supplied by
    `PureSpec.execute_DIVREM_remu_pure`. Wraps
    `PureSpec.execute_DIVREM_remu_pure_equiv`. -/
theorem equiv_REMU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remu_input.r2_val state)
    (h_input_rd : remu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remu_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = let remu_output := PureSpec.execute_DIVREM_remu_pure remu_input
        (do
          Sail.writeReg Register.nextPC remu_output.nextPC
          match remu_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_remu_pure_equiv
    remu_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 REMU
    equals `(bus_effect exec_row mem_row state).2`. Composes
    `equiv_REMU_sail` with `bus_effect_matches_sail_alu_rrw` (shape
    (a), RRW). Structural bus hypotheses are parameterized
    audit derives them. -/
theorem equiv_REMU_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remu_input.r2_val state)
    (h_input_rd : remu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : remu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = (execute_DIV_REM_pure remu_input.r1_val remu_input.r2_val .DRU).2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_REMU_sail state remu_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_remu_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-- **Tier-1: REMU without `h_rd_val` parameter**.
    Derives `h_rd_val` internally via
    `RdValDerivation.MulDivRemUnsigned.h_rd_val_mdru_remu`, then forwards
    to `equiv_REMU_metaplan`. -/
theorem equiv_REMU_metaplan_tier1
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remu_input.r2_val state)
    (h_input_rd : remu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : remu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Tier-1 discharge parameters (DIV layout: a=quotient, b=divisor,
    -- c=dividend, d=remainder; bytes pack d[]).
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : FGL)
    (cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆ : FGL)
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_a0 : a₀.val < 65536) (h_a1 : a₁.val < 65536)
    (h_a2 : a₂.val < 65536) (h_a3 : a₃.val < 65536)
    (h_b0 : b₀.val < 65536) (h_b1 : b₁.val < 65536)
    (h_b2 : b₂.val < 65536) (h_b3 : b₃.val < 65536)
    (h_c0 : c₀.val < 65536) (h_c1 : c₁.val < 65536)
    (h_c2 : c₂.val < 65536) (h_c3 : c₃.val < 65536)
    (h_d0 : d₀.val < 65536) (h_d1 : d₁.val < 65536)
    (h_d2 : d₂.val < 65536) (h_d3 : d₃.val < 65536)
    (h_cy0 : cy₀.val < 131072) (h_cy1 : cy₁.val < 131072)
    (h_cy2 : cy₂.val < 131072) (h_cy3 : cy₃.val < 131072)
    (h_cy4 : cy₄.val < 131072) (h_cy5 : cy₅.val < 131072)
    (h_cy6 : cy₆.val < 131072)
    (hC31 : a₀ * b₀ + d₀ = c₀ + cy₀ * 65536)
    (hC32 : a₁ * b₀ + a₀ * b₁ + d₁ + cy₀ = c₁ + cy₁ * 65536)
    (hC33 : a₂ * b₀ + a₁ * b₁ + a₀ * b₂ + d₂ + cy₁ = c₂ + cy₂ * 65536)
    (hC34 : a₃ * b₀ + a₂ * b₁ + a₁ * b₂ + a₀ * b₃ + d₃ + cy₂
              = c₃ + cy₃ * 65536)
    (hC35 : a₃ * b₁ + a₂ * b₂ + a₁ * b₃ + cy₃ = cy₄ * 65536)
    (hC36 : a₃ * b₂ + a₂ * b₃ + cy₄ = cy₅ * 65536)
    (hC37 : a₃ * b₃ + cy₅ = cy₆ * 65536)
    (hC38 : cy₆ = 0)
    (h_byte_lo :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        = d₀.val + d₁.val * 65536)
    (h_byte_hi :
      e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
        = d₂.val + d₃.val * 65536)
    (h_op1 : remu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 c₀.val c₁.val c₂.val c₃.val)
    (h_op2 : remu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 b₀.val b₁.val b₂.val b₃.val)
    (h_op2_ne : remu_input.r2_val.toNat ≠ 0)
    (h_d_lt_b : ZiskFv.PackedBitVec.MulNoWrap.packed4 d₀.val d₁.val d₂.val d₃.val
                  < remu_input.r2_val.toNat) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned.h_rd_val_mdru_remu
      remu_input.r1_val remu_input.r2_val e2
      a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
      cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
      h0 h1 h2 h3 h4 h5 h6 h7
      h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
      h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
      h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
      h_byte_lo h_byte_hi h_op1 h_op2 h_op2_ne h_d_lt_b
  exact equiv_REMU_metaplan state remu_input r1 r2 rd exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_rd_idx h_rd_val


/-- **Bus-precondition companion.** Drops `h_input_r1` / `h_input_r2` /
    `h_input_pc` / `h_input_rd` in favor of a single `h_bus :
    (bus_effect ...).1` plus ptr/value match hypotheses.
    Delegates to `equiv_REMU_metaplan` after chip_bus_hyps + match composition.  -/
theorem equiv_REMU_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r1_val : remu_input.r1_val
      = U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                    e0.x4, e0.x5, e0.x6, e0.x7])
    (h_r2_ptr : regidx_to_fin r2 = Transpiler.wrap_to_regidx e1.ptr)
    (h_r2_val : remu_input.r2_val
      = U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                    e1.x4, e1.x5, e1.x6, e1.x7])
    (h_pc : remu_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_idx : remu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = (execute_DIV_REM_pure remu_input.r1_val remu_input.r2_val .DRU).2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
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
        = EStateM.Result.ok remu_input.r1_val state := by
    rw [h_r1_ptr, h_r1_val]; exact h_rs1_read
  have h_input_r2 :
      read_xreg (regidx_to_fin r2) state
        = EStateM.Result.ok remu_input.r2_val state := by
    rw [h_r2_ptr, h_r2_val]; exact h_rs2_read
  have h_input_rd : remu_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some remu_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_REMU_metaplan state remu_input r1 r2 rd exec_row e0 e1 e2 h_input_r1 h_input_r2 h_input_rd h_input_pc h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_rd_val


/-- Constructor: build a `PureSpec.RemuInput` from bus entries. -/
def RemuInput_of_bus
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL)) :
    PureSpec.RemuInput :=
  { r1_val := U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                          e0.x4, e0.x5, e0.x6, e0.x7]
    r2_val := U64.toBV #v[e1.x0, e1.x1, e1.x2, e1.x3,
                          e1.x4, e1.x5, e1.x6, e1.x7]
    rd := Transpiler.wrap_to_regidx e2.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Bus-self form for REMU.** Eliminates value-level match hyps via `RemuInput_of_bus`. -/
theorem equiv_REMU_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remu_pure (RemuInput_of_bus e0 e1 e2 exec_row)).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r2_ptr : regidx_to_fin r2 = Transpiler.wrap_to_regidx e1.ptr)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = (execute_DIV_REM_pure (RemuInput_of_bus e0 e1 e2 exec_row).r1_val (RemuInput_of_bus e0 e1 e2 exec_row).r2_val .DRU).2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2

    := by
  exact equiv_REMU_metaplan_from_bus state
    (RemuInput_of_bus e0 e1 e2 exec_row) r1 r2 rd
    exec_row e0 e1 e2
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_bus h_r1_ptr rfl h_r2_ptr rfl rfl h_rd_ptr
    rfl h_rd_val

/-- **Op-bus companion for REMU.** Op-bus companion to
    `equiv_REMU_metaplan`: drops `h_input_r1` / `h_input_r2` in
    favour of an op-bus precondition. Mirrors
    `equiv_ADD_metaplan_op_bus`. -/
theorem equiv_REMU_metaplan_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (op_entry : OperationBusEntry FGL)
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin r1) (regidx_to_fin r2)).1)
    (h_a_match :
      remu_input.r1_val = Goldilocks.lanes_to_bv64 op_entry.a_lo op_entry.a_hi)
    (h_b_match :
      remu_input.r2_val = Goldilocks.lanes_to_bv64 op_entry.b_lo op_entry.b_hi)
    (h_input_rd : remu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : remu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = (execute_DIV_REM_pure remu_input.r1_val remu_input.r2_val .DRU).2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨h_r1_read, h_r2_read⟩ :=
    ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_alu
      state op_entry (regidx_to_fin r1) (regidx_to_fin r2) h_op_mult h_op_bus
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remu_input.r1_val state := by
    rw [h_a_match]; exact h_r1_read
  have h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remu_input.r2_val state := by
    rw [h_b_match]; exact h_r2_read
  exact equiv_REMU_metaplan state remu_input r1 r2 rd exec_row e0 e1 e2 h_input_r1 h_input_r2 h_input_rd h_input_pc h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_rd_val

end ZiskFv.Equivalence.Remu
