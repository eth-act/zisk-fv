import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Mul
import ZiskFv.Circuit.Divu
import ZiskFv.Airs.Main
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.divu
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned

/-!
End-to-end theorem for RV64 **DIVU**. Differs from
`Equivalence.Div` only in the opcode literal (184 vs 186), the pure
spec (`execute_DIVREM_divu_pure` / `_equiv`), and the Sail instruction
payload (`instruction.DIV (r2, r1, rd, true)` — the boolean selector
picks unsigned).

Three canonical theorems:
* `equiv_DIVU_circuit` — circuit-level, wraps `Circuit.Divu.divu_compositional`.
* `equiv_DIVU_sail` — Sail-level, wraps
  `PureSpec.execute_DIVREM_divu_pure_equiv`.
* `equiv_DIVU` — canonical shape, discharged via shape-
  (a) `bus_effect_matches_sail_alu_rrw` (RRW).
-/

namespace ZiskFv.Equivalence.Divu

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Mul
open ZiskFv.Circuit.Divu
open ZiskFv.Tactics.ArithSMArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 DIVU reduces to the pure-function block supplied by
    `PureSpec.execute_DIVREM_divu_pure`. Wraps
    `PureSpec.execute_DIVREM_divu_pure_equiv`. -/
theorem equiv_DIVU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divu_input : PureSpec.DivuInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divu_input.r2_val state)
    (h_input_rd : divu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divu_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, true))) state
      = let divu_output := PureSpec.execute_DIVREM_divu_pure divu_input
        (do
          Sail.writeReg Register.nextPC divu_output.nextPC
          match divu_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_DIVREM_divu_pure_equiv
    divu_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    DIVU equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `RdValDerivation.MulDivRemUnsigned.h_rd_val_mdru_divu` discharge
    lemma. -/
theorem equiv_DIVU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divu_input : PureSpec.DivuInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divu_input.r2_val state)
    (h_input_rd : divu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : divu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Discharge parameters (DIV layout: a=quotient, b=divisor,
    -- c=dividend, d=remainder).
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
        = a₀.val + a₁.val * 65536)
    (h_byte_hi :
      e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
        = a₂.val + a₃.val * 65536)
    (h_op1 : divu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 c₀.val c₁.val c₂.val c₃.val)
    (h_op2 : divu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 b₀.val b₁.val b₂.val b₃.val)
    (h_op2_ne : divu_input.r2_val.toNat ≠ 0)
    (h_d_lt_b : ZiskFv.PackedBitVec.MulNoWrap.packed4 d₀.val d₁.val d₂.val d₃.val
                  < divu_input.r2_val.toNat) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned.h_rd_val_mdru_divu
      divu_input.r1_val divu_input.r2_val e2
      a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ d₀ d₁ d₂ d₃
      cy₀ cy₁ cy₂ cy₃ cy₄ cy₅ cy₆
      h0 h1 h2 h3 h4 h5 h6 h7
      h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
      h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
      h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
      h_byte_lo h_byte_hi h_op1 h_op2 h_op2_ne h_d_lt_b
  rw [equiv_DIVU_sail state divu_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_divu_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Divu
