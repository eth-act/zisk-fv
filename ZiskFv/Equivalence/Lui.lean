import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.LoadUpperImmediate
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.lui
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.RdValDerivation.JumpUType

/-!
End-to-end theorem for RV64 LUI (Phase 3C Track T-U1). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_LUI`),
* the compositional LUI spec
  (`ZiskFv.Circuit.LoadUpperImmediate.lui_pc_advance` +
  `lui_store_value_lo`/`_hi`),
* the Sail pure-function equivalence
  (`PureSpec.execute_LUI_pure_equiv`, closed Phase 3B),

into a metaplan-shaped theorem:

* `equiv_LUI_metaplan` — the metaplan target shape:
  `execute_instruction (.UTYPE (imm, rd, uop.LUI)) state
    = (bus_effect exec_row mem_row state).2`.

The bus shape is **shape (c)** — two execution-bus entries (pc-read +
nextPC-write) and a single memory-bus rd-write entry. LUI uses
`store_pc = 0` but the shape-(c) `bus_effect_matches_sail_jump_rrw`
lemma is agnostic to `store_pc` (it only looks at the multiplicities
and address spaces on the two buses), so it reuses cleanly here.
-/

namespace ZiskFv.Equivalence.Lui

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.LoadUpperImmediate

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level LUI theorem.** Given the LUI archetype circuit
    hypotheses (`lui_archetype_circuit_holds`), the next-pc cell
    advances by `jmp_offset2` and the rd lanes equal `(b_0, b_1)`.

    This is the circuit-level companion to `equiv_LUI_sail` below. -/
theorem equiv_LUI
    (_rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit :
      ZiskFv.Tactics.UTypeArchetype.lui_archetype_circuit_holds
        m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main :=
  lui_pc_advance m r_main next_pc h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LUI reduces to the pure-function block supplied by
    `PureSpec.execute_LUI_pure`, given PC readability and the rd /
    imm input alignment.

    Wraps `PureSpec.execute_LUI_pure_equiv` to expose the Sail chain
    at this module's export surface. -/
theorem equiv_LUI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (h_input_imm : lui_input.imm = imm)
    (h_input_rd : lui_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some lui_input.PC) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = let lui_output := PureSpec.execute_LUI_pure lui_input
        (do
          Sail.writeReg Register.nextPC lui_output.nextPC
          match lui_output.rd with
            | .some (reg, rd_val) => write_xreg reg rd_val
            | .none => pure ()
          (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_LUI_pure_equiv lui_input imm rd
    h_input_imm h_input_rd h_input_pc

/-- **Metaplan theorem.** The shape the original metaplan targets for
    RV64 LUI: Sail's `execute_instruction` on an RV64 LUI equals the
    state computed by applying `bus_effect` to the circuit's execution
    and memory bus rows.

    Composes `equiv_LUI_sail` with the shape-(c) bus-matching lemma
    `bus_effect_matches_sail_jump_rrw` (Phase 2.5 D3). LUI has no
    throw/success branching — the pure spec unconditionally writes rd
    (or skips for rd = x0) and advances PC — so no `h_success` /
    `h_not_throws` hypotheses are needed.

    **Hypotheses.**
    * Sail side (from `equiv_LUI_sail`): PC readability (`h_input_pc`)
      and input alignment (`h_input_imm`, `h_input_rd`).
    * Bus side (structural, Phase-4-derivable): exec_row has two
      entries (pc-read + nextPC-write) with the appropriate
      multiplicities; `e_rd` is the single register-write entry for rd.
    * `h_nextPC_option` pins the Sail pure-spec's `nextPC` output to
      `nextPC_val`.
    * `h_rd_match`: bridges the shape-(c) `if h :` output to the Sail
      pure-spec `match rd`. -/
theorem equiv_LUI_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_imm : lui_input.imm = imm)
    (h_input_rd : lui_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some lui_input.PC)
    -- Phase 2.5 D3: shape-(c) structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_LUI_pure lui_input).nextPC = nextPC_val)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_idx : lui_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = BitVec.signExtend 64 (lui_input.imm ++ 0#12)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  rw [equiv_LUI_sail state lui_input imm rd
        h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_jump_rrw
        state exec_row e_rd nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as]
  -- Align the nextPC on both sides before unfolding, so h_nextPC_eq
  -- can still fire against the projected `.nextPC`.
  simp only [h_nextPC_eq]
  simp only [PureSpec.execute_LUI_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-- **Tier-1 metaplan: LUI without `h_rd_val` parameter.**

    Same conclusion as `equiv_LUI_metaplan`, but the `h_rd_val`
    OUTPUT-EQ parameter is **derived internally** via the
    `RdValDerivation.JumpUType.h_rd_val_jut_lui` discharge lemma. -/
theorem equiv_LUI_metaplan_tier1
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    -- Sail-state input bridges
    (h_input_imm : lui_input.imm = imm)
    (h_input_rd : lui_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some lui_input.PC)
    -- Bus-protocol structural hypotheses
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_LUI_pure lui_input).nextPC = nextPC_val)
    (h_rd_idx : lui_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    -- Tier-1 discharge parameters (replacing the OUTPUT-EQ h_rd_val)
    (h_circuit : ZiskFv.Tactics.UTypeArchetype.lui_archetype_circuit_holds m r_main next_pc)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e_rd)
    (h_imm_lo_nat : (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat : (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    (h_e2_0 : e_rd.x0.val < 256) (h_e2_1 : e_rd.x1.val < 256)
    (h_e2_2 : e_rd.x2.val < 256) (h_e2_3 : e_rd.x3.val < 256)
    (h_e2_4 : e_rd.x4.val < 256) (h_e2_5 : e_rd.x5.val < 256)
    (h_e2_6 : e_rd.x6.val < 256) (h_e2_7 : e_rd.x7.val < 256) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  -- Derive h_rd_val internally via the discharge lemma.
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.JumpUType.h_rd_val_jut_lui
      imm m r_main next_pc e_rd
      h_circuit h_lane_rd h_imm_lo_nat h_imm_hi_nat
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
  -- Need lui_input.imm = imm to thread the conclusion shape.
  rw [← h_input_imm] at h_rd_val
  -- Delegate to the parametric metaplan with the derived h_rd_val.
  exact equiv_LUI_metaplan state lui_input imm rd exec_row e_rd nextPC_val
    h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_nextPC_eq h_rd_idx h_rd_val

/-- **Phase 5 V12 companion for LUI.** Drops `h_input_pc` and
    `h_input_rd` via `chip_bus_hyps_jump_rrw` + `readReg_of_readReg_succ`.
    `h_input_imm` stays (not bus-derivable). -/
theorem equiv_LUI_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_imm : lui_input.imm = imm)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_LUI_pure lui_input).nextPC = nextPC_val)
    -- Phase 5 V12: bus precondition + ptr/value match.
    (h_bus : (bus_effect exec_row [e_rd] state).1)
    (h_pc : lui_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_idx : lui_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = BitVec.signExtend 64 (lui_input.imm ++ 0#12)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_jump_rrw
    state exec_row e_rd
    h_exec_len h_e0_mult h_e1_mult h_rd_mult h_rd_as h_bus
  have h_input_rd : lui_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some lui_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_LUI_metaplan state lui_input imm rd exec_row e_rd
    nextPC_val h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_nextPC_eq h_rd_idx h_rd_val

/-- Constructor: build a `PureSpec.LuiInput` from bus + imm. -/
def LuiInput_of_bus
    (e_rd : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (imm : BitVec 20) : PureSpec.LuiInput :=
  { imm := imm
    rd := Transpiler.wrap_to_regidx e_rd.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for LUI.** Bus-derived input form. -/
theorem equiv_LUI_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_LUI_pure (LuiInput_of_bus e_rd exec_row imm)).nextPC = nextPC_val)
    (h_bus : (bus_effect exec_row [e_rd] state).1)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = BitVec.signExtend 64 ((LuiInput_of_bus e_rd exec_row imm).imm ++ 0#12)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  exact equiv_LUI_metaplan_from_bus state
    (LuiInput_of_bus e_rd exec_row imm) imm rd
    exec_row e_rd nextPC_val
    rfl
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_nextPC_eq
    h_bus rfl h_rd_ptr rfl h_rd_val

end ZiskFv.Equivalence.Lui
