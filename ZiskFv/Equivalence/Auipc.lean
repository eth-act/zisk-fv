import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.AddUpperImmediatePC
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.auipc
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Equivalence.RdValDerivation.JumpUType

/-!
End-to-end theorem for RV64 AUIPC (Phase 3C Track T-U2). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_AUIPC`),
* the compositional AUIPC spec
  (`ZiskFv.Circuit.AddUpperImmediatePC.auipc_pc_advance` +
  `auipc_store_value_lo`/`_hi`),
* the Sail pure-function equivalence
  (`PureSpec.execute_AUIPC_pure_equiv`, closed Phase 3B via
  `get_arch_pc` / `readReg_succ (writeReg_read_diff ...)` bridging),

into a metaplan-shaped theorem:

* `equiv_AUIPC_metaplan` — the metaplan target shape:
  `execute_instruction (.UTYPE (imm, rd, uop.AUIPC)) state
    = (bus_effect exec_row mem_row state).2`.

The bus shape is **shape (c)** — two execution-bus entries (pc-read +
nextPC-write) and a single memory-bus rd-write entry.

**PC-read wrinkle.** AUIPC's Sail spec reads the architectural PC via
`get_arch_pc()`, which after the `nextPC` write still returns the
original PC (`readReg_succ (writeReg_read_diff ...)` — PC and nextPC
are distinct registers in the Sail state). The Phase 3B pure-spec
equivalence theorem handles this bridge; at the Equivalence level we
merely consume that theorem. The circuit side carries the PC via the
`store_pc` mechanic (`store_value[0] = pc + jmp_offset2 = pc + imm`),
which is captured by `auipc_store_value_lo`.
-/

namespace ZiskFv.Equivalence.Auipc

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.AddUpperImmediatePC

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level AUIPC theorem.** Given the AUIPC archetype circuit
    hypotheses (`auipc_archetype_circuit_holds`), the next-pc cell
    advances by `jmp_offset1 = 4`, and the rd lane equals
    `pc + jmp_offset2 = pc + imm`.

    This is the circuit-level companion to `equiv_AUIPC_sail` below. -/
theorem equiv_AUIPC
    (_rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit :
      ZiskFv.Tactics.UTypeArchetype.auipc_archetype_circuit_holds
        m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main :=
  auipc_pc_advance m r_main next_pc h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 AUIPC reduces to the pure-function block supplied by
    `PureSpec.execute_AUIPC_pure`, given PC readability and the
    rd / imm input alignment.

    Wraps `PureSpec.execute_AUIPC_pure_equiv` to expose the Sail chain
    at this module's export surface. The Phase 3B pure-spec theorem
    already bridges the `get_arch_pc` read-after-write-nextPC via
    `readReg_succ (writeReg_read_diff ...)`. -/
theorem equiv_AUIPC_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (h_input_imm : auipc_input.imm = imm)
    (h_input_rd : auipc_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some auipc_input.PC) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = let auipc_output := PureSpec.execute_AUIPC_pure auipc_input
        (do
          Sail.writeReg Register.nextPC auipc_output.nextPC
          match auipc_output.rd with
            | .some (reg, rd_val) => write_xreg reg rd_val
            | .none => pure ()
          (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_AUIPC_pure_equiv auipc_input imm rd
    h_input_imm h_input_rd h_input_pc

/-- **Metaplan theorem.** The shape the original metaplan targets for
    RV64 AUIPC: Sail's `execute_instruction` on an RV64 AUIPC equals
    the state computed by applying `bus_effect` to the circuit's
    execution and memory bus rows.

    Composes `equiv_AUIPC_sail` with the shape-(c) bus-matching lemma
    `bus_effect_matches_sail_jump_rrw` (Phase 2.5 D3). Like LUI, AUIPC
    has no throw/success branching — the pure spec unconditionally
    writes rd (or skips for rd = x0) and advances PC.

    **Hypotheses.**
    * Sail side (from `equiv_AUIPC_sail`): PC readability
      (`h_input_pc`), input alignment (`h_input_imm`, `h_input_rd`).
    * Bus side (structural, Phase-4-derivable): exec_row has two
      entries (pc-read + nextPC-write) with the appropriate
      multiplicities; `e_rd` is the single register-write entry for rd.
    * `h_nextPC_eq` pins the Sail pure-spec's `nextPC` output to
      `nextPC_val`.
    * `h_rd_match`: bridges the shape-(c) `if h :` output to the Sail
      pure-spec `match rd`. -/
theorem equiv_AUIPC_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_imm : auipc_input.imm = imm)
    (h_input_rd : auipc_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some auipc_input.PC)
    -- Phase 2.5 D3: shape-(c) structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_AUIPC_pure auipc_input).nextPC = nextPC_val)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_idx : auipc_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ 0#12)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  rw [equiv_AUIPC_sail state auipc_input imm rd
        h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_jump_rrw
        state exec_row e_rd nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as]
  -- Align the nextPC on both sides before unfolding, so h_nextPC_eq
  -- can still fire against the projected `.nextPC`.
  simp only [h_nextPC_eq]
  simp only [PureSpec.execute_AUIPC_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-- **Tier-1 metaplan: AUIPC without `h_rd_val` parameter** (finishing5 S5+S6).

    Companion to `equiv_AUIPC_metaplan` that drops the `h_rd_val :`
    OUTPUT-EQ residual parameter. Internally derives the rd-write
    equality `U64.toBV ... = auipc_input.PC + signExtend 64 (imm ++ 0#12)`
    via `RdValDerivation.JumpUType.h_rd_val_jut_auipc`, which composes:

    * `transpile_PC_for_AUIPC` (S1) — Sail-PC ↔ Main-pc-column bridge,
    * `auipc_store_value_lo_bv` / `_hi_bv` (S3) — bus-emission BitVec
      bridges,
    * `store_pc_lanes_match_{lo,hi}_of_bus_emission` (S4),
    * `WidePCNoWrap.fgl_pc_plus_offset_val_eq_lo_strict` (S2) —
      wide-PC no-wrap arithmetic for the imm-dependent offset.

    Unlike JAL/JALR, AUIPC's offset is `signExtend 64 (imm ++ 0#12)`
    rather than the constant 4. The transpile axiom `transpile_AUIPC`
    pins `m.jmp_offset2 r = imm_offset` at the FGL level; the
    BitVec-side lift requires a TRANSPILE-BRIDGE parameter
    `h_offset_bridge`. The `h_no_wrap` parameter generalizes
    `h_pc_bound` to admit the imm-sized offset. All parameters live
    in {CIRCUIT-CONSTRAINT, LANE-MATCH, RANGE, TRANSPILE-BRIDGE}. NO
    OUTPUT-EQ parameters survive. -/
theorem equiv_AUIPC_metaplan_tier1
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_input_imm : auipc_input.imm = imm)
    (h_input_rd : auipc_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some auipc_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_AUIPC_pure auipc_input).nextPC = nextPC_val)
    (h_rd_idx : auipc_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    -- Tier-1 discharge parameters (replace h_rd_val).
    (h_circuit :
      ZiskFv.Tactics.UTypeArchetype.auipc_archetype_circuit_holds m r_main next_pc)
    (h_offset_bridge : (m.jmp_offset2 r_main).val
      = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat)
    (h_lane_lo : ZiskFv.Airs.MemoryBus.store_pc_lanes_match_lo m r_main e_rd)
    (h_lane_hi : ZiskFv.Airs.MemoryBus.store_pc_lanes_match_hi m r_main e_rd)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296)
    (h_e_rd_0 : e_rd.x0.val < 256) (h_e_rd_1 : e_rd.x1.val < 256)
    (h_e_rd_2 : e_rd.x2.val < 256) (h_e_rd_3 : e_rd.x3.val < 256)
    (h_e_rd_4 : e_rd.x4.val < 256) (h_e_rd_5 : e_rd.x5.val < 256)
    (h_e_rd_6 : e_rd.x6.val < 256) (h_e_rd_7 : e_rd.x7.val < 256) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.JumpUType.h_rd_val_jut_auipc
      auipc_input.PC auipc_input.imm m r_main next_pc e_rd
      h_circuit h_offset_bridge h_lane_lo h_lane_hi
      h_no_wrap h_lo_bound h_pc_offset_lt_2_32
      h_e_rd_0 h_e_rd_1 h_e_rd_2 h_e_rd_3
      h_e_rd_4 h_e_rd_5 h_e_rd_6 h_e_rd_7
  exact equiv_AUIPC_metaplan state auipc_input imm rd exec_row e_rd
    nextPC_val h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_nextPC_eq h_rd_idx h_rd_val

/-- **Phase 5 V12 companion for AUIPC.** Drops `h_input_pc` and
    `h_input_rd` via `chip_bus_hyps_jump_rrw` + `readReg_of_readReg_succ`. -/
theorem equiv_AUIPC_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_imm : auipc_input.imm = imm)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_AUIPC_pure auipc_input).nextPC = nextPC_val)
    -- Phase 5 V12: bus precondition + ptr/value match.
    (h_bus : (bus_effect exec_row [e_rd] state).1)
    (h_pc : auipc_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_idx : auipc_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ 0#12)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_jump_rrw
    state exec_row e_rd
    h_exec_len h_e0_mult h_e1_mult h_rd_mult h_rd_as h_bus
  have h_input_rd : auipc_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some auipc_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_AUIPC_metaplan state auipc_input imm rd exec_row e_rd
    nextPC_val h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_nextPC_eq h_rd_idx h_rd_val

/-- Constructor: build a `PureSpec.AuipcInput` from bus + imm. -/
def AuipcInput_of_bus
    (e_rd : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (imm : BitVec 20) : PureSpec.AuipcInput :=
  { imm := imm
    rd := Transpiler.wrap_to_regidx e_rd.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for AUIPC.** Bus-derived input form. -/
theorem equiv_AUIPC_metaplan_bus_self
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
      (PureSpec.execute_AUIPC_pure (AuipcInput_of_bus e_rd exec_row imm)).nextPC = nextPC_val)
    (h_bus : (bus_effect exec_row [e_rd] state).1)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = (AuipcInput_of_bus e_rd exec_row imm).PC
        + BitVec.signExtend 64 ((AuipcInput_of_bus e_rd exec_row imm).imm ++ 0#12)) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  exact equiv_AUIPC_metaplan_from_bus state
    (AuipcInput_of_bus e_rd exec_row imm) imm rd
    exec_row e_rd nextPC_val
    rfl
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_nextPC_eq
    h_bus rfl h_rd_ptr rfl h_rd_val

end ZiskFv.Equivalence.Auipc
