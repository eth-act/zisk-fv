import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.LoadUpperImmediate
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.lui
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 LUI (Phase 3C Track T-U1). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_LUI`),
* the compositional LUI spec
  (`ZiskFv.Spec.LoadUpperImmediate.lui_pc_advance` +
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
open ZiskFv.Spec.LoadUpperImmediate

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
    (h_rd_match :
      (if h : Transpiler.wrap_to_regidx e_rd.ptr = 0 then
        (pure () : SailM Unit)
      else
        let val := U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                                e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
        let reg_idx : Finset.Icc 1 31 :=
          ⟨ (Transpiler.wrap_to_regidx e_rd.ptr).val, by simp; omega ⟩
        write_xreg reg_idx val)
      =
      (match (PureSpec.execute_LUI_pure lui_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  rw [equiv_LUI_sail state lui_input imm rd
        h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_jump_rrw
        state exec_row e_rd nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as]
  -- Unfold the `let lui_output := ...` binder so hypotheses about
  -- `.nextPC`/`.rd` can fire.
  simp only [h_nextPC_eq]
  rw [h_rd_match]
  -- Normalize the `do`-notation residue on both sides.
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.execute_LUI_pure lui_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.Lui
