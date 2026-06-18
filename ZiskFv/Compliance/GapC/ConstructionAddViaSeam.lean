import ZiskFv.Compliance.GapC.NextPcOfSeam

/-!
# GO/NO-GO gate — `construction_add_sound_via_seam`

This is the **gate demonstration** for Route C: a NEW soundness theorem with the
SAME conclusion as `construction_add_sound`, but with the `h_nextPC_matches`
binder REMOVED and replaced by the strictly-smaller seam fact `h_seam` plus the
faithful sequential row facts / pc-column bridge. `h_nextPC_matches` is DERIVED
internally via `nextPC_matches_of_seam`, then forwarded into
`construction_add_sound`.

The registered `construction_add_sound` is **unchanged** — this theorem proves
Route C *discharges* the `h_nextPC_matches` residual (it is removable, not just
relocatable).

## Binder delta vs. `construction_add_sound`

* REMOVED: `h_nextPC_matches` — the `BitVec`-coerced eq vs `add_input.PC + 4#64`.
* ADDED (all on the real trace row, faithful, strictly smaller in shape):
  - `h_seam` : `execRow[1].pc = (pcLastMessage row).pc`  — X100.1a SEAM (FGL eq).
  - `h_set_pc`, `h_flag`, `h_jmp2` : sequential mux selectors.
  - `h_pc_col` : pc-column ↔ Sail-PC bridge (lane-bridge analogue).
  - `h_no_overflow` : no field wraparound on `+4`.

`execRow` remains a genuine top-level ∀-binder (anti-vacuity preserved): the bus
is the real trace bus, and `h_seam` ties its producer PC to the real mux output.

## Trust note

No PROJECT (`ZiskFv.*`) axioms. Closure is Sail + Lean kernel.
-/

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises

namespace ZiskFv.Compliance

set_option maxHeartbeats 2000000

/-- The honest unified Main+ROM row at `i` (alias of `mainRowWithRomSub`),
    exposed for the seam binder's `pcLastMessage` argument. -/
@[reducible]
def seamRow (trace : AcceptedTrace) (binding : ProgramBinding trace)
    (i : Fin trace.length) : ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  mainRowWithRomSub trace binding i

/-- **GATE — sound ADD construction via the #100 seam (Route C).**

    Identical conclusion to `construction_add_sound`, with `h_nextPC_matches`
    REPLACED by `h_seam` + the sequential row facts + the pc-column bridge.
    `h_nextPC_matches` is derived in-body by `GapC.nextPC_matches_of_seam`. -/
theorem construction_add_sound_via_seam
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_ADD)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok add_input.r1_val (binding.stateAt i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding.stateAt i)
        = EStateM.Result.ok add_input.r2_val (binding.stateAt i))
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some add_input.PC)
    (h_input_rd : add_input.rd = regidx_to_fin rd)
    -- (b) lane bridges
    (h_a_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    (h_b_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r2)))
    (h_b_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r2)))
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    -- ROUTE C: the #100 SEAM (replaces `h_nextPC_matches`) + sequential row
    -- facts + the faithful pc-column ↔ Sail-PC bridge.
    (h_seam :
      (busSub trace binding i execRow).exec_row[1]!.pc
        = (GapC.pcLastMessage (seamRow trace binding i)).pc)
    (h_set_pc : (seamRow trace binding i).core.set_pc = 0)
    (h_flag : (seamRow trace binding i).core.flag = 0)
    (h_jmp2 : (seamRow trace binding i).core.jmp_offset2 = 4)
    (h_pc_col :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((seamRow trace binding i).core.pc).val) : BitVec 64)
        = add_input.PC)
    (h_no_overflow : ((seamRow trace binding i).core.pc).val + 4 < GL_prime)
    (h_rd_idx :
      add_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.ADD))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  -- Derive the `h_nextPC_matches` promise from the seam via Route C.
  have h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_add_pure add_input).nextPC := by
    show (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = add_input.PC + 4#64
    exact GapC.nextPC_matches_of_seam (seamRow trace binding i)
      (busSub trace binding i execRow).exec_row[1]!.pc add_input.PC
      h_seam h_set_pc h_flag h_jmp2 h_pc_col h_no_overflow
  -- Forward into the registered construction (unchanged).
  exact construction_add_sound trace binding i add_input r1 r2 rd
    h_main_op h_main_active h_m32 h_store_pc
    h_input_r1 h_input_r2 h_input_pc h_input_rd
    h_a_lo_t h_a_hi_t h_b_lo_t h_b_hi_t
    execRow h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_idx

end ZiskFv.Compliance

#print axioms ZiskFv.Compliance.construction_add_sound_via_seam
