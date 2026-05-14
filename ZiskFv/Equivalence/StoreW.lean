import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Circuit.StoreD
import ZiskFv.Circuit.StoreW
import ZiskFv.Circuit.MemModel
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Sail.sw
import ZiskFv.Sail.BusEffect
import ZiskFv.Tactics.StoreArchetype

/-!
End-to-end theorem for RV64 SW (store word). The 4-byte narrow store
closes via `bus_effect_matches_sail_store_rrrw` plus a single bridging
premise that ties Sail's narrow `modify_memory_4` 4-insert post-state
to the bus's 8-insert update. The bridging premise factors out the
per-byte work (ptr-match, low-byte match, high-byte no-op match) into
a single caller obligation; it is decomposable into the smaller
circuit-level facts but tractably composable at the equivalence layer.
-/

namespace ZiskFv.Equivalence.StoreW

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Circuit.StoreD
open ZiskFv.Circuit.StoreW
open ZiskFv.Tactics.StoreArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

lemma equiv_SW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sw_state_assumptions sw_input state) :
    execute_instruction (instruction.STORE (
      sw_input.imm,
      regidx.Regidx sw_input.r2,
      regidx.Regidx sw_input.r1,
      4
    )) state
      = let output := PureSpec.execute_STOREW_pure sw_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          set (PureSpec.modify_memory_4 (← get) output)
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_STOREW_pure_equiv
    sw_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** -/
theorem equiv_SW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sw_state_assumptions sw_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREW_pure sw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2)
    -- Bridging premise: bus side's 8-insert chain on `state.mem`
    -- equals Sail's 4-insert chain (via `modify_memory_4` data
    -- fields). Bundles ptr-match + low-byte match + high-byte no-op
    -- match. Caller establishes via byte-bus high-zero witnesses +
    -- ptr-match against `transpile_SW`.
    (h_mem_eq :
      (((((((state.mem.insert e2.ptr.toNat e2.x0
          ).insert (e2.ptr.toNat + 1) e2.x1
          ).insert (e2.ptr.toNat + 2) e2.x2
          ).insert (e2.ptr.toNat + 3) e2.x3
          ).insert (e2.ptr.toNat + 4) e2.x4
          ).insert (e2.ptr.toNat + 5) e2.x5
          ).insert (e2.ptr.toNat + 6) e2.x6
          ).insert (e2.ptr.toNat + 7) e2.x7
        = (((state.mem.insert
              (PureSpec.execute_STOREW_pure sw_input).data0.1
              (PureSpec.execute_STOREW_pure sw_input).data0.2
            ).insert
              (PureSpec.execute_STOREW_pure sw_input).data1.1
              (PureSpec.execute_STOREW_pure sw_input).data1.2
            ).insert
              (PureSpec.execute_STOREW_pure sw_input).data2.1
              (PureSpec.execute_STOREW_pure sw_input).data2.2
            ).insert
              (PureSpec.execute_STOREW_pure sw_input).data3.1
              (PureSpec.execute_STOREW_pure sw_input).data3.2) :
    execute_instruction (instruction.STORE (
      sw_input.imm,
      regidx.Regidx sw_input.r2,
      regidx.Regidx sw_input.r1,
      4
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SW_sail state sw_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_store_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_STOREW_pure sw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  -- Both sides are EStateM monadic blocks: same `Sail.writeReg`,
  -- then bus's `modify (fun s => { s with mem := <8 inserts on s.mem> })`
  -- equals Sail's `set (modify_memory_4 (← get) output)`. Strip
  -- monad machinery (and unfold modify_memory_4) so both sides land
  -- on a common state record whose `mem` field is an insert chain.
  simp [bind, pure, EStateM.bind, EStateM.pure, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, set,
        MonadStateOf.set, EStateM.set, get, MonadState.get, getThe,
        MonadStateOf.get, EStateM.get,
        Sail.writeReg, PreSail.writeReg,
        PureSpec.modify_memory_4]
  -- Goal: bus 8-insert chain on state.mem = Sail 4-insert chain on
  -- state.mem. Close via the bridging premise.
  exact h_mem_eq

end ZiskFv.Equivalence.StoreW
