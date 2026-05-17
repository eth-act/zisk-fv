import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Equivalence.Promises.Store
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Airs.Main.Main
import ZiskFv.SailSpec.sb
import ZiskFv.SailSpec.sh
import ZiskFv.SailSpec.sw
import ZiskFv.SailSpec.sd

/-!
# `StorePromises` companion helpers

For each STORE opcode (SB, SH, SW, SD), provides a single helper that
derives `h_mem_eq` — the additional canonical-side argument that
`equiv_<OP>` accepts alongside the structural `StorePromises` bundle.

These helpers were extracted from the per-opcode
`Compliance/FromTrust/<Op>.lean` wrappers, where they previously lived
inline as a call to `Equivalence.Bridge.Mem.<op>_discharge_full` with
some `h_opcode_assumptions`-projection prep. The wrappers are now pure
pass-throughs that take the bundle and `h_mem_eq` directly.

The `StorePromises` bundle itself is trivially constructible from
pass-through binders, so no bundle-constructor helper is provided.
-/

namespace ZiskFv.Equivalence.Promises

open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- Derive SB's `h_mem_eq` from the SB emission bundle. Repackages
    `Bridge.Mem.sb_discharge_full` with the `h_opcode_assumptions`
    projection step baked in. -/
lemma sb_h_mem_eq_of_emission
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e_st : Interaction.MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = OP_COPYB)
    (h_ind_width : main.ind_width r_main = 1)
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    (h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input state) :
    (((((((state.mem.insert e_st.ptr.toNat e_st.x0
        ).insert (e_st.ptr.toNat + 1) e_st.x1
        ).insert (e_st.ptr.toNat + 2) e_st.x2
        ).insert (e_st.ptr.toNat + 3) e_st.x3
        ).insert (e_st.ptr.toNat + 4) e_st.x4
        ).insert (e_st.ptr.toNat + 5) e_st.x5
        ).insert (e_st.ptr.toNat + 6) e_st.x6
        ).insert (e_st.ptr.toNat + 7) e_st.x7
      = state.mem.insert
          (PureSpec.execute_STOREB_pure sb_input).data0.1
          (PureSpec.execute_STOREB_pure sb_input).data0.2 :=
  ZiskFv.Equivalence.Bridge.Mem.sb_discharge_full
    main r_main e_st state sb_input
    h_active h_op_main h_ind_width h_e_st_mult h_e_st_as_val
    h_opcode_assumptions.2.1 h_opcode_assumptions.2.2.1

/-- Derive SH's `h_mem_eq` from the SH emission bundle. -/
lemma sh_h_mem_eq_of_emission
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e_st : Interaction.MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = OP_COPYB)
    (h_ind_width : main.ind_width r_main = 2)
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    (h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input state) :
    (((((((state.mem.insert e_st.ptr.toNat e_st.x0
        ).insert (e_st.ptr.toNat + 1) e_st.x1
        ).insert (e_st.ptr.toNat + 2) e_st.x2
        ).insert (e_st.ptr.toNat + 3) e_st.x3
        ).insert (e_st.ptr.toNat + 4) e_st.x4
        ).insert (e_st.ptr.toNat + 5) e_st.x5
        ).insert (e_st.ptr.toNat + 6) e_st.x6
        ).insert (e_st.ptr.toNat + 7) e_st.x7
      = (state.mem.insert
            (PureSpec.execute_STOREH_pure sh_input).data0.1
            (PureSpec.execute_STOREH_pure sh_input).data0.2
        ).insert
            (PureSpec.execute_STOREH_pure sh_input).data1.1
            (PureSpec.execute_STOREH_pure sh_input).data1.2 :=
  ZiskFv.Equivalence.Bridge.Mem.sh_discharge_full
    main r_main e_st state sh_input
    h_active h_op_main h_ind_width h_e_st_mult h_e_st_as_val
    h_opcode_assumptions.2.1 h_opcode_assumptions.2.2.1

/-- Derive SW's `h_mem_eq` from the SW emission bundle. -/
lemma sw_h_mem_eq_of_emission
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e_st : Interaction.MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = OP_COPYB)
    (h_ind_width : main.ind_width r_main = 4)
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    (h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input state) :
    (((((((state.mem.insert e_st.ptr.toNat e_st.x0
        ).insert (e_st.ptr.toNat + 1) e_st.x1
        ).insert (e_st.ptr.toNat + 2) e_st.x2
        ).insert (e_st.ptr.toNat + 3) e_st.x3
        ).insert (e_st.ptr.toNat + 4) e_st.x4
        ).insert (e_st.ptr.toNat + 5) e_st.x5
        ).insert (e_st.ptr.toNat + 6) e_st.x6
        ).insert (e_st.ptr.toNat + 7) e_st.x7
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
            (PureSpec.execute_STOREW_pure sw_input).data3.2 :=
  ZiskFv.Equivalence.Bridge.Mem.sw_discharge_full
    main r_main e_st state sw_input
    h_active h_op_main h_ind_width h_e_st_mult h_e_st_as_val
    h_opcode_assumptions.2.1 h_opcode_assumptions.2.2.1

/-- Derive SD's `h_mem_eq` from the SD emission bundle. Unlike the
    narrow stores, SD's `discharge_full` consumes `read_xreg`-form
    reads; this helper does the `rX_bits → read_xreg` conversion
    via `rX_read_xreg_equiv`. -/
lemma sd_h_mem_eq_of_emission
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (e_st : Interaction.MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = OP_COPYB)
    (h_e_st_mult : e_st.multiplicity = 1) (h_e_st_as_val : e_st.as.val = 2)
    (h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input state) :
    e_st.ptr.toNat = (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat
    ∧ (e_st.x0 : BitVec 8) = BitVec.extractLsb 7 0 sd_input.r2_val
    ∧ (e_st.x1 : BitVec 8) = BitVec.extractLsb 15 8 sd_input.r2_val
    ∧ (e_st.x2 : BitVec 8) = BitVec.extractLsb 23 16 sd_input.r2_val
    ∧ (e_st.x3 : BitVec 8) = BitVec.extractLsb 31 24 sd_input.r2_val
    ∧ (e_st.x4 : BitVec 8) = BitVec.extractLsb 39 32 sd_input.r2_val
    ∧ (e_st.x5 : BitVec 8) = BitVec.extractLsb 47 40 sd_input.r2_val
    ∧ (e_st.x6 : BitVec 8) = BitVec.extractLsb 55 48 sd_input.r2_val
    ∧ (e_st.x7 : BitVec 8) = BitVec.extractLsb 63 56 sd_input.r2_val := by
  have h_read_r1 := h_opcode_assumptions.2.1
  have h_read_r2 := h_opcode_assumptions.2.2.1
  have h_read_r1' :
      read_xreg (regidx_to_fin (regidx.Regidx sd_input.r1)) state
        = EStateM.Result.ok sd_input.r1_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sd_input.r1)
          (regidx_to_fin (regidx.Regidx sd_input.r1))
          (by simp [regidx_to_fin])]
    exact h_read_r1
  have h_read_r2' :
      read_xreg (regidx_to_fin (regidx.Regidx sd_input.r2)) state
        = EStateM.Result.ok sd_input.r2_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sd_input.r2)
          (regidx_to_fin (regidx.Regidx sd_input.r2))
          (by simp [regidx_to_fin])]
    exact h_read_r2
  exact ZiskFv.Equivalence.Bridge.Mem.sd_discharge_full
    main r_main e_st state
    (regidx_to_fin (regidx.Regidx sd_input.r1))
    (regidx_to_fin (regidx.Regidx sd_input.r2))
    sd_input.r1_val sd_input.r2_val sd_input.imm
    h_active h_op_main h_e_st_mult h_e_st_as_val
    h_read_r1' h_read_r2'

end ZiskFv.Equivalence.Promises
