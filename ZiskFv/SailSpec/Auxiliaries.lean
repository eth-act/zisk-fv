import LeanRV64D
import Mathlib

namespace ExtDHashMap

  lemma insert_eq_self [BEq K] [LawfulBEq K] [Hashable K]
    (m : Std.ExtDHashMap K V)
    (h : m.get? k = .some v)
  :
    m.insert k v = m
  := by
    grind

  lemma insert_comm [BEq K] [LawfulBEq K] [Hashable K]
    (m : Std.ExtDHashMap K V)
    (h_neq : ¬ K₁ = K₂)
  :
    (m.insert K₁ V₁).insert K₂ V₂ = (m.insert K₂ V₂).insert K₁ V₁
  := by
    grind

end ExtDHashMap

/-
  No need to simplify the following:

  bind
  LeanRV64D.Functions.translationMode
  LeanRV64D.Functions.set_next_pc
-/

attribute [simp]
  instBEqSATPMode.beq

  get
  getThe
  instMonadStateOfMonadStateOf
  liftM
  modify
  modifyGet
  monadLift
  MonadLift.monadLift
  pure

  Functor.map

  ExceptT.bind
  ExceptT.bindCont
  ExceptT.instMonad
  ExceptT.lift
  ExceptT.map
  ExceptT.mk
  ExceptT.pure
  ExceptT.run

  EStateM.bind
  EStateM.get
  EStateM.map
  EStateM.modifyGet
  EStateM.instMonad
  EStateM.instMonadStateOf
  EStateM.pure

  ExceptT.instMonad ExceptT.pure ExceptT.mk

  Int.le
  Int.neg
  Int.negOfNat
  Int.sub
  Int.tmod_eq_emod

  untilFuelM
  untilFuelM.go

  Sail.BitVec.access
  Sail.BitVec.addInt
  Sail.BitVec.extractLsb
  Sail.BitVec.signExtend
  Sail.BitVec.toNatInt
  Sail.BitVec.updateSubrange
  Sail.BitVec.updateSubrange'
  Sail.BitVec.zeroExtend
  Sail.get_slice_int
  zero_extend

  LeanRV64D.Functions._get_Misa_C
  LeanRV64D.Functions._get_Mstatus_MPRV
  LeanRV64D.Functions.allowed_misaligned
  LeanRV64D.Functions.bits_of_physaddr
  LeanRV64D.Functions.bits_of_virtaddr
  LeanRV64D.Functions.check_misaligned
  LeanRV64D.Functions.checked_mem_read
  LeanRV64D.Functions.checked_mem_write
  LeanRV64D.Functions.currentlyEnabled
  LeanRV64D.Functions.Data
  LeanRV64D.Functions.effectivePrivilege
  LeanRV64D.Functions.encdec_reg_forwards
  LeanRV64D.Functions.encdec_reg_forwards_matches
  LeanRV64D.Functions.ext_control_check_pc
  LeanRV64D.Functions.ext_data_get_addr
  LeanRV64D.Functions.extend_value
  LeanRV64D.Functions.get_config_rvfi
  LeanRV64D.Functions.get_config_use_abi_names
  LeanRV64D.Functions.get_next_pc
  LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.is_aligned_vaddr
  LeanRV64D.Functions.is_aligned_paddr
  LeanRV64D.Functions.matching_pma
  LeanRV64D.Functions.matching_pma_bits_range
  LeanRV64D.Functions.mem_read
  LeanRV64D.Functions.mem_read_priv
  LeanRV64D.Functions.mem_read_priv_meta
  LeanRV64D.Functions.mem_write_ea
  LeanRV64D.Functions.mem_write_value
  LeanRV64D.Functions.mem_write_value_meta
  LeanRV64D.Functions.mem_write_value_priv_meta
  LeanRV64D.Functions.MemoryOpResult_drop_meta
  LeanRV64D.Functions.misaligned_order
  LeanRV64D.Functions.not
  LeanRV64D.Functions.phys_access_check
  LeanRV64D.Functions.plat_enable_misaligned_access
  -- pmaCheck: closed by the ZisK platform profile lemmas.
  -- pmpCheck: closed by the ZisK platform profile lemmas.
  LeanRV64D.Functions.range_subset
  LeanRV64D.Functions.read_kind_of_flags
  LeanRV64D.Functions.read_ram
  LeanRV64D.Functions.reg_arch_name_raw_forwards
  LeanRV64D.Functions.reg_name_forwards
  LeanRV64D.Functions.regval_from_reg
  LeanRV64D.Functions.regval_into_reg
  LeanRV64D.Functions.RETIRE_SUCCESS
  LeanRV64D.Functions.sail_branch_announce
  LeanRV64D.Functions.sign_extend
  LeanRV64D.Functions.sign_extend
  LeanRV64D.Functions.split_misaligned
  LeanRV64D.Functions.sys_misaligned_order_decreasing
  LeanRV64D.Functions.sys_pmp_count
  LeanRV64D.Functions.to_bits
  LeanRV64D.Functions.to_bits_checked
  LeanRV64D.Functions.translateAddr
  -- within_clint: closed by the ZisK platform profile lemmas.
  LeanRV64D.Functions.within_htif_readable
  LeanRV64D.Functions.within_htif_writable
  LeanRV64D.Functions.within_mmio_readable
  LeanRV64D.Functions.within_mmio_writable
  LeanRV64D.Functions.write_kind_of_flags
  LeanRV64D.Functions.write_ram
  LeanRV64D.Functions.xlen
  LeanRV64D.Functions.xlen_bytes
  LeanRV64D.Functions.xreg_full_write_callback
  LeanRV64D.Functions.xreg_write_callback
  LeanRV64D.Functions.zero_reg
  LeanRV64D.Functions.zeros
  LeanRV64D.Functions.zeros
  LeanRV64D.Functions.zopz0zI_s
  LeanRV64D.Functions.zopz0zI_u
  LeanRV64D.Functions.zopz0zIzJ_u
  LeanRV64D.Functions.zopz0zKzJ_s
  LeanRV64D.Functions.zopz0zKzJ_u

  PreSail.ConcurrencyInterfaceV1.sail_mem_read
  PreSail.ConcurrencyInterfaceV1.sail_mem_write
  PreSail.PreSailME.run
  PreSail.readByte
  PreSail.readBytes
  PreSail.writeByte
  PreSail.writeBytes

  Sail.ConcurrencyInterfaceV1.sail_mem_read
  Sail.ConcurrencyInterfaceV1.sail_mem_write
  Sail.SailME.run

section SimplerMonadicReasoning

  /-- Simpler monadic pure ok -/
  @[simp high]
  lemma pure_ok_equiv :
    @pure (PreSail.PreSailM RegisterType Sail.trivialChoiceSource exception) EStateM.instMonad.toPure T val =
    λ s => EStateM.Result.ok val s
  := by
    rfl

  /-- Simpler monadic pure exception -/
  @[simp high]
  lemma pure_except_equiv :
    @pure (SailME ExecutionResult) ExceptT.instMonad.toPure T val state =
    EStateM.Result.ok (Except.ok val) state
  := by
    rfl

  /-- Simpler monadic throw -/
  @[simp high]
  lemma throw_equiv :
    @throw
      (Sail.Error exception)
      (PreSail.PreSailM RegisterType Sail.trivialChoiceSource exception)
      (instMonadExceptOfMonadExceptOf
        (Sail.Error exception)
        (PreSail.PreSailM RegisterType Sail.trivialChoiceSource exception))
      T
      error =
    λ s_1 => EStateM.Result.error error s_1
  := by
    unfold throw instMonadExceptOfMonadExceptOf
    unfold throwThe MonadExceptOf.throw
    unfold EStateM.instMonadExceptOfOfBacktrackable EStateM.throw
    dsimp

  /-- Simpler bind equiv -/
  @[simp high]
  lemma bind_equiv :
    (@bind
      SailM
      EStateM.instMonad.toBind
      T1
      T2
      f1
      f2
    ) = λ s =>
      match f1 s with
      | EStateM.Result.ok a s => f2 a s
      | EStateM.Result.error e s => EStateM.Result.error e s
  := by
    unfold bind EStateM.instMonad EStateM.bind Monad.toBind
    simp
    funext state
    set state' := f1 state
    cases state' <;> simp

  @[simp high]
  lemma EStateM_bind_equiv :
    @EStateM.bind
      (Sail.Error exception)
      (PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
      (Except ExecutionResult Unit)
      (Except ExecutionResult ExecutionResult)
      f1
      f2
      state =
    (match f1 state with
    | EStateM.Result.ok a s => f2 a s
    | EStateM.Result.error e s => EStateM.Result.error e s)
  := by
    simp [EStateM.bind]
    set state' := f1 state
    cases state' <;> simp

end SimplerMonadicReasoning

section RegisterManipulation

  /-- Converting a register to a Fin 32 -/
  def regidx_to_fin (r : regidx): Fin 32 :=
    match r with
      | regidx.Regidx r => ⟨
          r.toNat,
          by {
            have : (if false = true then 4 else 5) ≤ 5 := by decide
            convert BitVec.toNat_lt_twoPow_of_le this
          }
        ⟩

  def reg_of_fin (r : Fin 32) : Register :=
    match r.1 with
      | 1 => Register.x1
      | 2 => Register.x2
      | 3 => Register.x3
      | 4 => Register.x4
      | 5 => Register.x5
      | 6 => Register.x6
      | 7 => Register.x7
      | 8 => Register.x8
      | 9 => Register.x9
      | 10 => Register.x10
      | 11 => Register.x11
      | 12 => Register.x12
      | 13 => Register.x13
      | 14 => Register.x14
      | 15 => Register.x15
      | 16 => Register.x16
      | 17 => Register.x17
      | 18 => Register.x18
      | 19 => Register.x19
      | 20 => Register.x20
      | 21 => Register.x21
      | 22 => Register.x22
      | 23 => Register.x23
      | 24 => Register.x24
      | 25 => Register.x25
      | 26 => Register.x26
      | 27 => Register.x27
      | 28 => Register.x28
      | 29 => Register.x29
      | 30 => Register.x30
      | _ => Register.x31

  @[simp]
  lemma register_type_reg_of_fin_equiv (r : Fin 32) :
    RegisterType (reg_of_fin r) = BitVec 64
  := by
    fin_cases r <;>
    simp [reg_of_fin, RegisterType]

  @[simp]
  lemma register_type_pc_equiv :
    RegisterType Register.PC = BitVec 64
  := by
    simp [RegisterType]

  /-- Register read in terms of Fin 32 -/
  def read_xreg (reg : Fin 32) : SailM (BitVec 64) :=
    match reg.1 with
      | 0 => pure (0#64)
      | _ => (register_type_reg_of_fin_equiv reg) ▸ (Sail.readReg (reg_of_fin reg))

  set_option maxHeartbeats 0 in
  /-- Equivalence of register reading when in Fin 32 -/
  lemma rX_read_xreg_equiv
    (state)
    (rd_idx : regidx)
    (rd : Fin 32)
    (h_rd : rd_idx = regidx.Regidx (BitVec.ofNat 5 rd))
  :
    LeanRV64D.Functions.rX_bits rd_idx state =
    read_xreg rd state
  := by
    unfold LeanRV64D.Functions.rX_bits
    simp [h_rd]
    unfold LeanRV64D.Functions.rX read_xreg
    fin_cases rd
    . simp
    all_goals
      simp [PreSail.readReg, reg_of_fin]
      aesop

  lemma regidx_non_zero (h_non_zero: ¬rd = 0):
    regidx_to_fin (regidx.Regidx rd) ∈ Finset.Icc 1 31
  := by
    obtain ⟨ rd', eq_rd' ⟩ : exists rd' : BitVec 5, rd' = rd := by simp
    subst rd
    by_cases rd' = 0; simp_all
    by_cases h: rd' = 1; rewrite [h]; decide
    by_cases h: rd' = 2; rewrite [h]; decide
    by_cases h: rd' = 3; rewrite [h]; decide
    by_cases h: rd' = 4; rewrite [h]; decide
    by_cases h: rd' = 5; rewrite [h]; decide
    by_cases h: rd' = 6; rewrite [h]; decide
    by_cases h: rd' = 7; rewrite [h]; decide
    by_cases h: rd' = 8; rewrite [h]; decide
    by_cases h: rd' = 9; rewrite [h]; decide
    by_cases h: rd' = 10; rewrite [h]; decide
    by_cases h: rd' = 11; rewrite [h]; decide
    by_cases h: rd' = 12; rewrite [h]; decide
    by_cases h: rd' = 13; rewrite [h]; decide
    by_cases h: rd' = 14; rewrite [h]; decide
    by_cases h: rd' = 15; rewrite [h]; decide
    by_cases h: rd' = 16; rewrite [h]; decide
    by_cases h: rd' = 17; rewrite [h]; decide
    by_cases h: rd' = 18; rewrite [h]; decide
    by_cases h: rd' = 19; rewrite [h]; decide
    by_cases h: rd' = 20; rewrite [h]; decide
    by_cases h: rd' = 21; rewrite [h]; decide
    by_cases h: rd' = 22; rewrite [h]; decide
    by_cases h: rd' = 23; rewrite [h]; decide
    by_cases h: rd' = 24; rewrite [h]; decide
    by_cases h: rd' = 25; rewrite [h]; decide
    by_cases h: rd' = 26; rewrite [h]; decide
    by_cases h: rd' = 27; rewrite [h]; decide
    by_cases h: rd' = 28; rewrite [h]; decide
    by_cases h: rd' = 29; rewrite [h]; decide
    by_cases h: rd' = 30; rewrite [h]; decide
    by_cases h: rd' = 31; rewrite [h]; decide
    exfalso
    have : rd' < 32 := by bv_decide
    grind

  /-- Successful read -/
  @[simp]
  lemma readReg_succ
    (h: state.regs.get? reg = .some reg_val)
  :
    Sail.readReg reg state = EStateM.Result.ok reg_val state
  := by
    unfold Sail.readReg PreSail.readReg
    aesop

  /-- Unsuccessful read -/
  @[simp]
  lemma readReg_fail
    (h: state.regs.get? reg = .none)
  :
    Sail.readReg reg state = EStateM.Result.error Sail.Error.Unreachable state
  := by
    unfold Sail.readReg PreSail.readReg
    aesop

  def write_xreg (reg : Finset.Icc 1 31) (val : BitVec 64) : SailM Unit :=
    let result := Sail.writeReg (reg_of_fin ⟨ reg.1, by grind ⟩ )
    (result (cast (by rw [register_type_reg_of_fin_equiv]) val))

  lemma wX_write_xreg_zero_equiv :
    LeanRV64D.Functions.wX_bits (regidx.Regidx 0) data state =
    EStateM.Result.ok () state
  := by
    simp [
      LeanRV64D.Functions.wX_bits,
      LeanRV64D.Functions.wX,
    ]

  set_option maxHeartbeats 0
  lemma wX_write_xreg_non_zero_equiv
    (data)
    (state)
    (rd_idx : regidx)
    (rd : Finset.Icc 1 31)
    (h_rd : rd_idx = regidx.Regidx (BitVec.ofNat 5 rd))
  :
    LeanRV64D.Functions.wX_bits rd_idx data state =
    write_xreg rd data state
  := by
    unfold LeanRV64D.Functions.wX_bits
    simp [h_rd]
    obtain ⟨rd, h_rd_range⟩ := rd
    obtain ⟨h_rd_low, h_rd_high⟩ := Finset.mem_Icc.mp h_rd_range
    rewrite [Int.emod_eq_of_lt (by grind) (by grind)]
    unfold LeanRV64D.Functions.wX
    simp [write_xreg]
    by_cases rd = 0 ; aesop
    by_cases rd = 1 ; aesop
    by_cases rd = 2 ; aesop
    by_cases rd = 3 ; aesop
    by_cases rd = 4 ; aesop
    by_cases rd = 5 ; aesop
    by_cases rd = 6 ; aesop
    by_cases rd = 7 ; aesop
    by_cases rd = 8 ; aesop
    by_cases rd = 9 ; aesop
    by_cases rd = 10 ; aesop
    by_cases rd = 11 ; aesop
    by_cases rd = 12 ; aesop
    by_cases rd = 13 ; aesop
    by_cases rd = 14 ; aesop
    by_cases rd = 15 ; aesop
    by_cases rd = 16 ; aesop
    by_cases rd = 17 ; aesop
    by_cases rd = 18 ; aesop
    by_cases rd = 19 ; aesop
    by_cases rd = 20 ; aesop
    by_cases rd = 21 ; aesop
    by_cases rd = 22 ; aesop
    by_cases rd = 23 ; aesop
    by_cases rd = 24 ; aesop
    by_cases rd = 25 ; aesop
    by_cases rd = 26 ; aesop
    by_cases rd = 27 ; aesop
    by_cases rd = 28 ; aesop
    by_cases rd = 29 ; aesop
    by_cases rd = 30 ; aesop
    by_cases rd = 31 ; aesop
    omega

  def write_reg_state
    (state: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (register: Register)
    (value: RegisterType register)
  : PreSail.SequentialState RegisterType Sail.trivialChoiceSource := {
      regs := state.regs.insert register value,
      choiceState := state.choiceState,
      mem := state.mem,
      tags := state.tags,
      cycleCount := state.cycleCount,
      sailOutput := state.sailOutput
    }

  lemma writeReg_state_success:
    (Sail.writeReg register value state) =
    EStateM.Result.ok PUnit.unit (write_reg_state state register value)
  := by
    simp [
      PreSail.writeReg,
      write_reg_state,
    ]

  @[simp]
  lemma writeReg_read_same
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  :
    (write_reg_state state register value).regs.get? register = Option.some value
  := by
    unfold write_reg_state
    grind

  @[simp]
  lemma writeReg_write_same
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  :
    write_reg_state
      (write_reg_state state register value1)
      register
      value2
    =
    write_reg_state state register value2
  := by
    simp [
      write_reg_state,
    ]
    apply Std.ExtDHashMap.ext_get?
    intro reg
    by_cases h: reg = register
    . grind
    . grind

  lemma writeReg_read_diff
    (h: state.regs.get? register1 = .some value1)
    (h_neq: register1 ≠ register2)
  :
    (write_reg_state state register2 value2).regs.get? register1 = Option.some value1
  := by
    unfold write_reg_state
    grind

  set_option maxHeartbeats 0
  lemma read_xreg_write_other_reg_state
    (r1 : Fin 32)
    (h: read_xreg r1 state = EStateM.Result.ok read_val state)
    (h_neq: reg_of_fin r1 ≠ register)
  :
    read_xreg r1 (write_reg_state state register write_val) =
    EStateM.Result.ok
      read_val
      (write_reg_state state register write_val)
  := by
    have h_reg : (¬ r1 = 0) → state.regs.get? (reg_of_fin r1) = .some (cast (by rw [register_type_reg_of_fin_equiv]) read_val)
    := by
      clear h_neq; intro h_neq
      simp [read_xreg, PreSail.readReg] at *
      simp [h_neq] at h
      by_cases h_r1 : state.regs.get? (reg_of_fin r1) = .none
      . fin_cases r1 <;> simp_all
      . obtain ⟨ val, eq_val ⟩ : ∃ val, state.regs.get? (reg_of_fin r1) = .some val
        := by
          obtain ⟨ x, eq_x ⟩ : ∃ x, state.regs.get? (reg_of_fin r1) = x := by simp
          rw [eq_x] at h_r1 ⊢
          clear *- h_r1
          rw [← Option.isSome_iff_exists]
          rw [← Option.not_isSome_iff_eq_none] at h_r1
          tauto
        fin_cases r1 <;> simp_all
    by_cases rz : r1 = 0
    . simp [rz, read_xreg] at h ⊢
      assumption
    . specialize h_reg rz
      have :=
        @writeReg_read_diff
          (reg_of_fin r1)
          register
          state
          write_val
          _
          h_reg
          h_neq
      simp [rz, read_xreg, PreSail.readReg]
      fin_cases r1 <;> simp_all

  set_option maxHeartbeats 0 in
  lemma rX_bits_write_other_reg_state
    (h_r_val : LeanRV64D.Functions.rX_bits (regidx.Regidx r) state = EStateM.Result.ok r_val state)
    (h_neq : (reg_of_fin r.toFin) ≠ reg)
  :
    LeanRV64D.Functions.rX_bits (regidx.Regidx r) (write_reg_state state reg val) =
    EStateM.Result.ok r_val (write_reg_state state reg val)
  := by
    trans read_xreg r.toFin (write_reg_state state reg val)
    . clear *-
      simp [read_xreg, LeanRV64D.Functions.rX_bits, LeanRV64D.Functions.rX]
      rcases r with ⟨r, ub_r⟩
      simp at *; simp at ub_r
      interval_cases r <;> simp [reg_of_fin] <;> grind
    . have := @read_xreg_write_other_reg_state state r_val reg val r.toFin
      have h_read_xreg : read_xreg r.toFin state = EStateM.Result.ok r_val state
      := by
        simp [read_xreg]
        simp [LeanRV64D.Functions.rX_bits, LeanRV64D.Functions.rX] at h_r_val
        rw [← h_r_val]; clear *-
        simp [reg_of_fin]
        rcases r with ⟨r, ub_r⟩
        simp at *; simp at ub_r
        interval_cases r <;> simp <;> grind
      tauto

  lemma reg_of_fin_neq_nextPC :
    (reg_of_fin r) ≠ Register.nextPC
  := by
    fin_cases r <;> simp [reg_of_fin]

  lemma reg_of_fin_neq_mstatus :
    (reg_of_fin r) ≠ Register.mstatus
  := by
    fin_cases r <;> simp [reg_of_fin]

  lemma reg_of_fin_neq_cur_privilege :
    (reg_of_fin r) ≠ Register.cur_privilege
  := by
    fin_cases r <;> simp [reg_of_fin]

  lemma reg_of_fin_neq_htif_tohost_base :
    (reg_of_fin r) ≠ Register.htif_tohost_base
  := by
    fin_cases r <;> simp [reg_of_fin]

  lemma reg_of_fin_neq_pma_regions :
    (reg_of_fin r) ≠ Register.pma_regions
  := by
    fin_cases r <;> simp [reg_of_fin]

  lemma readReg_of_write_other_reg_state
    (h_reg : Sail.readReg reg state = EStateM.Result.ok val state)
    (h_neq : reg ≠ reg')
  :
    Sail.readReg reg (write_reg_state state reg' val') =
    EStateM.Result.ok val (write_reg_state state reg' val')
  := by
    simp [
      Sail.readReg, PreSail.readReg, write_reg_state
    ] at ⊢ h_reg
    have :
      (state.regs.insert reg' val').get? reg = state.regs.get? reg
    := by grind
    simp [this]
    rcases h: state.regs.get? reg
    . simp [h] at h_reg
    . simp [h] at ⊢ h_reg
      exact h_reg

  lemma insert_reg_eq_self
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {r : Fin 32}
    (h_r_not_zero : ¬ r.val = 0)
    (h_read_xreg : (read_xreg r state = EStateM.Result.ok val state))
  :
    state.regs.insert (reg_of_fin r) ((register_type_reg_of_fin_equiv r) ▸ val) = state.regs
  := by
    rw [ExtDHashMap.insert_eq_self]
    suffices h_some : ((register_type_reg_of_fin_equiv r) ▸ (state.regs.get? (reg_of_fin r))) = .some val
    . generalize_proofs pfl pft at h_some
      rw [← eq_rec_inj (h := pft)]
      grind
    . simp [read_xreg, Sail.readReg, PreSail.readReg] at h_read_xreg
      cases h : state.regs.get? (reg_of_fin r) <;>
        fin_cases r <;> simp_all

end RegisterManipulation

section SimplerFunctions

  @[simp high]
  lemma bit_to_bool :
    LeanRV64D.Functions.bit_to_bool =
    λ b => b == 1#1
  := by
    unfold
      LeanRV64D.Functions.bit_to_bool
      LeanRV64D.Functions.bool_bit_backwards
    grind

  @[simp]
  lemma bool_bits_forwards_to_if {b : Bool} :
    LeanRV64D.Functions.bool_bits_forwards b = if b then 1#1 else 0#1
  := by aesop

  /-- In RV64D, `currentlyEnabled Ext_Zca` depends on `currentlyEnabled Ext_C`,
      which in turn reads misa bit 2. ZisK targets RV64IM only and therefore
      disables the C extension, i.e. the caller must witness `misa[2] = 0`.
      The original RV32D lemma takes only the misa-readable hypothesis because
      the upstream `LeanRV32D` `currentlyEnabled` definition for `Ext_Zca`
      ignores misa.  See `LeanRV64D/Types.lean` lines ~540-545.

      We carry this lemma locally (mirroring openvm-fv's
      `OpenvmFv/RV32D/Auxiliaries.lean::currentlyEnabled_Zca_of_misa_val`
      pattern). The dependency on `NethermindEth/sail-riscv-lean` is the
      stock upstream — no fork. -/
  @[simp high]
  lemma currentlyEnabled_Zca_of_misa_val
    {misa_val : BitVec 64}
    (h: state.regs.get? Register.misa = .some misa_val)
    (h_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    LeanRV64D.Functions.currentlyEnabled extension.Ext_Zca state =
    EStateM.Result.ok false state
  := by
    simp [LeanRV64D.Functions.currentlyEnabled,
          LeanRV64D.Functions._get_Misa_C,
          LeanRV64D.Functions.hartSupports]
    aesop

    @[simp high]
    lemma sail_assert_equiv :
      Sail.assert =
      λ check msg state =>
        if check
        then EStateM.Result.ok () state
        else EStateM.Result.error (Sail.Error.Assertion msg) state
    := by
      unfold Sail.assert PreSail.assert
      simp
      funext check message state
      cases check <;> simp

  @[simp]
  lemma translationMode_in_machine
  :
    LeanRV64D.Functions.translationMode Privilege.Machine state =
    EStateM.Result.ok ( SATPMode.Bare ) state
  := by
    aesop

  @[simp high]
  lemma set_next_pc_equiv :
    LeanRV64D.Functions.set_next_pc pc =
    Sail.writeReg Register.nextPC pc
  := rfl

end SimplerFunctions

section Memory

  -- ZisK uses a flat 32-bit guest-visible physical address space.
  notation "ZiskPhysicalAddressSpaceSize" => 2 ^ 32

  @[simp]
  lemma bare_is_bare : (SATPMode.Bare == SATPMode.Bare) = true := rfl

  lemma arithmetic_helper
    (h_ub : a + b < ZiskPhysicalAddressSpaceSize)
  :
    (a + b) % 4294967296 = (a + b) ∧
    (a + b) % 17179869184 = (a + b) ∧
    (a + b) % 18446744073709551616 = (a + b)
  := by
    omega

end Memory

section ControlFlow

  /-- In RV64D `jump_to` consults `currentlyEnabled Ext_Zca` to decide whether
      2-byte alignment is allowed. ZisK targets RV64IM only, so the C extension
      is disabled, i.e. the caller must witness `misa[2] = 0`.

      Closure relies on the `@[simp high]` local lemma
      `currentlyEnabled_Zca_of_misa_val` defined earlier in this file. -/
  lemma jump_to_equiv
    (h_misa : state.regs.get? Register.misa = .some misa_val)
    (h_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    LeanRV64D.Functions.jump_to target state =
      if (BitVec.ofBool target[0]) == 1#1 then EStateM.Result.error (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30") state
        else
          if (BitVec.ofBool target[1] == 1#1)
          then EStateM.Result.ok (ExecutionResult.Memory_Exception ((virtaddr.Virtaddr target), (ExceptionType.E_Fetch_Addr_Align ()))) state
          else EStateM.Result.ok (ExecutionResult.Retire_Success ()) (write_reg_state state Register.nextPC target)
  := by
    -- `jump_to` wraps its body in `SailME.run do ...`. The local `@[simp high]`
    -- lemma `currentlyEnabled_Zca_of_misa_val` reduces `currentlyEnabled Ext_Zca
    -- state` to `ok false state` under the misa-bit-2-zero hypothesis and fires
    -- implicitly via the simp-set.
    have h_c' : BitVec.extractLsb 2 2 misa_val = 0#1 := h_c
    simp [LeanRV64D.Functions.jump_to]
    by_cases h_bit_0 : BitVec.ofBool target[0] = 0#1 <;> simp [h_bit_0]
    . simp [readReg_succ h_misa, h_c']
      by_cases h_bit_1 : BitVec.ofBool target[1] = 1#1 <;> simp [h_bit_1]
      simp [writeReg_state_success]
    . grind

end ControlFlow

namespace ZiskFv.PlatformScope

  /-- **Platform-feature theorem (PMP off).** PMP is disabled in the
      RV64IM scope ZisK targets: no `pmpcfg_n` entry has its `A` field set
      to anything other than `OFF`, so the 16-entry match loop in
      `LeanRV64D.Functions.pmpCheck` never yields `PMP_Match` /
      `PMP_PartialMatch`, and the final `if priv == Machine then none`
      branch is taken. Under these conditions `pmpCheck` is a pure
      identity: it returns `(ok none, state)` unconditionally.

      Narrow and scope-honest: ZisK (per `CLAUDE.md`) excludes Zicclsm,
      precompiles, and privilege-model extensions; PMP is out of scope.

      Stated in monadic form (LHS `pmpCheck args`, not `pmpCheck args state`)
      so `simp` can rewrite the call inside a `bind` chain before `state`
      is threaded in. -/
  @[simp high]
  theorem pmpCheck_is_pure_none
    (addr : physaddr) (width : Nat) (acc : MemoryAccessType Unit)
    (priv : Privilege)
  : LeanRV64D.Functions.pmpCheck addr width acc priv
      = (pure none : SailM (Option ExceptionType))
  := by
    funext s
    simp [LeanRV64D.Functions.pmpCheck, LeanRV64D.Functions.sys_pmp_count]

  /-- **Platform-feature theorem (CLINT disjoint).** The CLINT MMIO region is
      never addressed by ZisK-generated code: user programs access only
      flat program memory. Under this scope commitment
      `LeanRV64D.Functions.within_clint` is a pure identity: it returns
      `(ok false, state)` unconditionally.

      The vendored `LeanRV64D` bakes in `plat_clint_base = 2^25` and
      `plat_clint_size = 786432`, which intersects the
      `ZiskPhysicalAddressSpaceSize = 2^32` envelope — so a state-level
      `addr_disjoint` precondition would be necessary to close `within_clint`
      for arbitrary widths. The opcodes here use concrete positive access
      widths, where the generated CLINT predicate reduces directly.

      Stated in monadic (uncurried) form for the same reason as
      `pmpCheck_is_pure_none`. -/
  theorem within_clint_is_false_of_pos_width
    (addr : physaddr) (width : Nat)
    (h_width : 0 < width)
  : LeanRV64D.Functions.within_clint addr width
      = (pure false : SailM Bool)
  := by
    funext state
    cases addr
    simp [
      LeanRV64D.Functions.within_clint,
      LeanRV64D.Functions.plat_clint_size,
      Sail.BitVec.toNatInt
    ]
    omega

  @[simp high] theorem within_clint_is_false_1 (addr : physaddr) :
    LeanRV64D.Functions.within_clint addr 1 = (pure false : SailM Bool) :=
    within_clint_is_false_of_pos_width addr 1 (by decide)

  @[simp high] theorem within_clint_is_false_2 (addr : physaddr) :
    LeanRV64D.Functions.within_clint addr 2 = (pure false : SailM Bool) :=
    within_clint_is_false_of_pos_width addr 2 (by decide)

  @[simp high] theorem within_clint_is_false_4 (addr : physaddr) :
    LeanRV64D.Functions.within_clint addr 4 = (pure false : SailM Bool) :=
    within_clint_is_false_of_pos_width addr 4 (by decide)

  @[simp high] theorem within_clint_is_false_8 (addr : physaddr) :
    LeanRV64D.Functions.within_clint addr 8 = (pure false : SailM Bool) :=
    within_clint_is_false_of_pos_width addr 8 (by decide)

  @[simp high]
  theorem pmaCheck_load_is_none
    (addr : BitVec 64) (width : Nat) (acc : Unit)
    (h_regions : Sail.readReg Register.pma_regions state = EStateM.Result.ok [pmaRegion] state)
    (h_base : pmaRegion.base = 0)
    (h_size : ZiskPhysicalAddressSpaceSize ≤ pmaRegion.size.toNat)
    (h_readable : pmaRegion.attributes.readable)
    (h_misaligned : pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
    (h_bound : addr.toNat + width ≤ ZiskPhysicalAddressSpaceSize)
    (h_div : (↑width : Int) ∣ ↑addr.toNat)
  : LeanRV64D.Functions.pmaCheck (physaddr.Physaddr addr) width (MemoryAccessType.Load acc) false state
      = EStateM.Result.ok none state
  := by
    have h_mod :
      (↑addr.toNat + ↑width) % 18446744073709551616 = ↑(addr.toNat + width) := by
      omega
    have h_range :
      addr.toNat ≤ pmaRegion.size.toNat ∧
        (↑addr.toNat + ↑width) % 18446744073709551616 ≤ ↑pmaRegion.size.toNat ∧
          ↑addr.toNat ≤ (↑addr.toNat + ↑width) % 18446744073709551616 := by
      rw [h_mod]
      omega
    simp [
      LeanRV64D.Functions.pmaCheck,
      LeanRV64D.Functions.matching_pma,
      LeanRV64D.Functions.matching_pma_bits_range,
      LeanRV64D.Functions.range_subset,
      LeanRV64D.Functions.bits_of_physaddr,
      h_regions, h_base, h_div, h_range
    ]
    rw [if_pos (by
      constructor
      · omega
      · omega)]
    simp [h_readable, h_misaligned]

  @[simp high]
  theorem pmaCheck_store_is_none
    (addr : BitVec 64) (width : Nat) (acc : Unit)
    (h_regions : Sail.readReg Register.pma_regions state = EStateM.Result.ok [pmaRegion] state)
    (h_base : pmaRegion.base = 0)
    (h_size : ZiskPhysicalAddressSpaceSize ≤ pmaRegion.size.toNat)
    (h_writable : pmaRegion.attributes.writable)
    (h_misaligned : pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault)
    (h_bound : addr.toNat + width ≤ ZiskPhysicalAddressSpaceSize)
    (h_div : (↑width : Int) ∣ ↑addr.toNat)
  : LeanRV64D.Functions.pmaCheck (physaddr.Physaddr addr) width (MemoryAccessType.Store acc) false state
      = EStateM.Result.ok none state
  := by
    have h_mod :
      (↑addr.toNat + ↑width) % 18446744073709551616 = ↑(addr.toNat + width) := by
      omega
    have h_range :
      addr.toNat ≤ pmaRegion.size.toNat ∧
        (↑addr.toNat + ↑width) % 18446744073709551616 ≤ ↑pmaRegion.size.toNat ∧
          ↑addr.toNat ≤ (↑addr.toNat + ↑width) % 18446744073709551616 := by
      rw [h_mod]
      omega
    simp [
      LeanRV64D.Functions.pmaCheck,
      LeanRV64D.Functions.matching_pma,
      LeanRV64D.Functions.matching_pma_bits_range,
      LeanRV64D.Functions.range_subset,
      LeanRV64D.Functions.bits_of_physaddr,
      h_regions, h_base, h_div, h_range
    ]
    rw [if_pos (by
      constructor
      · omega
      · omega)]
    simp [h_writable, h_misaligned]

  /-- **Platform-feature theorem (Zicfilp disabled).** The Zicfilp landing-pad
      extension is disabled in ZisK's RV64IM target. Under this scope
      `LeanRV64D.Functions.update_elp_state` (ZicfilpRegs.lean:224) is a
      no-op: its `currentlyEnabled Ext_Zicfilp` guard is always false,
      so the helper reduces to `pure ()`.

      The proof uses the machine-mode and `mseccfg` profile facts threaded
      through `RISC_V_assumptions`. -/
  @[simp high]
  theorem update_elp_state_is_pure_unit
    (rs1 : regidx)
    (h_priv : Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state)
  : LeanRV64D.Functions.update_elp_state rs1 state
      = EStateM.Result.ok () state
  := by
    simp [
      LeanRV64D.Functions.update_elp_state,
      LeanRV64D.Functions.currentlyEnabled,
      LeanRV64D.Functions.get_xLPE,
      LeanRV64D.Functions.hartSupports,
      h_priv,
      h_mseccfg
    ]

end ZiskFv.PlatformScope

section Spec

  @[simp]
  noncomputable def execute_instruction
    (instr : instruction)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  :=
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute instr
    ) state

  def RISC_V_assumptions
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
  : Prop :=
    -- Assumption A1.1: machine privilege
    Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state ∧
    -- Assumption A1.2: MPRV bit of the mstatus register not set
    (Sail.readReg Register.mstatus state = EStateM.Result.ok mstatus state ∧ BitVec.extractLsb 17 17 mstatus = 0#1) ∧
    -- A2.1 : Single PMA region
    Sail.readReg Register.pma_regions state = EStateM.Result.ok [ pmaRegion ] state ∧
    -- A2.2 : with base 0 and at least the flat 32-bit ZisK address space
    pmaRegion.base = 0 ∧
    ZiskPhysicalAddressSpaceSize ≤ pmaRegion.size.toNat ∧
    -- A2.3 : with all addresses readable and writable, and misaligned accesses treated as errors
    pmaRegion.attributes.readable ∧
    pmaRegion.attributes.writable ∧
    pmaRegion.attributes.misaligned_fault = misaligned_fault.AlignmentFault ∧
    -- Assumption A3: no host-target interface
    Sail.readReg Register.htif_tohost_base state = EStateM.Result.ok .none state ∧
    -- Assumption A4.1: misa register exists
    state.regs.get? Register.misa = .some misa ∧
    -- Assumption A4.2: mseccfg register exists
    Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state

  lemma RISC_V_assumptions_invariant_under_pc_increment
    (assumptions : RISC_V_assumptions s mstatus pmaRegion misa mseccfg)
  :
    RISC_V_assumptions (write_reg_state s Register.nextPC val) mstatus pmaRegion misa mseccfg
  := by
    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := assumptions
    refine ⟨ ?_, ⟨ ?_, ?_ ⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
    . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_priv (by trivial)]
    . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_mprv.1 (by trivial)]
    . exact h_mprv.2
    . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_pma_regions (by trivial)]
    . exact h_pma_base
    . exact h_pma_size
    . exact h_pma_readable
    . exact h_pma_writable
    . exact h_pma_misaligned
    . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_htif (by trivial)]
    . grind [write_reg_state]
    . rw [readReg_of_write_other_reg_state (reg' := Register.nextPC) (val' := val) h_mseccfg (by trivial)]

end Spec
