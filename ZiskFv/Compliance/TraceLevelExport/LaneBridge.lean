import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.AirsClean.Main.Spec
import ZiskFv.AirsClean.CompletenessHelpers

/-!
# LaneBridge — per-step register-column lane equalities

`LaneBridge` packages four universally quantified lane equalities (a_0/a_1/b_0/b_1)
at a single step `k`. Each equality fires when the ROM says the corresponding source
channel reads from a nonzero register. The `*_of_laneBridge` helpers below derive
unconditional equalities by case-splitting on `r = 0` (SourceSpec path) vs `r ≠ 0`
(LaneBridge path).
-/

namespace ZiskFv.Compliance

open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)

structure LaneBridge {n : Nat} (trace : AcceptedZiskTrace n)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) (k : ℕ) : Prop where
  a_lo : ∀ (r : Fin 32), r ≠ 0 →
    (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_src_reg = 1 →
    Transpiler.wrap_to_regidx
      (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 = r →
    (mainOfTable trace.program trace.mainTable).a_0 k =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg r)
  a_hi : ∀ (r : Fin 32), r ≠ 0 →
    (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_src_reg = 1 →
    Transpiler.wrap_to_regidx
      (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 = r →
    (mainOfTable trace.program trace.mainTable).a_1 k =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg r)
  b_lo : ∀ (r : Fin 32), r ≠ 0 →
    (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_src_reg = 1 →
    Transpiler.wrap_to_regidx
      (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_offset_imm0 = r →
    (mainOfTable trace.program trace.mainTable).b_0 k =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg r)
  b_hi : ∀ (r : Fin 32), r ≠ 0 →
    (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_src_reg = 1 →
    Transpiler.wrap_to_regidx
      (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_offset_imm0 = r →
    (mainOfTable trace.program trace.mainTable).b_1 k =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg r)

/-! ## Unconditional lane equalities from LaneBridge + SourceSpec + Decode fields -/

theorem fgl_eq_of_mul_sub_zero (a b : FGL) (h : (1 : FGL) * (a + -1 * b) = 0) :
    a = b := by
  simp only [one_mul] at h
  have : a = -(-1 * b) + 0 := by rw [← h]; ring
  simp at this; exact this

theorem a_lo_of_laneBridge
    {n : Nat} (trace : AcceptedZiskTrace n)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (k : ℕ) (r : Fin 32)
    (lb : LaneBridge trace state k)
    (hSS : ZiskFv.AirsClean.Main.SourceSpec (mainTableRowAtOrZero trace.program trace.mainTable k))
    (h_src_reg : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_src_reg =
      ZiskFv.AirsClean.boolF (decide (r ≠ 0)))
    (h_offset : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 =
      Transpiler.ind r)
    (h_src_imm : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_src_imm =
      ZiskFv.AirsClean.boolF (decide (r = 0)))
    (h_imm1 : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_imm1 = 0) :
    (mainOfTable trace.program trace.mainTable).a_0 k =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg r) := by
  by_cases hr : (r : Fin 32) = 0
  · subst hr
    simp only [ne_eq, not_true_eq_false, decide_false, decide_true,
      ZiskFv.AirsClean.boolF] at h_src_imm
    have ⟨hss1, _, _, _⟩ := hSS
    rw [h_src_imm] at hss1
    have ha0 : (mainOfTable trace.program trace.mainTable).a_0 k =
        (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 :=
      fgl_eq_of_mul_sub_zero _ _ hss1
    rw [ha0, h_offset]
    simp [Transpiler.ind, ZiskFv.Trusted.lane_lo,
      ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64, read_xreg]
  · exact lb.a_lo r hr
      (by rw [h_src_reg]; simp [ZiskFv.AirsClean.boolF, hr])
      (by rw [h_offset, Transpiler.wrap_to_regidx_ind])

theorem a_hi_of_laneBridge
    {n : Nat} (trace : AcceptedZiskTrace n)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (k : ℕ) (r : Fin 32)
    (lb : LaneBridge trace state k)
    (hSS : ZiskFv.AirsClean.Main.SourceSpec (mainTableRowAtOrZero trace.program trace.mainTable k))
    (h_src_reg : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_src_reg =
      ZiskFv.AirsClean.boolF (decide (r ≠ 0)))
    (h_offset : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 =
      Transpiler.ind r)
    (h_src_imm : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_src_imm =
      ZiskFv.AirsClean.boolF (decide (r = 0)))
    (h_imm1 : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_imm1 = 0) :
    (mainOfTable trace.program trace.mainTable).a_1 k =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg r) := by
  by_cases hr : (r : Fin 32) = 0
  · subst hr
    simp only [ne_eq, not_true_eq_false, decide_false, decide_true,
      ZiskFv.AirsClean.boolF] at h_src_imm
    have ⟨_, hss2, _, _⟩ := hSS
    rw [h_src_imm, h_imm1] at hss2
    have ha1 : (mainOfTable trace.program trace.mainTable).a_1 k = 0 :=
      fgl_eq_of_mul_sub_zero _ _ hss2
    rw [ha1]
    simp [ZiskFv.Trusted.lane_hi,
      ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64, read_xreg]
  · exact lb.a_hi r hr
      (by rw [h_src_reg]; simp [ZiskFv.AirsClean.boolF, hr])
      (by rw [h_offset, Transpiler.wrap_to_regidx_ind])

theorem b_lo_of_laneBridge
    {n : Nat} (trace : AcceptedZiskTrace n)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (k : ℕ) (r : Fin 32)
    (lb : LaneBridge trace state k)
    (hSS : ZiskFv.AirsClean.Main.SourceSpec (mainTableRowAtOrZero trace.program trace.mainTable k))
    (h_src_reg : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_src_reg =
      ZiskFv.AirsClean.boolF (decide (r ≠ 0)))
    (h_offset : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_offset_imm0 =
      Transpiler.ind r)
    (h_src_imm : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_src_imm =
      ZiskFv.AirsClean.boolF (decide (r = 0)))
    (h_imm1 : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_imm1 = 0) :
    (mainOfTable trace.program trace.mainTable).b_0 k =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg r) := by
  by_cases hr : (r : Fin 32) = 0
  · subst hr
    simp only [ne_eq, not_true_eq_false, decide_false, decide_true,
      ZiskFv.AirsClean.boolF] at h_src_imm
    have ⟨_, _, hss3, _⟩ := hSS
    rw [h_src_imm] at hss3
    have hb0 : (mainOfTable trace.program trace.mainTable).b_0 k =
        (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_offset_imm0 :=
      fgl_eq_of_mul_sub_zero _ _ hss3
    rw [hb0, h_offset]
    simp [Transpiler.ind, ZiskFv.Trusted.lane_lo,
      ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64, read_xreg]
  · exact lb.b_lo r hr
      (by rw [h_src_reg]; simp [ZiskFv.AirsClean.boolF, hr])
      (by rw [h_offset, Transpiler.wrap_to_regidx_ind])

theorem b_hi_of_laneBridge
    {n : Nat} (trace : AcceptedZiskTrace n)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (k : ℕ) (r : Fin 32)
    (lb : LaneBridge trace state k)
    (hSS : ZiskFv.AirsClean.Main.SourceSpec (mainTableRowAtOrZero trace.program trace.mainTable k))
    (h_src_reg : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_src_reg =
      ZiskFv.AirsClean.boolF (decide (r ≠ 0)))
    (h_offset : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_offset_imm0 =
      Transpiler.ind r)
    (h_src_imm : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_src_imm =
      ZiskFv.AirsClean.boolF (decide (r = 0)))
    (h_imm1 : (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_imm1 = 0) :
    (mainOfTable trace.program trace.mainTable).b_1 k =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg r) := by
  by_cases hr : (r : Fin 32) = 0
  · subst hr
    simp only [ne_eq, not_true_eq_false, decide_false, decide_true,
      ZiskFv.AirsClean.boolF] at h_src_imm
    have ⟨_, _, _, hss4⟩ := hSS
    rw [h_src_imm, h_imm1] at hss4
    have hb1 : (mainOfTable trace.program trace.mainTable).b_1 k = 0 :=
      fgl_eq_of_mul_sub_zero _ _ hss4
    rw [hb1]
    simp [ZiskFv.Trusted.lane_hi,
      ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64, read_xreg]
  · exact lb.b_hi r hr
      (by rw [h_src_reg]; simp [ZiskFv.AirsClean.boolF, hr])
      (by rw [h_offset, Transpiler.wrap_to_regidx_ind])

end ZiskFv.Compliance
