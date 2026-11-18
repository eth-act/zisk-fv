import ZiskFv.Compliance.TraceLevelExport.Base
import ZiskFv.AirsClean.ArithTableProjections

/-!
# Actual register-write provider chunk ranges

Source helpers for the physical C-register fold. These proofs use the existing
provider table specs and operation-bus matches at one actual Main source index;
the conclusions concern that source row's `cMemMessage`, not a packed-word proxy.

The Binary static routes use byte membership plus core/chain consequences for
logic, ADD/SUB, W mode and comparisons. BinaryAdd uses its output-chunk spec.
ArithMul selects its actual primary result role from the full/shared-div specs.
BinaryExtension uses the existing static shift/sign-extension lookup range
proofs. Carry and mode helpers retain the source-row interfaces used by the
consumer glue, so no opcode classifier, total physical-step family, stronger
source specification or caller-supplied actual-entry range is introduced.

The source proofs are the provider/arithmetic slice of `Soundness.lean` (formerly
private helpers at lines 320–925); this module does not import that endpoint.
The PC-store/control arithmetic is deliberately not part of this module.
-/

namespace ZiskFv.Compliance.PhysicalRegisterWriteRanges

open ZiskFv.AirsClean.FullEnsemble
  (mainTableRowAtOrZero mainOfTable mainOfTable_c_0 mainOfTable_c_1)
open ZiskFv.AirsClean.Main (cMemMessage)
open ZiskFv.Channels.MemoryBus (MemBusMessage.toEntry)

private lemma matches_entry_c_eq
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {i : ℕ} {msg : ZiskFv.Channels.OperationBus.OpBusMessage FGL}
    (h : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m i)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry msg 1)) :
    m.c_0 i = msg.c_lo ∧ m.c_1 i = msg.c_hi := by
  simp only [ZiskFv.Airs.OperationBus.matches_entry,
    ZiskFv.Airs.OperationBus.opBus_row_Main] at h
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

private lemma fgl_two_chunks_val_lt (a b : FGL)
    (ha : a.val < 65536) (hb : b.val < 65536) :
    (a * 65536 + b : FGL).val < 4294967296 := by
  have hav : (65536 : FGL).val = 65536 := by decide
  have h1 : a.val * (65536 : FGL).val % GL_prime = a.val * 65536 :=
    Nat.mod_eq_of_lt (by rw [hav]; omega)
  have h2 : (a.val * 65536 + b.val) % GL_prime = a.val * 65536 + b.val :=
    Nat.mod_eq_of_lt (by omega)
  simp only [Fin.val_add, Fin.val_mul, h1, h2]
  omega

private lemma fgl_two_chunks_val_lt_comm (a b : FGL)
    (ha : a.val < 65536) (hb : b.val < 65536) :
    (b + a * 65536 : FGL).val < 4294967296 := by
  rw [add_comm]; exact fgl_two_chunks_val_lt a b ha hb

private lemma fgl_two_bytes_val_lt (a b : FGL)
    (ha : a.val < 256) (hb : b.val < 256) :
    (a + 256 * b : FGL).val < 65536 := by
  have h256v : (256 : FGL).val = 256 := by decide
  have h1 : (256 : FGL).val * b.val % GL_prime = 256 * b.val :=
    Nat.mod_eq_of_lt (by rw [h256v]; omega)
  have h2 : (a.val + 256 * b.val) % GL_prime = a.val + 256 * b.val :=
    Nat.mod_eq_of_lt (by omega)
  simp only [Fin.val_add, Fin.val_mul, h256v]
  omega

private lemma fgl_four_bytes_val_lt (a b c d : FGL)
    (ha : a.val < 256) (hb : b.val < 256) (hc : c.val < 256) (hd : d.val < 256) :
    (a + 256 * b + 65536 * c + 16777216 * d : FGL).val < 4294967296 := by
  have h_eq : (a + 256 * b + 65536 * c + 16777216 * d : FGL)
      = (c + 256 * d) * 65536 + (a + 256 * b) := by ring
  rw [h_eq]
  exact fgl_two_chunks_val_lt _ _ (fgl_two_bytes_val_lt c d hc hd)
    (fgl_two_bytes_val_lt a b ha hb)

private lemma fgl_four_bytes_carry_val_lt (a b c d carry : FGL)
    (ha : a.val < 256) (hb : b.val < 256) (hc : c.val < 256) (hd : d.val < 256)
    (hcarry : carry = 0) :
    (a + 256 * b + 65536 * c + 16777216 * d + carry : FGL).val < 4294967296 := by
  rw [hcarry, add_zero]
  exact fgl_four_bytes_val_lt a b c d ha hb hc hd

/-- The four high result bytes are bounded by exact static BinaryTable membership. -/
lemma binary_static_opBus_c_hi_lt
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row) :
    (ZiskFv.AirsClean.Binary.opBusMessage row).c_hi.val < 4294967296 := by
  show (ZiskFv.AirsClean.Binary.cHiValue row).val < _
  unfold ZiskFv.AirsClean.Binary.cHiValue
  have hr4 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.2.2.1
  have hr5 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.2.2.2.1
  have hr6 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.2.2.2.2.1
  have hr7 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.2.2.2.2.2
  simp only [ZiskFv.Airs.Tables.BinaryTable.range_conditions] at hr4 hr5 hr6 hr7
  exact fgl_four_bytes_val_lt _ _ _ _ hr4.2.2.1 hr5.2.2.1 hr6.2.2.1 hr7.2.2.1

private lemma binary_static_opBus_c_lo_lt
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_carry : row.chain.carry_7 = 0) :
    (ZiskFv.AirsClean.Binary.opBusMessage row).c_lo.val < 4294967296 := by
  show (ZiskFv.AirsClean.Binary.cLoValue row).val < _
  unfold ZiskFv.AirsClean.Binary.cLoValue
  have hr0 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.1
  have hr1 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.1
  have hr2 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.1
  have hr3 := ZiskFv.AirsClean.BinaryTable.spec_range_conditions h_spec.2.2.2.1
  simp only [ZiskFv.Airs.Tables.BinaryTable.range_conditions] at hr0 hr1 hr2 hr3
  exact fgl_four_bytes_carry_val_lt _ _ _ _ _ hr0.2.2.1 hr1.2.2.1 hr2.2.2.1 hr3.2.2.1 h_carry

/-- Static table membership excludes opcode zero, fixing XOR mode and both opcode pins. -/
lemma mode_pins_of_emit_op_eq_16_of_static_spec
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (16 : FGL)) :
    row.mode.mode32 = 0
      ∧ row.chain.b_op.val = 16
      ∧ row.chain.b_op_or_sext.val = 16 := by
  have h_bop_ne : row.chain.b_op.val ≠ 0 := by
    have := ZiskFv.AirsClean.BinaryTable.spec_op_val_ne_zero h_static.1
    simpa [ZiskFv.AirsClean.Binary.lookupMessage0Row] using this
  have h_mode_bool : row.mode.mode32 * (1 - row.mode.mode32) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_mode32,
      ZiskFv.AirsClean.Binary.validOfRow] using h_core.1
  have h16v : (16 : FGL).val = 16 := by decide
  rcases (mul_eq_zero.mp h_mode_bool) with h_mode_zero | h_mode_sub
  · have h_bop_val : row.chain.b_op.val = 16 := by
      have hv := congrArg Fin.val h_emit
      simp only [Fin.val_add, Fin.val_mul] at hv
      rw [h_mode_zero] at hv
      simp only [Fin.val_zero, Nat.mul_zero,
        Nat.mod_eq_of_lt (by omega : 0 < GL_prime),
        Nat.add_zero,
        Nat.mod_eq_of_lt (show row.chain.b_op.val < GL_prime from row.chain.b_op.isLt),
        h16v] at hv
      exact hv
    have h_bop_or :=
      ZiskFv.EquivCore.Bridge.Binary.b_op_or_sext_val_eq_of_mode32_zero
        (ZiskFv.AirsClean.Binary.validOfRow row) 0 16
        h_core (by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_mode_zero)
        (by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop_val)
    exact ⟨h_mode_zero, h_bop_val,
      by simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_bop_or⟩
  · exfalso
    have h_mode_one : row.mode.mode32 = 1 := (sub_eq_zero.mp h_mode_sub).symm
    have h_bad : row.chain.b_op.val = 0 := by
      have hv := congrArg Fin.val h_emit
      simp only [Fin.val_add, Fin.val_mul] at hv
      rw [h_mode_one] at hv
      simp only [Fin.val_one, Nat.mul_one, h16v,
        Nat.mod_eq_of_lt (by omega : 16 < GL_prime)] at hv
      have hsmall : row.chain.b_op.val + 16 < GL_prime := by omega
      rw [Nat.mod_eq_of_lt hsmall] at hv
      omega
    exact h_bop_ne h_bad

/-- Derive the zero final carry for 64-bit ADD/SUB from the actual static byte chain. -/
lemma binary_static_add_sub_entry_range
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_wf : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (op_val : ℕ)
    (h_op_lt : op_val < 16)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_val : FGL))
    (h_op_add_or_sub :
      op_val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD ∨
      op_val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB) :
    row.chain.carry_7 = 0 := by
  have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
    row h_spec_facts op_val h_op_lt h_core h_emit
  have h_out := ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
    row h_wf op_val h_core h_pins.1 h_pins.2.1
  have h_carry_bool : (ZiskFv.AirsClean.Binary.validOfRow row).carry_7 0 *
      (1 - (ZiskFv.AirsClean.Binary.validOfRow row).carry_7 0) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_carry_7, ZiskFv.AirsClean.Binary.validOfRow]
      using h_core.2.1
  rcases h_op_add_or_sub with h | h
  · have := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_ADD_of_static_chain
      _ 0 (h ▸ h_out) h_core h_carry_bool
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using this
  · have := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_SUB_of_static_chain
      _ 0 (h ▸ h_out) h_core h_carry_bool
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using this

/-- Comparison byte-chain semantics zero the result bytes; the core bounds the final carry. -/
lemma binary_static_compare_c_lo_lt
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_wf : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (op_val : ℕ)
    (h_op_lt : op_val < 16)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_val : FGL))
    (h_c_zero_of_chain : ∀ {a b c cin flags pos : FGL},
      ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op_val a b c cin flags pos → c = 0) :
    (ZiskFv.AirsClean.Binary.opBusMessage row).c_lo.val < 4294967296 := by
  have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
    row h_spec_facts op_val h_op_lt h_core h_emit
  have h_out := ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
    row h_wf op_val h_core h_pins.1 h_pins.2.1
  have hc0 : row.cBytes.free_in_c_0 = 0 := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_c_zero_of_chain h_out.chain_0
  have hc1 : row.cBytes.free_in_c_1 = 0 := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_c_zero_of_chain h_out.chain_1
  have hc2 : row.cBytes.free_in_c_2 = 0 := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_c_zero_of_chain h_out.chain_2
  have hc3 : row.cBytes.free_in_c_3 = 0 := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_c_zero_of_chain h_out.chain_3
  have h_carry_bool : row.chain.carry_7 * (1 - row.chain.carry_7) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_carry_7,
      ZiskFv.AirsClean.Binary.validOfRow] using h_core.2.1
  show (ZiskFv.AirsClean.Binary.cLoValue row).val < _
  unfold ZiskFv.AirsClean.Binary.cLoValue
  rw [hc0, hc1, hc2, hc3]
  rcases mul_eq_zero.mp h_carry_bool with h | h
  · rw [h]; norm_num
  · have h1 := (sub_eq_zero.mp h).symm; rw [h1]; norm_num

/-- Derive W-mode and its zero final carry from static ADDW/SUBW membership and the core. -/
lemma binary_static_w_mode_carry_7_zero
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_spec_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_wf : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (op_val : ℕ)
    (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_val : FGL))
    (h_op_w : op_val = 26 ∨ op_val = 27) :
    row.chain.carry_7 = 0 := by
  have h_mode_bool : row.mode.mode32 * (1 - row.mode.mode32) = 0 := by
    simpa [ZiskFv.Airs.Binary.boolean_mode32,
      ZiskFv.AirsClean.Binary.validOfRow] using h_core.1
  have h_mode_one : row.mode.mode32 = 1 := by
    rcases mul_eq_zero.mp h_mode_bool with h | h
    · exfalso
      have h_ne := ZiskFv.AirsClean.BinaryTable.spec_op_val_ne_W_add_sub h_spec_facts.1
      have h_bop : row.chain.b_op = (op_val : FGL) := by
        have := h_emit; rw [h, mul_zero, add_zero] at this; exact this
      have h_bop_v := congrArg Fin.val h_bop
      simp only [Fin.val_natCast] at h_bop_v
      rcases h_op_w with rfl | rfl
      · exact h_ne.1 (by rw [show 26 % GL_prime = 26 from by omega] at h_bop_v; exact h_bop_v)
      · exact h_ne.2 (by rw [show 27 % GL_prime = 27 from by omega] at h_bop_v; exact h_bop_v)
    · exact (sub_eq_zero.mp h).symm
  have h_bop_val : row.chain.b_op.val = op_val - 16 := by
    have hv := congrArg Fin.val h_emit
    simp only [Fin.val_add, Fin.val_mul] at hv
    rw [h_mode_one] at hv
    have h16v : (16 : FGL).val = 16 := by decide
    simp only [Fin.val_one, Nat.mul_one, h16v,
      Nat.mod_eq_of_lt (by omega : 16 < GL_prime)] at hv
    have h_lt : row.chain.b_op.val < GL_prime := row.chain.b_op.isLt
    rcases h_op_w with rfl | rfl
    · simp only [Fin.val_natCast,
        Nat.mod_eq_of_lt (by omega : 26 < GL_prime)] at hv; omega
    · simp only [Fin.val_natCast,
        Nat.mod_eq_of_lt (by omega : 27 < GL_prime)] at hv; omega
  have h_bop_add_or_sub :
      row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD ∨
      row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB := by
    rcases h_op_w with rfl | rfl
    · left; rw [h_bop_val]; rfl
    · right; rw [h_bop_val]; rfl
  exact (ZiskFv.EquivCore.Bridge.Binary.w_mode_sext_choice_and_carry_7_zero_of_static_row
    row h_spec_facts h_wf h_core h_mode_one h_bop_add_or_sub).2

lemma cMemMessage_chunks_of_store_pc_zero
    (m : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (h_sp : m.core.store_pc = 0)
    (h_c0 : m.core.c_0.val < 4294967296)
    (h_c1 : m.core.c_1.val < 4294967296) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage m).toEntry 1 1) := by
  simp only [ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range,
    h_sp]
  constructor
  · show (0 * _ + m.core.c_0).val < _; simp [h_c0]
  · have : ((1 : FGL) - 0) * m.core.c_1 = m.core.c_1 := by ring
    rw [this]; exact h_c1

/-- Transfer genuine provider result-chunk bounds through the accepted match to the actual Main C message. -/
lemma entry_range_of_provider_match
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    {msg : ZiskFv.Channels.OperationBus.OpBusMessage FGL}
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry msg 1))
    (h_clo : msg.c_lo.val < 4294967296)
    (h_chi : msg.c_hi.val < 4294967296) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  have ⟨hc0_eq, hc1_eq⟩ := matches_entry_c_eq h_match
  simp only [mainOfTable_c_0] at hc0_eq
  simp only [mainOfTable_c_1] at hc1_eq
  exact cMemMessage_chunks_of_store_pc_zero _ h_sp
    (hc0_eq ▸ h_clo) (hc1_eq ▸ h_chi)

/-- Bound Main's C message using full Binary facts derived from its finished source channel. -/
lemma binary_static_entry_range
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    {providerTable providerRow}
    (_ : providerTable ∈ trace.witness.allTables)
    (h_pr : providerRow ∈ providerTable.table)
    (h_component : providerTable.component =
      ZiskFv.AirsClean.Binary.tableConsumerComponent)
    (h_spec : ∀ row ∈ providerTable.table,
      ZiskFv.AirsClean.Binary.Spec
        (ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
          (providerTable.environment row)) ∧
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts
        (ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
          (providerTable.environment row)))
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_carry :
      (ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
        (providerTable.environment providerRow)).chain.carry_7 = 0) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  have h_row_spec := (h_spec providerRow h_pr).2
  exact entry_range_of_provider_match i h_sp h_match
    (binary_static_opBus_c_lo_lt
      (ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
        (providerTable.environment providerRow)) h_row_spec h_carry)
    (binary_static_opBus_c_hi_lt
      (ZiskFv.AirsClean.Binary.tableConsumerComponent.rowInput
        (providerTable.environment providerRow)) h_row_spec)

private lemma binaryAdd_opBus_c_lo_lt (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)
    (h : ZiskFv.AirsClean.BinaryAdd.ComponentSpecFacts row) :
    (ZiskFv.AirsClean.BinaryAdd.opBusMessage row).c_lo.val < 4294967296 := by
  show (row.c_chunks_1 * 65536 + row.c_chunks_0 : FGL).val < _
  exact fgl_two_chunks_val_lt _ _ (by have := h.2.2.2.2.2.1; omega) (by have := h.2.2.2.2.1; omega)

private lemma binaryAdd_opBus_c_hi_lt (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)
    (h : ZiskFv.AirsClean.BinaryAdd.ComponentSpecFacts row) :
    (ZiskFv.AirsClean.BinaryAdd.opBusMessage row).c_hi.val < 4294967296 := by
  show (row.c_chunks_3 * 65536 + row.c_chunks_2 : FGL).val < _
  exact fgl_two_chunks_val_lt _ _ (by have := h.2.2.2.2.2.2.2; omega) (by have := h.2.2.2.2.2.2.1; omega)

/-- Bound the actual Main C message using the matching BinaryAdd provider's four 16-bit output chunks. -/
lemma binaryAdd_entry_range
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    {providerTable providerRow}
    (_ : providerTable ∈ trace.witness.allTables)
    (h_pr : providerRow ∈ providerTable.table)
    (h_component : providerTable.component = ZiskFv.AirsClean.BinaryAdd.component)
    (h_spec : providerTable.Spec)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryAdd.opBusMessage
          (ZiskFv.AirsClean.BinaryAdd.component.rowInput
            (providerTable.environment providerRow))) 1)) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  have h_facts : ZiskFv.AirsClean.BinaryAdd.ComponentSpecFacts
      (ZiskFv.AirsClean.BinaryAdd.component.rowInput
        (providerTable.environment providerRow)) := by
    simpa [h_component, ZiskFv.AirsClean.BinaryAdd.component_spec] using
      h_spec providerRow h_pr
  exact entry_range_of_provider_match i h_sp h_match
    (binaryAdd_opBus_c_lo_lt _ h_facts)
    (binaryAdd_opBus_c_hi_lt _ h_facts)

private lemma arithMul_opBus_c_lo_lt
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_full : ZiskFv.AirsClean.ArithMul.FullSpec row)
    (h_div_block : ZiskFv.AirsClean.ArithMul.SharedDivBlockSpec row) :
    (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage row).c_lo.val < 4294967296 := by
  have h_chunks := h_full.2.2.2.1
  have h_div_mode := h_div_block.1
  have h_mm_bool := h_div_mode.2.1
  have h_md_bool := h_div_mode.1
  have h_mm_md := h_div_mode.2.2.1
  show ((1 - row.flags.main_mul - row.flags.main_div) * (row.chunks.d_0 + row.chunks.d_1 * 65536)
    + row.flags.main_mul * (row.chunks.c_0 + row.chunks.c_1 * 65536)
    + row.flags.main_div * (row.chunks.a_0 + row.chunks.a_1 * 65536)).val < _
  rcases mul_eq_zero.mp h_mm_bool with hmm | hmm
  · rcases mul_eq_zero.mp h_md_bool with hmd | hmd
    · have h1 : (1 : FGL) - 0 - 0 = 1 := by ring
      simp only [hmm, hmd, zero_mul, add_zero, h1, one_mul]
      exact fgl_two_chunks_val_lt_comm row.chunks.d_1 row.chunks.d_0
        h_chunks.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h_chunks.2.2.2.2.2.2.2.2.2.2.2.2.1
    · have hmd1 := sub_eq_zero.mp hmd
      have h1 : (1 : FGL) - 0 - 1 = 0 := by ring
      simp only [hmm, hmd1, zero_mul, add_zero, zero_add, h1, one_mul]
      exact fgl_two_chunks_val_lt_comm row.chunks.a_1 row.chunks.a_0
        h_chunks.2.1 h_chunks.1
  · have hmm1 := sub_eq_zero.mp hmm
    have hmd0 : row.flags.main_div = 0 := by
      have h := hmm1 ▸ h_mm_md; rwa [one_mul] at h
    have h1 : (1 : FGL) - 1 - 0 = 0 := by ring
    simp only [hmm1, hmd0, h1, zero_mul, zero_add, one_mul, add_zero]
    exact fgl_two_chunks_val_lt_comm row.chunks.c_1 row.chunks.c_0
      h_chunks.2.2.2.2.2.2.2.2.2.1 h_chunks.2.2.2.2.2.2.2.2.1

private lemma arithMul_opBus_c_hi_lt
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_full : ZiskFv.AirsClean.ArithMul.FullSpec row)
    (h_div_block : ZiskFv.AirsClean.ArithMul.SharedDivBlockSpec row) :
    (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage row).c_hi.val < 4294967296 := by
  have h_chunks := h_full.2.2.2.1
  have h_table := h_full.2.1
  have h_c46 := h_full.2.2.1
  have h_div_mode := h_div_block.1
  have h_mm_bool := h_div_mode.2.1
  have h_md_bool := h_div_mode.1
  have h_mm_md := h_div_mode.2.2.1
  show row.flags.bus_res1.val < _
  have hbus : row.flags.bus_res1 = row.flags.sext * 4294967295
      + (1 - row.flags.m32) * (
          (1 - row.flags.main_mul - row.flags.main_div) * (row.chunks.d_2 + row.chunks.d_3 * 65536)
          + row.flags.main_mul * (row.chunks.c_2 + row.chunks.c_3 * 65536)
          + row.flags.main_div * (row.chunks.a_2 + row.chunks.a_3 * 65536)) :=
    sub_eq_zero.mp h_c46
  rw [hbus]
  rcases ZiskFv.AirsClean.ArithTableProjections.m32_boolean row h_table with hm32 | hm32
  · have hsext := ZiskFv.AirsClean.ArithTableProjections.sext_zero_of_m32_zero row h_table hm32
    simp only [hm32, hsext, zero_mul, zero_add, sub_zero, one_mul]
    rcases mul_eq_zero.mp h_mm_bool with hmm | hmm
    · rcases mul_eq_zero.mp h_md_bool with hmd | hmd
      · have h1 : (1 : FGL) - 0 - 0 = 1 := by ring
        simp only [hmm, hmd, h1, one_mul, zero_mul, add_zero]
        exact fgl_two_chunks_val_lt_comm row.chunks.d_3 row.chunks.d_2
          h_chunks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h_chunks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      · have hmd1 := sub_eq_zero.mp hmd
        have h1 : (1 : FGL) - 0 - 1 = 0 := by ring
        simp only [hmm, hmd1, zero_mul, add_zero, zero_add, h1, one_mul]
        exact fgl_two_chunks_val_lt_comm row.chunks.a_3 row.chunks.a_2
          h_chunks.2.2.2.1 h_chunks.2.2.1
    · have hmm1 := sub_eq_zero.mp hmm
      have hmd0 : row.flags.main_div = 0 := by
        have h := hmm1 ▸ h_mm_md; rwa [one_mul] at h
      have h1 : (1 : FGL) - 1 - 0 = 0 := by ring
      simp only [hmm1, hmd0, h1, zero_mul, zero_add, one_mul, add_zero]
      exact fgl_two_chunks_val_lt_comm row.chunks.c_3 row.chunks.c_2
        h_chunks.2.2.2.2.2.2.2.2.2.2.2.1 h_chunks.2.2.2.2.2.2.2.2.2.2.1
  · simp only [hm32, sub_self, zero_mul, add_zero]
    rcases ZiskFv.AirsClean.ArithTableProjections.sext_boolean row h_table with hs | hs
    · simp only [hs, zero_mul]; decide
    · simp only [hs, one_mul]
      show (4294967295 : FGL).val < 4294967296
      decide

/-- Bound the actual Main C message for all primary ArithMul roles using FullSpec and SharedDivBlockSpec. -/
lemma arithMul_entry_range
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    {providerTable providerRow}
    (_ : providerTable ∈ trace.witness.allTables)
    (hpr : providerRow ∈ providerTable.table)
    (hcomp : providerTable.component =
      ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent)
    (hspec : providerTable.Spec)
    (hmatch : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
            (providerTable.environment providerRow))) 1)) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  have h_row := (hspec providerRow hpr)
  rw [hcomp, ZiskFv.AirsClean.ArithMul.componentComplete_spec] at h_row
  exact entry_range_of_provider_match i h_sp hmatch
    (arithMul_opBus_c_lo_lt _ h_row.1 h_row.2)
    (arithMul_opBus_c_hi_lt _ h_row.1 h_row.2)

private lemma fgl_sum8_val_lt (a b c d e f g h : FGL)
    (hlt : a.val + b.val + c.val + d.val + e.val + f.val + g.val + h.val < 4294967296) :
    (a + b + c + d + e + f + g + h : FGL).val < 4294967296 := by
  have h1 : (a + b).val = a.val + b.val := by
    rw [Fin.val_add]; exact Nat.mod_eq_of_lt (by omega)
  have h2 : (a + b + c).val = a.val + b.val + c.val := by
    rw [Fin.val_add, h1]; exact Nat.mod_eq_of_lt (by omega)
  have h3 : (a + b + c + d).val = a.val + b.val + c.val + d.val := by
    rw [Fin.val_add, h2]; exact Nat.mod_eq_of_lt (by omega)
  have h4 : (a + b + c + d + e).val = a.val + b.val + c.val + d.val + e.val := by
    rw [Fin.val_add, h3]; exact Nat.mod_eq_of_lt (by omega)
  have h5 : (a + b + c + d + e + f).val = a.val + b.val + c.val + d.val + e.val + f.val := by
    rw [Fin.val_add, h4]; exact Nat.mod_eq_of_lt (by omega)
  have h6 : (a + b + c + d + e + f + g).val =
      a.val + b.val + c.val + d.val + e.val + f.val + g.val := by
    rw [Fin.val_add, h5]; exact Nat.mod_eq_of_lt (by omega)
  rw [Fin.val_add, h6]; rw [Nat.mod_eq_of_lt (by omega)]; omega

open ZiskFv.AirsClean.BinaryExtension
  (opBusMessage validOfRow StaticBinaryExtensionTableSpecFacts ShiftB0RangeSpecFact) in
open ZiskFv.Airs.BinaryExtension
  (binary_extension_row_byte_lookups ByteLookupWfHypotheses a_bytes_in_range) in
open ZiskFv.AirsClean.BinaryExtensionTable (spec_wf_properties) in
private lemma binExt_shift_opBus_c_lt
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (h_spec_facts : StaticBinaryExtensionTableSpecFacts row)
    (h_op : row.flags.op = ZiskFv.Trusted.OP_SLL
          ∨ row.flags.op = ZiskFv.Trusted.OP_SRL
          ∨ row.flags.op = ZiskFv.Trusted.OP_SRA
          ∨ row.flags.op = ZiskFv.Trusted.OP_SLL_W
          ∨ row.flags.op = ZiskFv.Trusted.OP_SRL_W
          ∨ row.flags.op = ZiskFv.Trusted.OP_SRA_W) :
    (opBusMessage row).c_lo.val < 4294967296
    ∧ (opBusMessage row).c_hi.val < 4294967296 := by
  let v := validOfRow row
  let h_bytes := binary_extension_row_byte_lookups v 0
  have h_wfs : ByteLookupWfHypotheses h_bytes := by
    rcases h_spec_facts with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨spec_wf_properties h0, spec_wf_properties h1, spec_wf_properties h2,
      spec_wf_properties h3, spec_wf_properties h4, spec_wf_properties h5,
      spec_wf_properties h6, spec_wf_properties h7⟩
  have h_a_range : a_bytes_in_range v 0 := by
    exact ⟨h_wfs.1.1.1, h_wfs.2.1.1.1, h_wfs.2.2.1.1.1, h_wfs.2.2.2.1.1.1,
      h_wfs.2.2.2.2.1.1.1, h_wfs.2.2.2.2.2.1.1.1, h_wfs.2.2.2.2.2.2.1.1.1,
      h_wfs.2.2.2.2.2.2.2.1.1⟩
  have h_v_op : (v.op 0) = row.flags.op := rfl
  have mk_lt (h_sums : _ ∧ _) : (opBusMessage row).c_lo.val < 4294967296
      ∧ (opBusMessage row).c_hi.val < 4294967296 :=
    ⟨fgl_sum8_val_lt _ _ _ _ _ _ _ _ h_sums.1,
     fgl_sum8_val_lt _ _ _ _ _ _ _ _ h_sums.2⟩
  rcases h_op with h | h | h | h | h | h
  · exact mk_lt (ZiskFv.Airs.BinaryExtension.binary_extension_sll_c_sums_lt_of_wf
        v 0 (by rw [h_v_op, h]; decide) h_bytes h_wfs h_a_range)
  · exact mk_lt (ZiskFv.Airs.BinaryExtension.binary_extension_srl_c_sums_lt_of_wf
        v 0 (by rw [h_v_op, h]; decide) h_bytes h_wfs h_a_range)
  · exact mk_lt (ZiskFv.Airs.BinaryExtension.binary_extension_sra_c_sums_lt_of_wf
        v 0 (by rw [h_v_op, h]; decide) h_bytes h_wfs h_a_range)
  · exact mk_lt (ZiskFv.Airs.BinaryExtension.binary_extension_sllw_c_sums_lt_of_wf
        v 0 (by rw [h_v_op, h]; decide) h_bytes h_wfs h_a_range)
  · exact mk_lt (ZiskFv.Airs.BinaryExtension.binary_extension_srlw_c_sums_lt_of_wf
        v 0 (by rw [h_v_op, h]; decide) h_bytes h_wfs h_a_range)
  · exact mk_lt (ZiskFv.Airs.BinaryExtension.binary_extension_sraw_c_sums_lt_of_wf
        v 0 (by rw [h_v_op, h]; decide) h_bytes h_wfs h_a_range)

open ZiskFv.AirsClean.BinaryExtension
  (opBusMessage shiftTableConsumerComponent Spec
   StaticBinaryExtensionTableSpecFacts ShiftB0RangeSpecFact) in
/-- Bound Main's C message from the actual shift consumer's full source-derived row facts. -/
lemma binExt_shift_entry_range
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    {providerTable providerRow}
    (_ : providerTable ∈ trace.witness.allTables)
    (hpr : providerRow ∈ providerTable.table)
    (hcomp : providerTable.component = shiftTableConsumerComponent)
    (hspec : ∀ row ∈ providerTable.table,
      Spec (shiftTableConsumerComponent.rowInput (providerTable.environment row)) ∧
      StaticBinaryExtensionTableSpecFacts
        (shiftTableConsumerComponent.rowInput (providerTable.environment row)) ∧
      ShiftB0RangeSpecFact
        (shiftTableConsumerComponent.rowInput (providerTable.environment row)))
    (hmatch : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (opBusMessage
          (shiftTableConsumerComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SLL
      ∨ (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRL
      ∨ (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRA
      ∨ (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SLL_W
      ∨ (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRL_W
      ∨ (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRA_W) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  set theRow := shiftTableConsumerComponent.rowInput (providerTable.environment providerRow)
  have h_row_spec := hspec providerRow hpr
  have h_op_eq := hmatch.2.1
  simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
  rw [h_op_eq] at h_main_op
  have h_c_lt := binExt_shift_opBus_c_lt theRow h_row_spec.2.1 h_main_op
  exact entry_range_of_provider_match i h_sp hmatch h_c_lt.1 h_c_lt.2

/-- Bound the actual Main C message from the actual sign-extension provider's static byte lookups. -/
lemma binExt_sext_entry_range
    {n : ℕ} {trace : AcceptedZiskTrace n}
    (i : Fin n)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SIGNEXTEND_B
      ∨ (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SIGNEXTEND_H
      ∨ (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SIGNEXTEND_W) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  obtain ⟨h_op, h_clo, h_chi⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      (mainOfTable trace.program trace.mainTable) v i.val r_binary h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes] using
      ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookup_wfs_of_static_lookup
        v r_binary offset env h_static
  have mk_range
      (h_sums :
        ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val
          < 4294967296)
        ∧ ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val
          < 4294967296)) :
      ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
        ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
    apply cMemMessage_chunks_of_store_pc_zero _ h_sp
    · rw [show (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.c_0 =
          (mainOfTable trace.program trace.mainTable).c_0 i.val from by
          simp only [mainOfTable_c_0], h_clo]
      exact fgl_sum8_val_lt _ _ _ _ _ _ _ _ h_sums.1
    · rw [show (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.c_1 =
          (mainOfTable trace.program trace.mainTable).c_1 i.val from by
          simp only [mainOfTable_c_1], h_chi]
      exact fgl_sum8_val_lt _ _ _ _ _ _ _ _ h_sums.2
  rcases h_main_op with h_b | h_h | h_w
  · exact mk_range
      (ZiskFv.Airs.BinaryExtension.binary_extension_sext_b_c_sums_lt_of_wf
        v r_binary (by rw [← h_op, h_b]; decide) h_bytes h_wfs)
  · exact mk_range
      (ZiskFv.Airs.BinaryExtension.binary_extension_sext_h_c_sums_lt_of_wf
        v r_binary (by rw [← h_op, h_h]; decide) h_bytes h_wfs)
  · exact mk_range
      (ZiskFv.Airs.BinaryExtension.binary_extension_sext_w_c_sums_lt_of_wf
        v r_binary (by rw [← h_op, h_w]; decide) h_bytes h_wfs)

end ZiskFv.Compliance.PhysicalRegisterWriteRanges
