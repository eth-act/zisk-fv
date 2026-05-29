import ZiskFv.AirsClean.Main.Soundness
import ZiskFv.AirsClean.Main.Constraints
import ZiskFv.Airs.Main.Main
import ZiskFv.Channels.OperationBus
import ZiskFv.Channels.MemoryBus
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.MemoryBus

/-!
# `Valid_Main` ↔ `MainRow` compatibility bridge (long-lived)

This is the **central Bridge** — every opcode's `EquivCore/<Op>.lean`
proof takes `m : Valid_Main FGL FGL`. The Bridge preserves the
`Valid_Main` parameter shape through Phases C and D, so opcode-level
proofs compile unchanged until the final Phase D3 (drop circuit field).

The cross-row pc_handshake adjacency theorem is NOT in this Phase B
commit; it's tracked as Phase B.1 follow-up. Per-row Spec is what
the Component captures.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open ZiskFv.Channels.OperationBus
open ZiskFv.Channels.MemoryBus


@[reducible]
def rowAt (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r : ℕ) : MainRow FGL where
  a_0 := m.a_0 r
  a_1 := m.a_1 r
  b_0 := m.b_0 r
  b_1 := m.b_1 r
  c_0 := m.c_0 r
  c_1 := m.c_1 r
  flag := m.flag r
  pc := m.pc r
  is_external_op := m.is_external_op r
  op := m.op r
  m32 := m.m32 r
  ind_width := m.ind_width r
  set_pc := m.set_pc r
  jmp_offset1 := m.jmp_offset1 r
  jmp_offset2 := m.jmp_offset2 r
  store_pc := m.store_pc r
  im_high_degree_2 := m.im_high_degree_2 r
  segment_l1 := m.segment_l1 r

@[reducible]
def validOfRow (row : MainRow FGL) :
    ZiskFv.Airs.Main.Valid_Main FGL FGL where
  a_0 := fun _ => row.a_0
  a_1 := fun _ => row.a_1
  b_0 := fun _ => row.b_0
  b_1 := fun _ => row.b_1
  c_0 := fun _ => row.c_0
  c_1 := fun _ => row.c_1
  flag := fun _ => row.flag
  pc := fun _ => row.pc
  is_external_op := fun _ => row.is_external_op
  op := fun _ => row.op
  m32 := fun _ => row.m32
  ind_width := fun _ => row.ind_width
  set_pc := fun _ => row.set_pc
  jmp_offset1 := fun _ => row.jmp_offset1
  jmp_offset2 := fun _ => row.jmp_offset2
  store_pc := fun _ => row.store_pc
  im_high_degree_2 := fun _ => row.im_high_degree_2
  segment_l1 := fun _ => row.segment_l1

theorem rowAt_validOfRow_zero (row : MainRow FGL) :
    rowAt (validOfRow row) 0 = row := by
  cases row
  rfl

/-- The 9 F-typed per-row Main constraints at row `r`, expressed
    against a `Valid_Main`. -/
def constraints_at (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r : ℕ) : Prop :=
  m.flag r * (1 - m.flag r) = 0
  ∧ m.is_external_op r * (1 - m.is_external_op r) = 0
  ∧ (1 - m.is_external_op r) * (1 - m.op r) * m.c_0 r = 0
  ∧ (1 - m.is_external_op r) * (1 - m.op r) * m.c_1 r = 0
  ∧ (1 - m.is_external_op r) * m.op r * (m.b_0 r - m.c_0 r) = 0
  ∧ (1 - m.is_external_op r) * m.op r * (m.b_1 r - m.c_1 r) = 0
  ∧ (1 - m.is_external_op r) * (1 - m.op r) * (1 - m.flag r) = 0
  ∧ (1 - m.is_external_op r) * m.op r * m.flag r = 0
  ∧ m.flag r * m.set_pc r = 0

theorem spec_of_valid
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt m r))
    (h_constraints : constraints_at m r) :
    Spec (rowAt m r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h_constraints
  exact soundness (rowAt m r) h_assumptions h1 h2 h3 h4 h5 h6 h7 h8 h9

/-- Main's operation-bus message without multiplicity, as a concrete row
    value. Clean carries multiplicity on the interaction, while the legacy
    `OperationBusEntry` carries it in the record. -/
@[reducible]
def opBusMessage (row : MainRow FGL) : OpBusMessage FGL :=
  { op := row.op
    a_lo := row.a_0
    a_hi := (1 - row.m32) * row.a_1
    b_lo := row.b_0
    b_hi := (1 - row.m32) * row.b_1
    c_lo := row.c_0
    c_hi := row.c_1
    flag := row.flag
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

theorem opBusMessage_toEntry_rowAt_eq_opBus_row
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r : ℕ) :
    OpBusMessage.toEntry (opBusMessage (rowAt m r)) (m.is_external_op r) =
      ZiskFv.Airs.OperationBus.opBus_row_Main m r := by
  rfl

theorem eval_opBusMessageExpr
    (env : Environment FGL) (row : Var MainRow FGL) :
    eval env (opBusMessageExpr row) = opBusMessage (eval env row) := by
  rw [OpBusMessage.mk.injEq]
  simp only [opBusMessageExpr, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field, Expression.eval]
  repeat constructor <;> try ring_nf <;> trivial

/-! ## T4 memory-bus message adapters

Concrete counterparts for Main's three PIL memory-bus messages. These are
not legacy `MemoryBusEntry`s: they retain the PIL tuple shape
`[mem_op, ptr, timestamp, width, value_0, value_1]`. The legacy
address-space and multiplicity slots are supplied later by
`MemBusMessage.toEntry`.
-/

@[reducible]
def aMemMessage (row : MainRowWithRom FGL) : MemBusMessage FGL :=
  { mem_op := row.rom.a_src_mem + 3 * row.rom.a_src_reg
    ptr := row.rom.addr0
    timestamp := 1 + row.rom.main_step * 4
    width := 8
    value_0 := row.core.a_0
    value_1 := row.core.a_1 }

@[reducible]
def bMemMessage (row : MainRowWithRom FGL) : MemBusMessage FGL :=
  { mem_op := (row.rom.b_src_mem + row.rom.b_src_ind)
      + 3 * row.rom.b_src_reg
    ptr := row.rom.addr1
    timestamp := 2 + row.rom.main_step * 4
    width := row.rom.b_src_ind * (row.core.ind_width - 8) + 8
    value_0 := row.core.b_0
    value_1 := row.core.b_1 }

@[reducible]
def cMemMessage (row : MainRowWithRom FGL) : MemBusMessage FGL :=
  { mem_op := 2 * (row.rom.store_mem + row.rom.store_ind)
      + 3 * row.rom.store_reg
    ptr := row.rom.addr2
    timestamp := 3 + row.rom.main_step * 4
    width := row.rom.store_ind * (row.core.ind_width - 8) + 8
    value_0 := row.core.store_pc *
        (row.core.pc + row.core.jmp_offset2 - row.core.c_0) + row.core.c_0
    value_1 := (1 - row.core.store_pc) * row.core.c_1 }

theorem eval_aMemMessageExpr
    (env : Environment FGL) (row : Var MainRowWithRom FGL) :
    eval env (aMemMessageExpr row) = aMemMessage (eval env row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [aMemMessageExpr, aMemOpExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor <;> simp

theorem eval_bMemMessageExpr
    (env : Environment FGL) (row : Var MainRowWithRom FGL) :
    eval env (bMemMessageExpr row) = bMemMessage (eval env row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [bMemMessageExpr, bMemOpExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor <;> simp <;> ring_nf

theorem eval_cMemMessageExpr
    (env : Environment FGL) (row : Var MainRowWithRom FGL) :
    eval env (cMemMessageExpr row) = cMemMessage (eval env row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [cMemMessageExpr, cMemOpExpr,
    storeValueLoExpr, storeValueHiExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor <;> simp <;> ring_nf

/-! ### Legacy lane facts from PIL-shaped Main memory messages -/

theorem bMemMessage_toEntry_load_emit
    (row : MainRowWithRom FGL) :
    (validOfRow row.core).b_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo
          (MemBusMessage.toEntry (bMemMessage row) (-1) 2)
    ∧ (validOfRow row.core).b_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi
          (MemBusMessage.toEntry (bMemMessage row) (-1) 2)
    ∧ (MemBusMessage.toEntry (bMemMessage row) (-1) 2).as = 2
    ∧ (MemBusMessage.toEntry (bMemMessage row) (-1) 2).multiplicity = -1 := by
  simp

theorem bMemMessage_toEntry_memory_load_lanes_match
    (row : MainRowWithRom FGL) :
    ZiskFv.Airs.MemoryBus.memory_load_lanes_match
      (validOfRow row.core) 0
      (MemBusMessage.toEntry (bMemMessage row) (-1) 2) := by
  exact ⟨(bMemMessage_toEntry_load_emit row).1,
    (bMemMessage_toEntry_load_emit row).2.1⟩

theorem cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
    (row : MainRowWithRom FGL)
    (h_store_pc : row.core.store_pc = 0) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match
      (validOfRow row.core) 0
      (MemBusMessage.toEntry (cMemMessage row) 1 1) := by
  simp [h_store_pc]

/-- Main external-arithmetic rd-write lane adapter for a concrete Clean
    Main row.

This is the lane portion of the legacy
`MemBridge.main_external_arith_emission_bundle`, but it is derived from
Main's real PIL-shaped `c` memory message. The `store_pc = 0` premise is
kept explicit: arithmetic rows write the computed `c_0/c_1` value to
`rd`, while `store_pc = 1` rows use the PC-write formula. -/
theorem external_arith_register_write_lanes_of_message
    (row : MainRowWithRom FGL)
    (h_store_pc : row.core.store_pc = 0) :
    (validOfRow row.core).c_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo
          (MemBusMessage.toEntry (cMemMessage row) 1 1)
    ∧ (validOfRow row.core).c_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi
          (MemBusMessage.toEntry (cMemMessage row) 1 1) := by
  exact cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
    row h_store_pc

/-- External-arithmetic rd-write lane adapter for an arbitrary legacy
    entry matched to the concrete Clean Main `c` message. -/
theorem external_arith_register_write_lanes_of_message_match
    (row : MainRowWithRom FGL)
    (e : Interaction.MemoryBusEntry FGL)
    (h_store_pc : row.core.store_pc = 0)
    (h_e_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e
        (MemBusMessage.toEntry (cMemMessage row) 1 1)) :
    (validOfRow row.core).c_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo e
    ∧ (validOfRow row.core).c_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi e := by
  obtain ⟨_h_mult, _h_as, _h_ptr, h_v0, h_v1, _h_ts⟩ := h_e_match
  constructor
  · simpa [validOfRow, ZiskFv.Airs.MemoryBus.memory_entry_lo,
      cMemMessage, MemBusMessage.toEntry, h_store_pc] using h_v0.symm
  · simpa [validOfRow, ZiskFv.Airs.MemoryBus.memory_entry_hi,
      cMemMessage, MemBusMessage.toEntry, h_store_pc] using h_v1.symm

/-- Variant of `external_arith_register_write_lanes_of_message_match`
    projected back to an existing `Valid_Main` row. -/
theorem external_arith_register_write_lanes_of_message_match_valid
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (row : MainRowWithRom FGL)
    (e : Interaction.MemoryBusEntry FGL)
    (h_row : row.core = rowAt main r_main)
    (h_store_pc : row.core.store_pc = 0)
    (h_e_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e
        (MemBusMessage.toEntry (cMemMessage row) 1 1)) :
    main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e
    ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e := by
  have h_raw :=
    external_arith_register_write_lanes_of_message_match row e
      h_store_pc h_e_match
  rw [h_row] at h_raw
  simpa [validOfRow, rowAt] using h_raw

/-- Store-PC rd-write lane adapter for an arbitrary legacy entry matched to
Main's real PIL-shaped `c` memory message.

This is the lane portion of the legacy
`MemBridge.main_store_pc_emission_bundle`, derived directly from the Clean
`cMemMessage` formula
`[store_pc * (pc + jmp_offset2 - c_0) + c_0, (1 - store_pc) * c_1]`. -/
theorem store_pc_lanes_of_message_match_valid
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (row : MainRowWithRom FGL)
    (e : Interaction.MemoryBusEntry FGL)
    (h_row : row.core = rowAt main r_main)
    (h_e_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e
        (MemBusMessage.toEntry (cMemMessage row) 1 1)) :
    ZiskFv.Airs.MemoryBus.store_pc_lanes_match_lo main r_main e
    ∧ ZiskFv.Airs.MemoryBus.store_pc_lanes_match_hi main r_main e := by
  obtain ⟨_h_mult, _h_as, _h_ptr, h_v0, h_v1, _h_ts⟩ := h_e_match
  constructor
  · simp only [ZiskFv.Airs.MemoryBus.store_pc_lanes_match_lo,
      ZiskFv.Airs.MemoryBus.memory_entry_lo]
    rw [h_v0]
    simp [h_row, rowAt]
  · simp only [ZiskFv.Airs.MemoryBus.store_pc_lanes_match_hi,
      ZiskFv.Airs.MemoryBus.memory_entry_hi]
    rw [h_v1]
    simp [h_row, rowAt]

theorem cMemMessage_toEntry_memory_store_lanes_match_of_store_pc_zero
    (row : MainRowWithRom FGL)
    (h_store_pc : row.core.store_pc = 0) :
    ZiskFv.Airs.MemoryBus.memory_store_lanes_match
      (validOfRow row.core) 0
      (MemBusMessage.toEntry (cMemMessage row) 1 2) := by
  simp [h_store_pc]

theorem internal_op1_copies_b0_of_spec_validOfRow
    (row : MainRow FGL) (h_spec : Spec row) :
    ZiskFv.Airs.Main.internal_op1_copies_b0 (validOfRow row) 0 := by
  exact h_spec.2.2.2.2.1

theorem internal_op1_copies_b1_of_spec_validOfRow
    (row : MainRow FGL) (h_spec : Spec row) :
    ZiskFv.Airs.Main.internal_op1_copies_b1 (validOfRow row) 0 := by
  exact h_spec.2.2.2.2.2.1

/-- Structural replacement for the lane/copy portion of
    `MemBridge.main_load_emission_bundle`, stated over a concrete Clean
    Main row and its PIL-shaped b/c memory messages.

This deliberately excludes ptr/rd routing: those require ROM/transpile
pins and remain a separate adapter step. -/
theorem load_emission_lane_copy_bundle_of_messages
    (row : MainRowWithRom FGL)
    (h_spec : Spec row.core)
    (h_store_pc : row.core.store_pc = 0) :
    (validOfRow row.core).b_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo
          (MemBusMessage.toEntry (bMemMessage row) (-1) 2)
    ∧ (validOfRow row.core).b_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi
          (MemBusMessage.toEntry (bMemMessage row) (-1) 2)
    ∧ (MemBusMessage.toEntry (bMemMessage row) (-1) 2).as = 2
    ∧ (MemBusMessage.toEntry (bMemMessage row) (-1) 2).multiplicity = -1
    ∧ (validOfRow row.core).c_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo
          (MemBusMessage.toEntry (cMemMessage row) 1 1)
    ∧ (validOfRow row.core).c_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi
          (MemBusMessage.toEntry (cMemMessage row) 1 1)
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 (validOfRow row.core) 0
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 (validOfRow row.core) 0 := by
  have h_b := bMemMessage_toEntry_load_emit row
  have h_c := cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
    row h_store_pc
  exact ⟨h_b.1, h_b.2.1, h_b.2.2.1, h_b.2.2.2, h_c.1, h_c.2,
    internal_op1_copies_b0_of_spec_validOfRow row.core h_spec,
    internal_op1_copies_b1_of_spec_validOfRow row.core h_spec⟩

/-- Structural ptr/rd-routing adapter for Main load rows.

The premises are the ROM/transpile pins that the old
`MemBridge.main_load_emission_bundle` packaged together with lane facts:
`addr1` is the memory-read address, and `addr2` is the register-write
destination tag. Keeping these pins explicit prevents the Clean
PIL-shaped memory interaction from being silently identified with a legacy
architectural row. -/
theorem load_ptr_rd_bundle_of_message_pins
    (row : MainRowWithRom FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_addr1 :
      row.rom.addr1.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx row.rom.addr2 = 0 ↔ rd = 0)
    (h_addr2_idx :
      rd.toNat = (Transpiler.wrap_to_regidx row.rom.addr2).val) :
    (MemBusMessage.toEntry (bMemMessage row) (-1) 2).ptr.toNat =
        r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx
          (MemBusMessage.toEntry (cMemMessage row) 1 1).ptr = 0 ↔ rd = 0)
    ∧ rd.toNat =
        (Transpiler.wrap_to_regidx
          (MemBusMessage.toEntry (cMemMessage row) 1 1).ptr).val := by
  simpa [bMemMessage, cMemMessage, MemBusMessage.toEntry]
    using And.intro h_addr1 (And.intro h_addr2_zero_iff h_addr2_idx)

/-- Load-side structural adapter matching the full shape of the legacy
`main_load_emission_bundle`, but stated for a concrete Clean Main row and
its PIL memory messages.

This is still a local adapter theorem, not a canonical-opcode discharge:
callers must supply the structural ROM/transpile pins explicitly. -/
theorem load_emission_bundle_of_message_pins
    (row : MainRowWithRom FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_spec : Spec row.core)
    (h_store_pc : row.core.store_pc = 0)
    (h_addr1 :
      row.rom.addr1.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx row.rom.addr2 = 0 ↔ rd = 0)
    (h_addr2_idx :
      rd.toNat = (Transpiler.wrap_to_regidx row.rom.addr2).val) :
    (validOfRow row.core).b_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo
          (MemBusMessage.toEntry (bMemMessage row) (-1) 2)
    ∧ (validOfRow row.core).b_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi
          (MemBusMessage.toEntry (bMemMessage row) (-1) 2)
    ∧ (MemBusMessage.toEntry (bMemMessage row) (-1) 2).as = 2
    ∧ (MemBusMessage.toEntry (bMemMessage row) (-1) 2).multiplicity = -1
    ∧ (validOfRow row.core).c_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo
          (MemBusMessage.toEntry (cMemMessage row) 1 1)
    ∧ (validOfRow row.core).c_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi
          (MemBusMessage.toEntry (cMemMessage row) 1 1)
    ∧ (MemBusMessage.toEntry (bMemMessage row) (-1) 2).ptr.toNat =
        r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx
          (MemBusMessage.toEntry (cMemMessage row) 1 1).ptr = 0 ↔ rd = 0)
    ∧ rd.toNat =
        (Transpiler.wrap_to_regidx
          (MemBusMessage.toEntry (cMemMessage row) 1 1).ptr).val
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 (validOfRow row.core) 0
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 (validOfRow row.core) 0 := by
  obtain ⟨h_b0, h_b1, h_b_as, h_b_mult, h_c0, h_c1, h_copy0, h_copy1⟩ :=
    load_emission_lane_copy_bundle_of_messages row h_spec h_store_pc
  obtain ⟨h_ptr, h_rd_zero, h_rd_idx⟩ :=
    load_ptr_rd_bundle_of_message_pins row r1_val imm rd
      h_addr1 h_addr2_zero_iff h_addr2_idx
  exact ⟨h_b0, h_b1, h_b_as, h_b_mult, h_c0, h_c1,
    h_ptr, h_rd_zero, h_rd_idx, h_copy0, h_copy1⟩

/-- Load-side structural adapter for arbitrary legacy entries matched to
the concrete Clean Main b/c messages.

Clean balance gives equality of PIL-shaped messages; the bridge in
`Airs.MemoryBus.matches_memory_entry_of_eval_msg_eq` turns that into
`matches_memory_entry` for legacy entries after the multiplicity/address
space are supplied. This theorem is the final projection from those
matched entries to the legacy bundle shape consumed by load proofs. -/
theorem load_emission_bundle_of_message_matches
    (row : MainRowWithRom FGL)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_spec : Spec row.core)
    (h_store_pc : row.core.store_pc = 0)
    (h_e1_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e1
        (MemBusMessage.toEntry (bMemMessage row) (-1) 2))
    (h_e2_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e2
        (MemBusMessage.toEntry (cMemMessage row) 1 1))
    (h_addr1 :
      row.rom.addr1.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx row.rom.addr2 = 0 ↔ rd = 0)
    (h_addr2_idx :
      rd.toNat = (Transpiler.wrap_to_regidx row.rom.addr2).val) :
    (validOfRow row.core).b_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo e1
    ∧ (validOfRow row.core).b_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi e1
    ∧ e1.as = 2
    ∧ e1.multiplicity = -1
    ∧ (validOfRow row.core).c_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo e2
    ∧ (validOfRow row.core).c_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi e2
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 (validOfRow row.core) 0
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 (validOfRow row.core) 0 := by
  obtain ⟨h1_mult, h1_as, h1_ptr, h1_v0, h1_v1, _h1_ts⟩ := h_e1_match
  obtain ⟨_h2_mult, _h2_as, h2_ptr, h2_v0, h2_v1, _h2_ts⟩ := h_e2_match
  have h_raw :=
    load_emission_bundle_of_message_pins row r1_val imm rd h_spec h_store_pc
      h_addr1 h_addr2_zero_iff h_addr2_idx
  obtain ⟨_hb0, _hb1, _hb_as, _hb_mult, _hc0, _hc1,
          _hptr, _hrd0, _hrdidx, hcopy0, hcopy1⟩ := h_raw
  have hb0 :
      (validOfRow row.core).b_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo e1 := by
    simpa [validOfRow, ZiskFv.Airs.MemoryBus.memory_entry_lo,
      bMemMessage, MemBusMessage.toEntry] using h1_v0.symm
  have hb1 :
      (validOfRow row.core).b_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi e1 := by
    simpa [validOfRow, ZiskFv.Airs.MemoryBus.memory_entry_hi,
      bMemMessage, MemBusMessage.toEntry] using h1_v1.symm
  have hc0 :
      (validOfRow row.core).c_0 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_lo e2 := by
    simpa [validOfRow, ZiskFv.Airs.MemoryBus.memory_entry_lo,
      cMemMessage, MemBusMessage.toEntry, h_store_pc] using h2_v0.symm
  have hc1 :
      (validOfRow row.core).c_1 0 =
        ZiskFv.Airs.MemoryBus.memory_entry_hi e2 := by
    simpa [validOfRow, ZiskFv.Airs.MemoryBus.memory_entry_hi,
      cMemMessage, MemBusMessage.toEntry, h_store_pc] using h2_v1.symm
  have hptr :
      e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [h1_ptr]
    simpa [bMemMessage, MemBusMessage.toEntry] using h_addr1
  have hrd0 :
      Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0 := by
    rw [h2_ptr]
    simpa [cMemMessage, MemBusMessage.toEntry] using h_addr2_zero_iff
  have hrdidx :
      rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val := by
    rw [h2_ptr]
    simpa [cMemMessage, MemBusMessage.toEntry] using h_addr2_idx
  exact ⟨hb0, hb1, h1_as, h1_mult, hc0, hc1, hptr, hrd0, hrdidx,
    hcopy0, hcopy1⟩

/-- Variant of `load_emission_bundle_of_message_matches` projected back to
an existing `Valid_Main` row.

This is the shape needed by opcode proofs: the Clean row supplies the
PIL-shaped messages and ROM fields, while `h_row` ties its core columns
to the already-existing `main, r_main` validator/index pair. -/
theorem load_emission_bundle_of_message_matches_valid
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (row : MainRowWithRom FGL)
    (e1 e2 : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_row : row.core = rowAt main r_main)
    (h_spec : Spec row.core)
    (h_store_pc : row.core.store_pc = 0)
    (h_e1_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e1
        (MemBusMessage.toEntry (bMemMessage row) (-1) 2))
    (h_e2_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e2
        (MemBusMessage.toEntry (cMemMessage row) 1 1))
    (h_addr1 :
      row.rom.addr1.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx row.rom.addr2 = 0 ↔ rd = 0)
    (h_addr2_idx :
      rd.toNat = (Transpiler.wrap_to_regidx row.rom.addr2).val) :
    main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
    ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
    ∧ e1.as = 2
    ∧ e1.multiplicity = -1
    ∧ main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
    ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main := by
  have h_raw :=
    load_emission_bundle_of_message_matches row e1 e2 r1_val imm rd
      h_spec h_store_pc h_e1_match h_e2_match
      h_addr1 h_addr2_zero_iff h_addr2_idx
  rw [h_row] at h_raw
  simpa [validOfRow, rowAt,
    ZiskFv.Airs.Main.internal_op1_copies_b0,
    ZiskFv.Airs.Main.internal_op1_copies_b1] using h_raw

/-- Structural replacement for the Main lane portion of the store-emission
    bundles (`SD` and the subword stores). Byte extraction and RMW
    high-byte preservation remain separate provider/byte-range adapter work. -/
theorem store_emission_lane_bundle_of_message
    (row : MainRowWithRom FGL)
    (h_store_pc : row.core.store_pc = 0) :
    ZiskFv.Airs.MemoryBus.memory_store_lanes_match
      (validOfRow row.core) 0
      (MemBusMessage.toEntry (cMemMessage row) 1 2)
    ∧ (MemBusMessage.toEntry (cMemMessage row) 1 2).as = 2
    ∧ (MemBusMessage.toEntry (cMemMessage row) 1 2).multiplicity = 1 := by
  exact ⟨cMemMessage_toEntry_memory_store_lanes_match_of_store_pc_zero
      row h_store_pc, rfl, rfl⟩

/-- Structural store-address adapter for Main store rows.

The explicit `addr2` pin is the store-side analogue of the load
`addr1` pin: it is the ROM/transpile fact connecting the PIL memory
message address to Sail's `rs1 + signExt(imm)` address. -/
theorem store_ptr_of_message_pin
    (row : MainRowWithRom FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    (h_addr2 :
      row.rom.addr2.toNat = (r1_val + BitVec.signExtend 64 imm).toNat) :
    (MemBusMessage.toEntry (cMemMessage row) 1 2).ptr.toNat =
      (r1_val + BitVec.signExtend 64 imm).toNat := by
  simpa [cMemMessage, MemBusMessage.toEntry] using h_addr2

/-- Main store lane/address adapter for a concrete Clean Main row.

Byte extraction for `SD` and high-byte RMW preservation for subword stores
remain outside this theorem; this only replaces the shared lane and ptr
portion of the legacy store-emission bundles. -/
theorem store_emission_lane_ptr_bundle_of_message_pin
    (row : MainRowWithRom FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    (h_store_pc : row.core.store_pc = 0)
    (h_addr2 :
      row.rom.addr2.toNat = (r1_val + BitVec.signExtend 64 imm).toNat) :
    ZiskFv.Airs.MemoryBus.memory_store_lanes_match
      (validOfRow row.core) 0
      (MemBusMessage.toEntry (cMemMessage row) 1 2)
    ∧ (MemBusMessage.toEntry (cMemMessage row) 1 2).as = 2
    ∧ (MemBusMessage.toEntry (cMemMessage row) 1 2).multiplicity = 1
    ∧ (MemBusMessage.toEntry (cMemMessage row) 1 2).ptr.toNat =
      (r1_val + BitVec.signExtend 64 imm).toNat := by
  obtain ⟨h_lanes, h_as, h_mult⟩ :=
    store_emission_lane_bundle_of_message row h_store_pc
  exact ⟨h_lanes, h_as, h_mult,
    store_ptr_of_message_pin row r1_val imm h_addr2⟩

/-- Store-side structural adapter for an arbitrary legacy entry matched to
the concrete Clean Main c/store message. -/
theorem store_emission_lane_ptr_bundle_of_message_match
    (row : MainRowWithRom FGL)
    (e : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    (h_store_pc : row.core.store_pc = 0)
    (h_e_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e
        (MemBusMessage.toEntry (cMemMessage row) 1 2))
    (h_addr2 :
      row.rom.addr2.toNat = (r1_val + BitVec.signExtend 64 imm).toNat) :
    ZiskFv.Airs.MemoryBus.memory_store_lanes_match
      (validOfRow row.core) 0 e
    ∧ e.as = 2
    ∧ e.multiplicity = 1
    ∧ e.ptr.toNat = (r1_val + BitVec.signExtend 64 imm).toNat := by
  obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, _h_ts⟩ := h_e_match
  have h_lanes :
      ZiskFv.Airs.MemoryBus.memory_store_lanes_match
        (validOfRow row.core) 0 e := by
    constructor
    · simpa [validOfRow, ZiskFv.Airs.MemoryBus.memory_entry_lo,
        cMemMessage, MemBusMessage.toEntry, h_store_pc] using h_v0.symm
    · simpa [validOfRow, ZiskFv.Airs.MemoryBus.memory_entry_hi,
        cMemMessage, MemBusMessage.toEntry, h_store_pc] using h_v1.symm
  have h_ptr_nat :
      e.ptr.toNat = (r1_val + BitVec.signExtend 64 imm).toNat := by
    rw [h_ptr]
    simpa [cMemMessage, MemBusMessage.toEntry] using h_addr2
  exact ⟨h_lanes, h_as, h_mult, h_ptr_nat⟩

/-- Variant of `store_emission_lane_ptr_bundle_of_message_match` projected
back to an existing `Valid_Main` row. -/
theorem store_emission_lane_ptr_bundle_of_message_match_valid
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (row : MainRowWithRom FGL)
    (e : Interaction.MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    (h_row : row.core = rowAt main r_main)
    (h_store_pc : row.core.store_pc = 0)
    (h_e_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e
        (MemBusMessage.toEntry (cMemMessage row) 1 2))
    (h_addr2 :
      row.rom.addr2.toNat = (r1_val + BitVec.signExtend 64 imm).toNat) :
    ZiskFv.Airs.MemoryBus.memory_store_lanes_match main r_main e
    ∧ e.as = 2
    ∧ e.multiplicity = 1
    ∧ e.ptr.toNat = (r1_val + BitVec.signExtend 64 imm).toNat := by
  have h_raw :=
    store_emission_lane_ptr_bundle_of_message_match row e r1_val imm
      h_store_pc h_e_match h_addr2
  rw [h_row] at h_raw
  simpa [validOfRow, rowAt,
    ZiskFv.Airs.MemoryBus.memory_store_lanes_match] using h_raw

end ZiskFv.AirsClean.Main
