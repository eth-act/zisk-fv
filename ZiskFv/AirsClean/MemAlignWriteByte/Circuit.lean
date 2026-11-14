import ZiskFv.AirsClean.MemAlignWriteByte.Constraints
import ZiskFv.AirsClean.MemAlignWriteByte.Soundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

namespace ZiskFv.AirsClean.MemAlignWriteByte
open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.MemAlignByte (byte_value_factor value_8b_factor value_16b_factor)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.DualByte (DualByteChannel)

def composedValueOf (high2 high1 : Bool) (byte value8 value16 : FGL) : FGL :=
  byte * byte_value_factor (boolF high2) (boolF high1) +
  value8 * value_8b_factor (boolF high2) (boolF high1) +
  value16 * value_16b_factor (boolF high2)

/-- Every byte route is constructible; no selector or limb is silently fixed.
Only actual lookup bounds restrict the free operands in completeness. -/
def rowOf (high4 high2 high1 : Bool)
    (byte writtenByte direct value16 value8 addr step : FGL) : MemAlignWriteByteRow FGL :=
  let written := composedValueOf high2 high1 writtenByte value8 value16
  { sel_high_4b := boolF high4
    sel_high_2b := boolF high2
    sel_high_b := boolF high1
    direct_value := direct
    composed_value := composedValueOf high2 high1 byte value8 value16
    written_composed_value := written
    written_byte_value := writtenByte
    value_16b := value16
    value_8b := value8
    byte_value := byte
    addr_w := addr
    step := step
    mem_write_values_0 := boolF high4 * (direct - written) + written
    mem_write_values_1 := boolF high4 * (written - direct) + direct }

set_option maxHeartbeats 1000000 in
def circuit : GeneralFormalCircuit FGL MemAlignWriteByteRow unit where
  name := "MemAlignWriteByte"
  main := main
  elaborated :=
    { localLength _ := 0
      output _ _ := ()
      channelsWithGuarantees := [] }
  channelsWithRequirements := [MemBusChannel.toRaw, DualByteChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel
      [ MemBusChannel.pulled (memReadMessageExpr row)
      , MemBusChannel.pulled (memWriteMessageExpr row)
      , MemBusChannel.pushed (memBusMessageExpr row) ] ++
    expose DualByteChannel [DualByteChannel.pulled (dualByteMessageExpr row)]
  Assumptions := fun _ _ => True
  Spec := fun row _ _ => Spec row
  ProverAssumptions := fun row _ _ =>
    ∃ high4 high2 high1 byte writtenByte direct value16 value8 addr step,
      writtenByte.val < 256 ∧ value16.val < 65536 ∧
      byte.val < 256 ∧ value8.val < 256 ∧
      row = rowOf high4 high2 high1 byte writtenByte direct value16 value8 addr step
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · obtain ⟨hw, h16, hd, h0, h1, h2, hc, hwc, hm0, hm1, _⟩ := h_holds
      have hd' : input.byte_value.val < 256 ∧ input.value_8b.val < 256 := by
        simpa [Lookup.Soundness, Table.fromStatic, StaticTable.toTable,
          Table.toRaw, RangeTables.dualByteTable] using hd
      refine ⟨?_, hw, h16, hd'⟩
      simp only [PolynomialSpec, byte_value_factor, value_8b_factor, value_16b_factor]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · linear_combination h0
      · linear_combination h1
      · linear_combination h2
      · linear_combination hc
      · linear_combination hwc
      · linear_combination hm0
      · linear_combination hm1
    · intro _
      simp [MemBusChannel, DualByteChannel]
  completeness := by
    circuit_proof_start [MemBusChannel, DualByteChannel, Lookup.completeness_def]
    obtain ⟨high4, high2, high1, byte, writtenByte, direct, value16, value8,
      addr, step, hw, h16, hb, h8, hrow⟩ := h_assumptions
    injection hrow with hs4 hs2 hs1 hd hc hwc hwb hv16 hv8 hbv ha hstep hm0 hm1
    subst_vars
    simp [rowOf, composedValueOf, byte_value_factor, value_8b_factor,
      value_16b_factor] at h_input ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [RangeTables.rangeTable8, RangeTables.rangeStaticTable] using hw
    · simpa only [RangeTables.rangeTable16, RangeTables.rangeStaticTable] using h16
    · simpa [Lookup.Completeness, Table.fromStatic, StaticTable.toTable,
        Table.toRaw, RangeTables.dualByteTable, h_input] using And.intro hb h8
    all_goals ring

def component : Component FGL := { circuit }

theorem component_spec (env : Environment FGL) :
    component.Spec env = Spec (component.rowInput env) := rfl

theorem component_interactionsWith_memBus :
    component.operations.interactionsWith MemBusChannel.toRaw =
      [ (MemBusChannel.pulled (memReadMessageExpr component.rowInputVar)).toRaw
      , (MemBusChannel.pulled (memWriteMessageExpr component.rowInputVar)).toRaw
      , (MemBusChannel.pushed (memBusMessageExpr component.rowInputVar)).toRaw ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw, _⟩ ∈ component.exposedChannels
  simp only [component, circuit, Component.exposedChannels, expose,
    List.mem_append, List.mem_singleton, List.map_cons, List.map_nil]
  exact Or.inl rfl

theorem component_interactionsWith_dualByte :
    component.operations.interactionsWith DualByteChannel.toRaw =
      [(DualByteChannel.pulled (dualByteMessageExpr component.rowInputVar)).toRaw] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨DualByteChannel.toRaw, _⟩ ∈ component.exposedChannels
  simp only [component, circuit, Component.exposedChannels, expose,
    List.mem_append, List.mem_singleton, List.map_cons, List.map_nil]
  exact Or.inr rfl

set_option maxHeartbeats 1000000 in
/-- Derive the complete local Spec from actual compiled row operations. All
range facts come from the real static lookups, not additional caller promises. -/
theorem spec_of_main_constraints (offset : Nat) (env : Environment FGL)
    (row : Var MemAlignWriteByteRow FGL)
    (h_holds : ConstraintsHold.Soundness env ((main row).operations offset)) :
    Spec (eval env row) := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, circuit_norm] at hsound
  have h_constraints := h_holds
  simp only [main, circuit_norm] at h_constraints
  exact (hsound env row (eval env row) (by simp only [circuit_norm]) h_constraints).1

end ZiskFv.AirsClean.MemAlignWriteByte
