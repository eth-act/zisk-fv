import Extraction.SourceDimensions
import ZiskFv.AirsClean.MemAlignWriteByte.ExtractedWiring
import ZiskFv.AirsClean.MemAlignWriteByte.Direct

/-! Source segment construction: `mem_align_byte_sm.rs:284-296,327-374`.
The populated rows are the rows actually produced by the nested input loops;
unused physical rows are filled with the computed zero STORE row. Direct
messages are emitted once per segment with the physical unused-row count.
This local operational model does not assert an AcceptedTrace embedding. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte
open Goldilocks
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

/-- Capacity comes only from pilout metadata, not a hand-copied exponent. -/
def physicalRowCount : ℕ := Extraction.SourceDimensions.MemAlignWriteByte.rowCount

def paddingRow : MemAlignWriteByteRow FGL :=
  rowOf false false false 0 0 0 0 0 0 0

structure Segment where
  populated : List (MemAlignWriteByteRow FGL)
  fits : populated.length ≤ physicalRowCount

def Segment.paddingCount (s : Segment) : ℕ := physicalRowCount - s.populated.length

def Segment.paddingSize (s : Segment) : FGL := (s.paddingCount : FGL)

def Segment.physicalRows (s : Segment) : List (MemAlignWriteByteRow FGL) :=
  s.populated ++ List.replicate s.paddingCount paddingRow

theorem Segment.physicalRows_length (s : Segment) :
    s.physicalRows.length = physicalRowCount := by
  simp only [Segment.physicalRows, List.length_append, List.length_replicate,
    Segment.paddingCount]
  have h := s.fits
  omega

theorem Segment.paddingSize_source_count (s : Segment) :
    s.paddingSize = ((s.physicalRows.length - s.populated.length : ℕ) : FGL) := by
  rw [s.physicalRows_length]
  rfl

/-- Honest construction specializes, but does not restrict, the actual raw
source-scalar Direct interface. -/
def Segment.directInteractions (s : Segment) : List (ChannelInteraction MemBusChannel) :=
  MemAlignWriteByte.directInteractions s.paddingSize

def Segment.directMain (s : Segment) : Circuit FGL Unit :=
  MemAlignWriteByte.directMain s.paddingSize

theorem Segment.directMain_operations (s : Segment) (offset : ℕ) :
    s.directMain.operations offset =
      s.directInteractions.map (fun interaction => Operation.interact interaction.toRaw) := rfl

/-- The segment runs the real local row circuit for every physical row and then
emits exactly the three once-per-segment weighted source Direct operations. -/
def Segment.main (s : Segment) : Circuit FGL Unit := do
  for row in s.physicalRows do
    MemAlignWriteByte.main (ProvableType.const row)
  s.directMain

theorem paddingRow_spec : Spec paddingRow := by
  norm_num [Spec, PolynomialSpec, RangeSpec, paddingRow, rowOf, composedValueOf,
    boolF, MemAlignByte.byte_value_factor, MemAlignByte.value_8b_factor,
    MemAlignByte.value_16b_factor]

/-- Exact source padding row messages before weighting. -/
theorem paddingRow_messages (env : Environment FGL) :
    ProvableType.eval env (memReadMessageExpr (ProvableType.const paddingRow)) =
      ProvableType.eval env paddingLoadMessage ∧
    ProvableType.eval env (memWriteMessageExpr (ProvableType.const paddingRow)) =
      ProvableType.eval env paddingAlignedStoreMessage ∧
    ProvableType.eval env (memBusMessageExpr (ProvableType.const paddingRow)) =
      ProvableType.eval env paddingSelectedStoreMessage := by
  have h_row := ProvableType.eval_const (env := env) (x := paddingRow)
  have h4 := congrArg MemAlignWriteByteRow.sel_high_4b h_row
  have h2 := congrArg MemAlignWriteByteRow.sel_high_2b h_row
  have h1 := congrArg MemAlignWriteByteRow.sel_high_b h_row
  have hd := congrArg MemAlignWriteByteRow.direct_value h_row
  have hc := congrArg MemAlignWriteByteRow.composed_value h_row
  have hw := congrArg MemAlignWriteByteRow.written_byte_value h_row
  have ha := congrArg MemAlignWriteByteRow.addr_w h_row
  have hs := congrArg MemAlignWriteByteRow.step h_row
  have hm0 := congrArg MemAlignWriteByteRow.mem_write_values_0 h_row
  have hm1 := congrArg MemAlignWriteByteRow.mem_write_values_1 h_row
  simp only [circuit_norm] at h4 h2 h1 hd hc hw ha hs hm0 hm1
  simp only [← CircuitType.eval_expression]
  simp only [circuit_norm, memReadMessageExpr, memWriteMessageExpr, memBusMessageExpr,
    paddingLoadMessage, paddingAlignedStoreMessage, paddingSelectedStoreMessage,
    h4, h2, h1, hd, hc, hw, ha, hs, hm0, hm1]
  simp [paddingRow, rowOf, composedValueOf, boolF, MemAlignByte.byte_value_factor,
    MemAlignByte.value_8b_factor, MemAlignByte.value_16b_factor]

/-- The same three typed memory operations exposed by the live row component,
specialized to the source zero padding row. -/
def paddingRowInteractions : List (ChannelInteraction MemBusChannel) :=
  [ MemBusChannel.pulled (memReadMessageExpr (ProvableType.const paddingRow))
  , MemBusChannel.pulled (memWriteMessageExpr (ProvableType.const paddingRow))
  , MemBusChannel.pushed (memBusMessageExpr (ProvableType.const paddingRow)) ]


/-- The three actual weighted Direct emissions negate exactly the source
padding-row memory roster, including the STORE step+1 and selected-byte signs. -/
theorem Segment.direct_coefficients (s : Segment) (env : Environment FGL)
    (message : MemBusMessage FGL) :
    memoryCoefficient env message s.directInteractions =
      -s.paddingSize * memoryCoefficient env message paddingRowInteractions := by
  classical
  obtain ⟨hload, hstore, hbyte⟩ := paddingRow_messages env
  simp only [memoryCoefficient, Segment.directInteractions,
    MemAlignWriteByte.directInteractions, paddingRowInteractions,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Channel.emitted, emitted, Channel.pulled, pulled, Channel.pushed, pushed,
    hload, hstore, hbyte]
  simp only [circuit_norm]
  split_ifs <;> ring

/-- Cancellation is pointwise for every concrete memory message, not merely a
sum of unrelated scalar selectors. The positive/negative terms are the actual
source-linked row and Direct rosters with the actual physical padding count. -/
theorem Segment.padding_coefficients_cancel (s : Segment) (env : Environment FGL)
    (message : MemBusMessage FGL) :
    memoryCoefficient env message
      ((List.replicate s.paddingCount paddingRowInteractions).flatten ++
        s.directInteractions) = 0 := by
  rw [memoryCoefficient_append, memoryCoefficient_replicate, s.direct_coefficients]
  change (s.paddingSize * memoryCoefficient env message paddingRowInteractions) +
    -s.paddingSize * memoryCoefficient env message paddingRowInteractions = 0
  ring

end ZiskFv.AirsClean.MemAlignWriteByte
