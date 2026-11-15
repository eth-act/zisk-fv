import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import ZiskFv.AirsClean.ZiskInstructionRom

/-!
# Committed instruction-ROM image provider

`rom.pil:7-25` has eleven public-root committed columns and one ordinary
witness column, `multiplicity`. Here `image` is a model parameter, not a
verified public-root opening. No opening certificate is requested or provided.
Relating it to the verifier's `rom_root`, actual final producer rows, and ELF
lowering are separate, unproved boundaries of this partial packet.

The image is materialized by the component, never supplied in raw witness
cells. The only raw cell is the multiplicity. Its sign in the lookup sum is
positive; PIL does not constrain its field value to be positive, boolean, or
nonzero. In particular this provider must not be replaced by a unit push.

`rom.rs:204-266` sorts original u64 instruction keys before field encoding and
then pads the committed image with zero rows. Neither an image row ordinal nor
the sorted order of field-valued `line` representatives determines that order.
The generic capacity parameter permits the source template's `N`; the dedicated
source module specializes to the compiled physical domain. No layout validator
is added to the AIR.
-/

namespace ZiskFv.AirsClean.ZiskInstructionRomProvider

open Goldilocks Air.Flat
open ZiskFv.Channels.ZiskRomBus
open ZiskFv.AirsClean.ZiskInstructionRom

structure RomRow (F : Type) where
  message : ZiskRomMessage F
  multiplicity : F
deriving ProvableStruct

@[circuit_norm]
def main (row : Var RomRow FGL) : Circuit FGL Unit := do
  ZiskRomBusChannel.emit row.multiplicity row.message

/-- There are no local polynomial gates in Rom before lookup lowering. Image
ownership is supplied by materialization, not by this circuit's `Spec`. -/
def circuit : GeneralFormalCircuit FGL RomRow unit where
  name := "CommittedInstructionRom7890"
  main := main
  channelsWithRequirements := [ZiskRomBusChannel.toRaw]
  exposedChannels row _ :=
    expose ZiskRomBusChannel [ZiskRomBusChannel.emitted row.multiplicity row.message]
  Assumptions := fun _ _ => True
  Spec := fun _ _ _ => True
  ProverAssumptions := fun _ _ _ => True
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    simp [ZiskRomBusChannel]
  completeness := by
    circuit_proof_start

private def imageLayout (slot : Fin 12) : Sum (Fin 1) (Fin 11) :=
  if h : slot.val < 11 then .inr ⟨slot.val, h⟩ else .inl ⟨0, by omega⟩

/-- The eleven values in exactly the `lookup_proves` source order. -/
def imageValues {capacity : Nat} (image : Program capacity)
    (slot : Fin 11) (row : Fin capacity) : FGL :=
  ![(image row).line, (image row).a_offset_imm0, (image row).a_imm1,
    (image row).b_offset_imm0, (image row).b_imm1, (image row).ind_width,
    (image row).op, (image row).store_offset, (image row).jmp_offset1,
    (image row).jmp_offset2, (image row).flags] slot

/-- These are committed-image data, not deterministic PIL fixed polynomials.
`IndexedFixedColumns` is only the Clean materialization mechanism. It does not
prove public commitment binding. -/
def imageColumns {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) : IndexedFixedColumns FGL 1 where
  capacity := capacity
  capacity_pos := positive
  effectiveWidth := 12
  fixedWidth := 11
  layout := imageLayout
  values := imageValues image

def component {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) : Component FGL :=
  { circuit, rawWidth := 1, fixedColumns := some (imageColumns positive image) }

theorem component_interactionsWith_rom {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) :
    (component positive image).operations.interactionsWith ZiskRomBusChannel.toRaw =
      [((ZiskRomBusChannel.emitted
        (component positive image).rowInputVar.multiplicity
        (component positive image).rowInputVar.message).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨ZiskRomBusChannel.toRaw, _⟩ ∈ (component positive image).exposedChannels
  simp only [component, circuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Constructibility and ownership at once: arbitrary raw data cannot change
any image column; a singleton raw array realizes any witness multiplicity. -/
theorem eval_materialize {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) (index : Fin capacity)
    (data : ProverData FGL) (raw : Array FGL) :
    Eval.eval
      (Environment.fromArray ((imageColumns positive image).materialize index.val raw) data)
      (varFromOffset (F := FGL) RomRow 0) =
      { message := image index, multiplicity := raw.getD 0 0 } := by
  rw [ProvableType.eval_varFromOffset, ProvableType.fromElements_eq_iff]
  rw [Vector.ext_iff]
  intro slot in_range
  have small : slot < 12 := by
    simpa only [explicit_provable_type, ProvableType.size] using in_range
  interval_cases slot <;>
    simp [Vector.getElem_mapRange, explicit_provable_type,
      ProvableStruct.combinedSize, ProvableStruct.components, ProvableStruct.toComponents,
      ProvableStruct.componentsToElements, instProvableStructRomRow,
      instProvableStructZiskRomMessage, IndexedFixedColumns.materialize,
      Array.getElem?_ofFn, IndexedFixedColumns.fixedAt, imageColumns,
      imageLayout, imageValues, Nat.mod_eq_of_lt index.isLt, ProvableType.size] <;> rfl

/-- Exact membership is a consequence of materialized image ownership, with
no caller-supplied table membership or validity premise. -/
theorem materialized_member {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) (index : Fin capacity)
    (data : ProverData FGL) (raw : Array FGL) :
    (romStaticTable capacity image).Spec
      (Eval.eval
        (Environment.fromArray ((imageColumns positive image).materialize index.val raw) data)
        (varFromOffset (F := FGL) RomRow 0)).message := by
  rw [eval_materialize]
  exact ⟨index, rfl⟩

/-- Kernel constructibility for every source-permitted multiplicity. -/
theorem materialize_witness {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) (index : Fin capacity)
    (data : ProverData FGL) (multiplicity : FGL) :
    Eval.eval
      (Environment.fromArray
        ((imageColumns positive image).materialize index.val #[multiplicity]) data)
      (varFromOffset (F := FGL) RomRow 0) =
      { message := image index, multiplicity := multiplicity } := by
  simpa using eval_materialize positive image index data #[multiplicity]

/-- Integration contract: balance supplies raw tuple equality; image ownership
then supplies consumer membership. This is not an accepted-trace premise. -/
theorem consumer_member_of_counterpart {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) (index : Fin capacity)
    (data : ProverData FGL) (raw : Array FGL)
    (consumerEnv : Environment FGL)
    (consumer : ZiskRomMessage (Expression FGL))
    (h_msg :
      (((ZiskRomBusChannel.emitted
        (varFromOffset (F := FGL) RomRow 0).multiplicity
        (varFromOffset (F := FGL) RomRow 0).message).toRaw).eval
          (Environment.fromArray
            ((imageColumns positive image).materialize index.val raw) data)).msg =
      (((ZiskRomBusChannel.pulled consumer).toRaw).eval consumerEnv).msg) :
    (romStaticTable capacity image).Spec (Eval.eval consumerEnv consumer) := by
  let providerEnv := Environment.fromArray
    ((imageColumns positive image).materialize index.val raw) data
  have h_vec :
      Vector.map (Expression.eval providerEnv)
        (toElements (varFromOffset (F := FGL) RomRow 0).message) =
      Vector.map (Expression.eval consumerEnv) (toElements consumer) := by
    apply Vector.toArray_injective
    simpa [providerEnv, ChannelInteraction.toRaw, AbstractInteraction.eval] using h_msg
  have h_typed := congrArg
    (fun xs => (fromElements xs : ZiskRomMessage FGL)) h_vec
  have h_eq :
      Eval.eval providerEnv (varFromOffset (F := FGL) RomRow 0).message =
      Eval.eval consumerEnv consumer := by
    simpa [ProvableType.fromElements_eval_toElements] using h_typed
  have h_member := materialized_member positive image index data raw
  have h_project :
      Eval.eval providerEnv (varFromOffset (F := FGL) RomRow 0).message =
      (Eval.eval providerEnv (varFromOffset (F := FGL) RomRow 0)).message := by
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      instProvableStructRomRow, ProvableStruct.eval.go]
  rw [← h_eq, h_project]
  exact h_member

/-- The physical witness, not a unit selector, supplies the provider weight. -/
theorem materialized_multiplicity {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) (index : Fin capacity)
    (data : ProverData FGL) (raw : Array FGL) :
    (((ZiskRomBusChannel.emitted
      (varFromOffset (F := FGL) RomRow 0).multiplicity
      (varFromOffset (F := FGL) RomRow 0).message).toRaw).eval
        (Environment.fromArray
          ((imageColumns positive image).materialize index.val raw) data)).mult =
      raw.getD 0 0 := by
  simp only [AbstractInteraction.eval, Channel.emitted, ChannelInteraction.toRaw, emitted]
  have h := congrArg RomRow.multiplicity (eval_materialize positive image index data raw)
  simpa only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    instProvableStructRomRow, ProvableStruct.eval.go, CircuitType.eval_var_field] using h

/-- A full physical ROM table is constructible for every multiplicity vector.
Only multiplicities are raw witness data. The standalone table is not claimed
to be balanced: the actual Main consumers must supply its counterparts. -/
def providerTable {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) (multiplicities : Fin capacity → FGL)
    (data : ProverData FGL) : Air.Flat.Table FGL where
  component := component positive image
  rawRows := List.ofFn fun index => #[multiplicities index]
  data := data
  raw_uniform_width := by
    intro row h_row
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp h_row
    rfl
  fixed_domain := by
    intro columns h_columns
    have h_eq : columns = imageColumns positive image := by
      simpa only [component, Option.some.injEq] using h_columns.symm
    subst columns
    simp [imageColumns]

@[simp] theorem providerTable_length {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) (multiplicities : Fin capacity → FGL)
    (data : ProverData FGL) :
    (providerTable positive image multiplicities data).length = capacity := by
  simp [Air.Flat.Table.length, providerTable]

/- Integration controls required before any source-fidelity claim:
* Use a freshly produced pilout from the pinned production compiler and actual
  ZisK PIL, then this dedicated renderer and the named local source theorems.
* Swap `a_imm1` and `b_offset_imm0` in Rom's actual `lookup_proves` tuple:
  `lookupTuple_sourceOfImage` and `polynomial_0_sourceOfImage` must reject the
  regenerated source, not merely a hand-mutated model.
* Negate the actual provider's `mul: multiplicity` expression: the regenerated
  `multiplicity_sourceOfImage` and `polynomial_0_sourceOfImage` must reject it.
* Change the actual lowering's c0 update/sign while retaining its hint:
  `polynomial_0_sourceOfImage` must reject the regenerated constraint. The exact
  pinned standard-lookup producer path must be selected by the integration gate.
* Retain a fresh unchanged production baseline and a harmless formatting/comment
  control. A producer/compiler failure is not a kernel correspondence kill;
  record the exact failing phase. No mutation checks are run by this module.

This provider is not inserted or finished by the live ensemble in this packet.
Main's existing `RomWiring` ties its c42 tuple to an internal static lookup; that
does not establish a live ROM-channel pull. Actual provider classification,
channel finishing, public-root authentication, and final-producer-row/history
realization remain unproved. Local materialization tests or model-only mutations
are useful diagnostics, not substitutes for the production controls above.
-/

end ZiskFv.AirsClean.ZiskInstructionRomProvider
