import ZiskFv.Channels.OperationBus
import Clean.Air.FlatEnsemble
import Clean.Circuit

/-!
The verifier's public input is the whole production vector: four ROM-root
cells followed by the 64 cells called `inputs` in `zisk.pil`.  This is not an
AIR table with unconstrained rows.  The verifier runs once and emits exactly
one positive unit operation-bus interaction per public 64-bit word.

`PublicIoSource` pins this independently written model to the compiled GLOBAL
constraint, including its cleared-denominator numerator sign.
-/
namespace ZiskFv.AirsClean.PublicIo

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus

abbrev PublicIO := fields 68
abbrev WordIndex := Fin 32
abbrev CellIndex := Fin 64

/-- The same vector must supply both ROM authentication and public outputs. -/
def romRootCell {F : Type} (publicIO : PublicIO F) (i : Fin 4) : F :=
  publicIO[i.val]

def inputCell {F : Type} (publicIO : PublicIO F) (i : CellIndex) : F :=
  publicIO[4 + i.val]

def lowCell (i : WordIndex) : CellIndex := ⟨2 * i.val, by omega⟩
def highCell (i : WordIndex) : CellIndex := ⟨2 * i.val + 1, by omega⟩

/-- The 11 slots, including the duplicate b/c limbs and all four zero-tail
slots.  No 32-bit range claim is introduced for an arbitrary public field. -/
def message (publicIO : PublicIO FGL) (i : WordIndex) : OpBusMessage FGL where
  op := 48
  a_lo := i.val
  a_hi := 0
  b_lo := inputCell publicIO (lowCell i)
  b_hi := inputCell publicIO (highCell i)
  c_lo := inputCell publicIO (lowCell i)
  c_hi := inputCell publicIO (highCell i)
  flag := 0
  main_step := 0
  extended_arg := 0
  extra_args_0 := 0

def messageExpr (publicIO : Var PublicIO FGL) (i : WordIndex) :
    OpBusMessage (Expression FGL) where
  op := 48
  a_lo := Expression.const (i.val : FGL)
  a_hi := 0
  b_lo := inputCell publicIO (lowCell i)
  b_hi := inputCell publicIO (highCell i)
  c_lo := inputCell publicIO (lowCell i)
  c_hi := inputCell publicIO (highCell i)
  flag := 0
  main_step := 0
  extended_arg := 0
  extra_args_0 := 0

theorem eval_messageExpr (env : Environment FGL) (publicIO : Var PublicIO FGL)
    (i : WordIndex) :
    eval env (messageExpr publicIO i) = message (eval env publicIO) i := by
  rw [OpBusMessage.mk.injEq]
  simp [messageExpr, message, inputCell, circuit_norm,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents]

@[circuit_norm]
def main (publicIO : Var PublicIO FGL) : Circuit FGL Unit := do
  let _ ← .mapFinRange 32 fun i => OpBusChannel.push (messageExpr publicIO i)

/-- A real zero-witness Clean verifier circuit, not `GeneralFormalCircuit.empty`.
Its local spec is trivial because the binding is a *balanced-world* property,
not a consequence of the (currently trivial) channel guarantee. -/
def verifier : GeneralFormalCircuit FGL PublicIO unit where
  name := "ZiskPublicIo"
  main := main
  channelsWithRequirements := [OpBusChannel.toRaw]
  exposedChannels publicIO _ := expose OpBusChannel
    ((List.finRange 32).map fun i => OpBusChannel.pushed (messageExpr publicIO i))
  exposedChannels_eq := by
    intro publicIO offset
    simp only [main, circuit_norm]
    rw [Operations.interactionsWith, Circuit.interactions_mapFinRange]
    simp [circuit_norm, List.ofFn_eq_map, List.map_map, Function.comp_def]
    rfl
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start [main, messageExpr, OpBusChannel]
  completeness := by
    circuit_proof_start [main, messageExpr, OpBusChannel]

theorem verifier_length_zero (publicIO : Var PublicIO FGL) :
    verifier.localLength publicIO = 0 := by
  simp [verifier, main, circuit_norm]

/-- Concrete typed-message encoding used by the balance lemmas below. -/
def interaction (mult : FGL) (msg : OpBusMessage FGL) : Interaction FGL where
  channel := OpBusChannel.toRaw
  mult := mult
  msg := (toElements msg).toArray
  same_size := by simp [OpBusChannel, Channel.toRaw]
  assumeGuarantees := false

set_option maxHeartbeats 1000000 in
@[simp] theorem interaction_opcode (mult : FGL) (msg : OpBusMessage FGL) :
    (interaction mult msg).msg[0]? = some msg.op := by
  simp [interaction, explicit_provable_type, circuit_norm]
  change ((#v[msg.op] ++ _) : Vector FGL 11)[(0 : Nat)] = msg.op
  rw [Vector.getElem_append_left (by decide)]
  rfl

/-- This finite list is a verifier computation, never caller-supplied rows. -/
def interactions (publicIO : PublicIO FGL) : List (Interaction FGL) :=
  (List.finRange 32).map fun i => interaction 1 (message publicIO i)

@[simp] theorem interactions_length (publicIO : PublicIO FGL) :
    (interactions publicIO).length = 32 := by simp [interactions]

@[simp] theorem mem_interactions (publicIO : PublicIO FGL) (i : WordIndex) :
    interaction 1 (message publicIO i) ∈ interactions publicIO := by
  simp [interactions]

theorem interaction_message_injective {m n : OpBusMessage FGL} {a b : FGL}
    (h : (interaction a m).msg = (interaction b n).msg) : m = n := by
  have hvec : toElements m = toElements n := Vector.toArray_injective h
  have := congrArg (fun v => (fromElements v : OpBusMessage FGL)) hvec
  simpa only [ProvableType.fromElements_toElements] using this

theorem index_cast_injective {i j : WordIndex}
    (h : (i.val : FGL) = (j.val : FGL)) : i = j := by
  have hval := congrArg (fun x : FGL => x.val) h
  have hi : i.val < GL_prime := by omega
  have hj : j.val < GL_prime := by omega
  have hnat : i.val = j.val := by
    simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hval
  exact Fin.ext hnat

/-- Different source indices cannot collide even if every output word is equal. -/
theorem message_index_injective (publicIO : PublicIO FGL) :
    Function.Injective (message publicIO) := by
  intro i j h
  exact index_cast_injective (congrArg OpBusMessage.a_lo h)

/-- All source verifier emissions occur once, with multiplicity +1. -/
theorem interactions_nodup (publicIO : PublicIO FGL) :
    (interactions publicIO).Nodup := by
  apply List.Nodup.map _ (List.nodup_finRange 32)
  intro i j h
  apply message_index_injective publicIO
  exact interaction_message_injective (congrArg Interaction.msg h)

/-- Project the precise per-index public binding, without losing the duplicate
result lanes, flag, or the three remaining fixed-zero lanes. -/
theorem binding_of_message_eq (publicIO : PublicIO FGL) (i : WordIndex)
    (mainMessage : OpBusMessage FGL) (h : mainMessage = message publicIO i) :
    mainMessage.op = 48 ∧ mainMessage.a_lo = (i.val : FGL) ∧ mainMessage.a_hi = 0 ∧
    mainMessage.b_lo = inputCell publicIO (lowCell i) ∧
    mainMessage.b_hi = inputCell publicIO (highCell i) ∧
    mainMessage.c_lo = inputCell publicIO (lowCell i) ∧
    mainMessage.c_hi = inputCell publicIO (highCell i) ∧
    mainMessage.flag = 0 ∧ mainMessage.main_step = 0 ∧
    mainMessage.extended_arg = 0 ∧ mainMessage.extra_args_0 = 0 := by
  subst mainMessage
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Source-aware partition theorem for the integration boundary. `mainRows`
contains only the real Main -1/0 interactions; `otherProviders` must have its
opcode exclusion *proved from each actual provider's constraints*. These are
local algebraic inputs, not new AcceptedTrace or root certificates.

Balance produces the tuple equality: it is not a premise. The sole positive
producer capable of matching opcode 48 is the concrete verifier list above.
The ensemble owner must instantiate the two classification facts, not expose
them as arbitrary caller promises. -/
theorem binding_of_balanced_partition
    (publicIO : PublicIO FGL)
    (mainRows otherProviders : List (Interaction FGL))
    (h_main : ∀ r ∈ mainRows, r.mult = -1 ∨ r.mult = 0)
    (h_other : ∀ r ∈ otherProviders, r.msg[0]? ≠ some (48 : FGL))
    (h_balance : BalancedInteractions
      (mainRows ++ interactions publicIO ++ otherProviders))
    (mainMessage : OpBusMessage FGL)
    (h_op : mainMessage.op = 48)
    (h_row : interaction (-1) mainMessage ∈ mainRows) :
    ∃ i : WordIndex, mainMessage = message publicIO i := by
  have h_mem : interaction (-1) mainMessage ∈
      mainRows ++ interactions publicIO ++ otherProviders := by
    simp only [List.mem_append]
    exact Or.inl (Or.inl h_row)
  obtain ⟨provider, h_provider, h_msg, h_nonzero, h_nonpull⟩ :=
    exists_push_of_pull _ h_balance _ h_mem rfl
  simp only [List.mem_append] at h_provider
  rcases h_provider with (h_provider | h_provider) | h_provider
  · rcases h_main provider h_provider with h | h
    · exact False.elim (h_nonpull h)
    · exact False.elim (h_nonzero h)
  · obtain ⟨i, _, h_eq⟩ := List.mem_map.mp h_provider
    subst provider
    exact ⟨i, (interaction_message_injective h_msg).symm⟩
  · exfalso
    apply h_other provider h_provider
    rw [h_msg]
    simpa only [interaction_opcode] using congrArg some h_op

/-- Pin a source index after balance, rather than ask for a tuple equality. -/
theorem binding_at_index_of_balanced_partition
    (publicIO : PublicIO FGL)
    (mainRows otherProviders : List (Interaction FGL))
    (h_main : ∀ r ∈ mainRows, r.mult = -1 ∨ r.mult = 0)
    (h_other : ∀ r ∈ otherProviders, r.msg[0]? ≠ some (48 : FGL))
    (h_balance : BalancedInteractions
      (mainRows ++ interactions publicIO ++ otherProviders))
    (mainMessage : OpBusMessage FGL)
    (h_op : mainMessage.op = 48)
    (h_row : interaction (-1) mainMessage ∈ mainRows)
    (i : WordIndex) (h_index : mainMessage.a_lo = (i.val : FGL)) :
    mainMessage = message publicIO i := by
  obtain ⟨j, hj⟩ := binding_of_balanced_partition publicIO mainRows otherProviders
    h_main h_other h_balance mainMessage h_op h_row
  have hji : j = i := index_cast_injective
    ((congrArg OpBusMessage.a_lo hj).symm.trans h_index)
  simpa only [hji] using hj

/-- Component view of the actual verifier, for existing Clean table lemmas. -/
def verifierComponent : Component FGL := { circuit := verifier, rawWidth := 68 }

/-- Only the source operation channel is emitted. Empty projections on the
other seven channels follow from actual operations, not global erasure. -/
theorem verifierComponent_interactionsWith_nil_of_ne (channel : RawChannel FGL)
    (hne : channel ≠ OpBusChannel.toRaw) :
    verifierComponent.operations.interactionsWith channel = [] := by
  rw [Component.interactionsWith_eq]
  change ((main (varFromOffset PublicIO 0)).operations (size PublicIO)).interactionsWith
    channel = []
  simp only [main, circuit_norm]
  rw [Operations.interactionsWith, Circuit.interactions_mapFinRange]
  simp [circuit_norm, hne, Ne.symm hne]

theorem verifierComponent_interactionsWith_opBus :
    verifierComponent.operations.interactionsWith OpBusChannel.toRaw =
      (List.finRange 32).map (fun i =>
        (OpBusChannel.pushed (messageExpr verifierComponent.rowInputVar i)).toRaw) := by
  apply Component.interactionsWith_of_exposedChannels
  simp only [verifierComponent, Component.exposedChannels, verifier, expose,
    List.mem_singleton, List.map_map, Function.comp_def]

theorem eval_pushed_messageExpr (env : Environment FGL)
    (publicIO : Var PublicIO FGL) (i : WordIndex) :
    ((OpBusChannel.pushed (messageExpr publicIO i)).toRaw).eval env =
      interaction 1 (message (eval env publicIO) i) := by
  rw [Channel.eval_pushed, eval_messageExpr]
  rfl

theorem verifierComponent_interactionValuesWith (env : Environment FGL) :
    verifierComponent.operations.interactionValuesWith OpBusChannel.toRaw env =
      interactions (eval env verifierComponent.rowInputVar) := by
  rw [Operations.interactionValuesWith_eq_map,
    verifierComponent_interactionsWith_opBus]
  simp only [List.map_map, interactions]
  apply List.map_congr_left
  intro i _
  exact eval_pushed_messageExpr env verifierComponent.rowInputVar i

/-- Every real verifier interaction has opcode 48, including on an arbitrary
component row. Ordinary provider classification must prove disjointness,
not discard these nonempty interactions. -/
theorem verifierComponent_interaction_opcode {table : Table FGL}
    (hc : table.component = verifierComponent) {r : Interaction FGL}
    (hr : r ∈ table.interactionsWith OpBusChannel.toRaw) :
    r.msg[0]? = some (48 : FGL) := by
  simp only [Table.interactionsWith, hc, verifierComponent_interactionValuesWith] at hr
  obtain ⟨row, _, hr⟩ := List.mem_flatMap.mp hr
  simp only [interactions] at hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  simp [interaction_opcode, message]

theorem interaction_message_eq_iff {m n : OpBusMessage FGL} {a b : FGL} :
    (interaction a m).msg = (interaction b n).msg ↔ m = n :=
  ⟨interaction_message_injective, by rintro rfl; rfl⟩

/-- The balance contribution is exactly +1 for each source index, not merely
nonzero or an unconstrained field-valued multiplicity. -/
theorem interactions_balanceOf (publicIO : PublicIO FGL) (i : WordIndex) :
    balanceOf (interactions publicIO) (interaction 1 (message publicIO i)).msg = 1 := by
  have h_mult : ∀ r ∈ interactions publicIO, r.mult = (1 : FGL) := by
    intro r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    rfl
  have h_count :
      (interactions publicIO).countP
        (·.msg = (interaction 1 (message publicIO i)).msg) = 1 := by
    simp only [interactions, List.countP_map, Function.comp_def,
      interaction_message_eq_iff, (message_index_injective publicIO).eq_iff]
    simpa only [List.count, Bool.beq_eq_decide_eq] using List.count_finRange i
  rw [balanceOf_eq_of_const_mult' h_mult, h_count]
  simp

/-- Exact per-index Main signed multiplicity follows from the actual finite
global contribution and exclusion of non-PUBOUT providers. -/
theorem main_balance_per_index
    (publicIO : PublicIO FGL)
    (mainRows otherProviders : List (Interaction FGL))
    (h_other : ∀ r ∈ otherProviders, r.msg[0]? ≠ some (48 : FGL))
    (h_balance : BalancedInteractions
      (mainRows ++ interactions publicIO ++ otherProviders))
    (i : WordIndex) :
    balanceOf mainRows (interaction 1 (message publicIO i)).msg = -1 := by
  have h_other_zero :
      balanceOf otherProviders (interaction 1 (message publicIO i)).msg = 0 := by
    have h := balanceOf_eq_of_const_mult (interactions := otherProviders)
      (msg := (interaction 1 (message publicIO i)).msg) (mult := (0 : FGL))
      (by
        intro r hr hmsg
        exfalso
        apply h_other r hr
        rw [hmsg, interaction_opcode]
        rfl)
    simpa only [zero_mul] using h
  have h := h_balance.2 (interaction 1 (message publicIO i)).msg
  simp only [balanceOf_append, interactions_balanceOf, h_other_zero, add_zero] at h
  linear_combination h

/-- Conversely, balance requires a genuine active Main counterpart at every
source-defined public index; it does not assume an epilogue row count. -/
theorem exists_active_main_at_each_index
    (publicIO : PublicIO FGL)
    (mainRows otherProviders : List (Interaction FGL))
    (h_main : ∀ r ∈ mainRows, r.mult = -1 ∨ r.mult = 0)
    (h_other : ∀ r ∈ otherProviders, r.msg[0]? ≠ some (48 : FGL))
    (h_balance : BalancedInteractions
      (mainRows ++ interactions publicIO ++ otherProviders))
    (i : WordIndex) :
    ∃ r ∈ mainRows, r.msg = (interaction 1 (message publicIO i)).msg ∧ r.mult = -1 := by
  have h_index := main_balance_per_index publicIO mainRows otherProviders
    h_other h_balance i
  by_contra h_none
  have h_zero : balanceOf mainRows (interaction 1 (message publicIO i)).msg = 0 := by
    have h := balanceOf_eq_of_const_mult (interactions := mainRows)
      (msg := (interaction 1 (message publicIO i)).msg) (mult := (0 : FGL))
      (by
        intro r hr hmsg
        rcases h_main r hr with h_neg | h_zero
        · exact False.elim (h_none ⟨r, hr, hmsg, h_neg⟩)
        · exact h_zero)
    simpa only [zero_mul] using h
  rw [h_zero] at h_index
  exact neg_ne_zero.mpr (one_ne_zero : (1 : FGL) ≠ 0) h_index.symm

/-- Minimal additive ensemble constructor. This deliberately returns an
`Ensemble`, not a `SoundEnsemble` with a false `verifier_empty` field.
The shared owner must re-establish ordered-channel table soundness with the
real globals included in balance. Tables and channel identities are unchanged. -/
def withVerifier (ens : Ensemble FGL PublicIO) : Ensemble FGL PublicIO :=
  { ens with
    verifier := verifier
    verifier_length_zero := verifier_length_zero }

@[simp] theorem withVerifier_tables (ens : Ensemble FGL PublicIO) :
    (withVerifier ens).tables = ens.tables := rfl

@[simp] theorem withVerifier_channels (ens : Ensemble FGL PublicIO) :
    (withVerifier ens).channels = ens.channels := rfl

/-- Clean's verifier table has exactly one row, populated from the actual
public input. Its concrete interactions are the finite source-indexed list,
not a separately supplied table or a correspondence certificate. -/
theorem withVerifier_verifierTable_interactionsWith
    (ens : Ensemble FGL PublicIO) (witness : EnsembleWitness (withVerifier ens)) :
    witness.verifierTable.interactionsWith OpBusChannel.toRaw =
      interactions witness.publicInput := by
  simp only [Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
    EnsembleWitness.verifierTable_environment]
  change verifierComponent.operations.interactionValuesWith OpBusChannel.toRaw
    (Environment.fromInput witness.publicInput witness.data) = interactions witness.publicInput
  rw [verifierComponent_interactionValuesWith]
  change interactions (eval (Environment.fromInput witness.publicInput witness.data)
    (varFromOffset PublicIO 0)) = interactions witness.publicInput
  rw [ProvableType.eval_fromInput_varFromOffset_zero]

/-- Exact full-world operation-bus delta for the ensemble owner. In particular,
the old `interactionsWith_of_verifier_empty` equation is no longer valid. -/
theorem withVerifier_interactionsWith
    (ens : Ensemble FGL PublicIO) (witness : EnsembleWitness (withVerifier ens)) :
    witness.interactionsWith OpBusChannel.toRaw =
      interactions witness.publicInput ++
        witness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw) := by
  change witness.verifierTable.interactionsWith OpBusChannel.toRaw ++
    witness.tables.flatMap (·.interactionsWith OpBusChannel.toRaw) = _
  rw [withVerifier_verifierTable_interactionsWith]

end ZiskFv.AirsClean.PublicIo
