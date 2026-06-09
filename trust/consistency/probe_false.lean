import ZiskFv.ZiskCircuit.MemModel

namespace ZiskFv.TrustConsistency

open Goldilocks
open Interaction
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.MemBridge
open ZiskFv.ZiskCircuit.MemModel
open ZiskFv.Channels.MemoryBusBytes (byteAt)

private def probeMem : Valid_Mem FGL FGL where
  addr := fun _ => 0
  step := fun _ => 0
  sel := fun _ => 1
  addr_changes := fun _ => 0
  step_dual := fun _ => 0
  sel_dual := fun _ => 0
  value_0 := fun _ => 0
  value_1 := fun _ => 0
  wr := fun _ => 0
  previous_step := fun _ => 0
  increment_0 := fun _ => 0
  increment_1 := fun _ => 0
  read_same_addr := fun _ => 0
  gsum := fun _ => 0
  im_0 := fun _ => 0
  im_1 := fun _ => 0

private def probeEntry : MemoryBusEntry FGL where
  multiplicity := -1
  as := 2
  ptr := 0
  value_0 := 0
  value_1 := 0
  timestamp := 0

private theorem probe_match : mem_row_matches_entry probeMem 0 probeEntry := by
  simp [probeMem, probeEntry, mem_row_matches_entry, entry_packs_mem_row_value,
    memory_entry_lo, memory_entry_hi]

private theorem probe_wr : probeMem.wr 0 = 0 := by
  rfl

private theorem false_from_row_models_sail_state_load : False := by
  let state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource := default
  have h := row_models_sail_state_load probeMem 0 probeEntry state probe_match probe_wr
  have hmem : state.mem[probeEntry.ptr.toNat]? = none := by
    native_decide
  cases hmem.symm.trans h.1

#print axioms false_from_row_models_sail_state_load

end ZiskFv.TrustConsistency
