import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.AirsClean.BinaryExtension.Bridge

/-!
# BinaryExtension static lookup adapters

T7 removes this module's old range-bus column-bound derivations. The remaining
helpers are structural adapters from the Clean static BinaryExtension-table
witness to the legacy row-byte lookup bundles used by signed-load bridges.
-/

namespace ZiskFv.Airs.BinaryExtension

open Goldilocks
open ZiskFv.Airs.Tables.BinaryExtensionTable

theorem binary_extension_row_byte_lookup_wfs_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v) :
    ByteLookupWfHypotheses (binary_extension_row_byte_lookups v r) := by
  have h_wfs := ZiskFv.AirsClean.BinaryExtension.static_lookup_wf_facts
    v r offset env h_static
  simpa [binary_extension_row_byte_lookups,
    ZiskFv.AirsClean.BinaryExtension.rowAt,
    ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using h_wfs

open ZiskFv.Trusted in
theorem binary_extension_op_is_shift_pin_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v) :
    ((v.op r = ZiskFv.Trusted.OP_SLL ∨ v.op r = ZiskFv.Trusted.OP_SRL ∨ v.op r = ZiskFv.Trusted.OP_SRA
      ∨ v.op r = ZiskFv.Trusted.OP_SLL_W ∨ v.op r = ZiskFv.Trusted.OP_SRL_W ∨ v.op r = ZiskFv.Trusted.OP_SRA_W)
        → v.op_is_shift r = 1)
  ∧ ((v.op r = ZiskFv.Trusted.OP_SIGNEXTEND_B ∨ v.op r = ZiskFv.Trusted.OP_SIGNEXTEND_H ∨ v.op r = ZiskFv.Trusted.OP_SIGNEXTEND_W)
        → v.op_is_shift r = 0) := by
  have h_wfs := binary_extension_row_byte_lookup_wfs_of_static_lookup
    v r offset env h_static
  exact binary_extension_op_is_shift_pin_of_wf_hypotheses v r h_wfs

open ZiskFv.Trusted in
lemma op_is_shift_zero_SIGNEXTEND_B_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = ZiskFv.Trusted.OP_SIGNEXTEND_B) :
    v.op_is_shift r = 0 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).2
    (Or.inl h_op)

open ZiskFv.Trusted in
lemma op_is_shift_zero_SIGNEXTEND_H_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = ZiskFv.Trusted.OP_SIGNEXTEND_H) :
    v.op_is_shift r = 0 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).2
    (Or.inr (Or.inl h_op))

open ZiskFv.Trusted in
lemma op_is_shift_zero_SIGNEXTEND_W_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = ZiskFv.Trusted.OP_SIGNEXTEND_W) :
    v.op_is_shift r = 0 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).2
    (Or.inr (Or.inr h_op))

end ZiskFv.Airs.BinaryExtension
