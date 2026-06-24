import ZiskFv.Completeness.Rv64im

/-!
# Root completeness

The headline completeness statement of the project, parallel to
`ZiskFv.Soundness` / `ZiskFv.Compliance`.  This is the actual RV completeness
composition (decode-support → lowering → row materialization + soundness
input), specialized to the RV64IM decode domain.
-/

namespace ZiskFv.Completeness

open ZiskFv.Completeness.Rv64im

/-- Public RV64IM completeness theorem.

Sail is the source of valid raw instructions.  For every Sail-executable
RV64IM raw word, outside explicitly known ZisK decode gaps, the production
ZisK decode/lower/materialize path covers the instruction and provides the
row-local soundness input expected by the opcode soundness theorems. -/
theorem root_completeness
    (iface : Rv.Interface)
    (h_sail_subset : SailExecutableContainedInSupportedDecode iface)
    (h_supported : SupportedDecodeAvoidKnownDecodeBugs iface)
    (h_lower : Rv.Interface.LoweringComplete iface)
    (h_rows : Rv.Interface.RowMaterializationComplete iface)
    (h_opcode : Rv.Interface.OpcodeCoverageComplete iface)
    (h_soundness : SupportedDecodeSoundnessInputComplete iface) :
    Rv64imCompletenessWithSoundnessInputAvoidingKnownDecodeBugs iface := by
  intro raw h_sail h_not_decode_gap
  have h_shape := h_sail_subset raw h_sail
  have h_decode := h_supported raw h_shape h_sail h_not_decode_gap
  have h_lowerable := h_lower raw h_decode
  exact
    ⟨⟨h_decode,
        h_lowerable,
        h_rows raw h_lowerable,
        h_opcode raw h_decode⟩,
      h_soundness raw h_shape h_lowerable⟩

end ZiskFv.Completeness
