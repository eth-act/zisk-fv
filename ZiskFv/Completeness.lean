import ZiskFv.Completeness.Rv64im

/-!
# Root completeness

The headline completeness statement of the project, factored out of the
RV64IM completeness development for visibility.  It sits parallel to
`ZiskFv.Soundness` / `ZiskFv.Compliance` and re-exports the single endpoint
theorem.
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
    Rv64imCompletenessWithSoundnessInputAvoidingKnownDecodeBugs iface :=
  rv64im_global_completeness_with_soundness_input_avoiding_known_decode_bugs
    iface
    h_sail_subset
    h_supported
    h_lower
    h_rows
    h_opcode
    h_soundness

end ZiskFv.Completeness
