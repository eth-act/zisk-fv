/-!
RV completeness: raw instruction word.

The live remnant of the old RV completeness interface — just the raw instruction
type, used by `Shapes` and the Sail containment proof. The abstract
`Rv.Interface` composition machinery that used to live here has moved to
`ZiskFv/Completeness/Aspirational/Interface.lean` (quarantined; see that
directory's `README.md`).
-/

namespace ZiskFv.Completeness.Rv

/-- Raw 32-bit instruction word. Kept as `BitVec 32` to match Sail decoding. -/
abbrev RawInstruction := BitVec 32

end ZiskFv.Completeness.Rv
