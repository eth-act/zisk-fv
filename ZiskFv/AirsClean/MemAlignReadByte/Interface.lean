import ZiskFv.AirsClean.MemAlignReadByte.Circuit

/-!
# MemAlignReadByte consumer interface and Q2 audit

The four legacy predicates map in order to the four `assertZero` operations
in `MemAlignReadByte.main`: three selector-boolean constraints and the
composed-value identity.  The legacy byte bits declaration maps to the direct
`rangeTable8` lookup for `byte_value`; its memory-bus interaction maps to
`MemBusChannel.push (memBusMessageExpr row)`.  There is no divergence.

**Verified deletion blocker:** `AirsClean/MemAlignReadByte/Bridge.lean`
remains load-bearing in `EquivCore/Lbu.lean`, `Lhu.lean`, and `Lwu.lean` for
`RangeLookupWitness` and `byte_value_in_range_via_component`.  Their witness
construction is coupled to the out-of-scope data-memory accepted-trace layer
in `Compliance/SharedBundles.lean` and `ZiskCircuit/LoadDerivation.lean`.
The bridge and legacy model therefore survive; no caller obligation was
added.
-/
