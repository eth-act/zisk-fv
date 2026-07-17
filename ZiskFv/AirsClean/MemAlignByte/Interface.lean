import ZiskFv.AirsClean.MemAlignByte.Circuit

/-!
# MemAlignByte consumer interface and Q2 audit

The nine legacy predicates map in order to the nine `assertZero` operations
in `MemAlignByte.main`: selector booleanity (three), composed-value identity,
`is_write` booleanity, written-composed identity, the two memory-write lane
identities, and the bus-byte identity.  The legacy bits declarations map to
the direct Clean lookups for `bus_byte : bits(8)`, `byte_value : bits(8)`, and
`is_write : bits(1)`.  The legacy memory-bus interaction maps to
`MemBusChannel.push (memBusMessageExpr row)`.  There is no divergence.

**Verified deletion blocker:** `AirsClean/MemAlignByte/Bridge.lean` remains
load-bearing in `EquivCore/Lbu.lean`, `Lhu.lean`, and `Lwu.lean`, where its
`RangeLookupWitness` projects accepted-trace lookup evidence to byte range
facts.  Those witnesses are assembled through the shared data-memory trace
surface (`Compliance/SharedBundles.lean` and
`ZiskCircuit/LoadDerivation.lean`), which this slice forbids changing.
Accordingly the bridge and legacy model survive until the data-memory family
is migrated; no caller obligation was added.
-/
