import ZiskFv.Compliance.AeneasBridgeTrust.Base
import ZiskFv.Compliance.AeneasBridgeTrust.Branches
import ZiskFv.Compliance.AeneasBridgeTrust.ControlAndUType
import ZiskFv.Compliance.AeneasBridgeTrust.Stores
import ZiskFv.Compliance.AeneasBridgeTrust.Loads
import ZiskFv.Compliance.AeneasBridgeTrust.Mul
import ZiskFv.Compliance.AeneasBridgeTrust.DivRem
import ZiskFv.Compliance.AeneasBridgeTrust.BinaryRType
import ZiskFv.Compliance.AeneasBridgeTrust.ImmediateAlu
import ZiskFv.Compliance.AeneasBridgeTrust.Shifts

/-!
# Aeneas bridge audit predicate

The main Lake proof does not yet import generated Aeneas Lean and derive every
row-provenance/source-lane field from the extracted production lowerer.  The
corresponding facts are carried by `OpEnvelope` constructors as ordinary proof
fields.  This file keeps the representative bridge predicate and
extracted-shape constructors available for audit and generated-row-shape
integration. The `aeneasBridgeTrust` predicate is deliberately explicit as a
global theorem hypothesis until generated Aeneas Lean is imported by main Lake
and proves these fields instead.

This module is a thin aggregator: the declarations have been split, verbatim,
into the sibling part files under `ZiskFv/Compliance/AeneasBridgeTrust/`,
grouped by opcode family. This file re-exports every part so consumers and
imports elsewhere are unaffected.
-/
