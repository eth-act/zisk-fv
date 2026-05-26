import Mathlib

import ZiskFv.Airs.OperationBus.Consolidated

/-!
# OperationBus per-provider specializations (retired in T4-purge P6)

The previous `op_bus_perm_sound_{BinaryAdd, Binary, BinaryExtension}`
theorems specialized the `op_bus_permutation_sound` axiom to specific
providers. Both the axiom and these specializations were retired in
T4-purge: all global theorem opcode routes now use row-explicit
static-lookup paths (Clean ensemble + static BinaryTable/
BinaryExtensionTable membership) instead of the bus-level permutation
axiom.

This file is preserved as a placeholder for the historical narrative
in case future axioms need re-introducing for new providers.
-/

namespace ZiskFv.Airs.OperationBus

open Goldilocks

-- All per-provider permutation-soundness theorems deleted in T4-purge P6.
-- The underlying `op_bus_permutation_sound` axiom is also retired.

end ZiskFv.Airs.OperationBus
