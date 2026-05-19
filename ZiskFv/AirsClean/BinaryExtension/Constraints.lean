import ZiskFv.AirsClean.BinaryExtension.Spec
import Clean.Circuit.Basic

/-!
# BinaryExtension circuit operations

Empty `main` — BinaryExtension has zero F-typed per-row constraints.
All semantic content is enforced by the BinaryExtensionTable lookup
channel, which is composed at the Component-instantiation level
(not in `main`'s `assertZero` body).

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks

/-- No-op circuit — BinaryExtension is entirely lookup-based. -/
@[circuit_norm]
def main (_row : Var BinaryExtensionRow FGL) : Circuit FGL Unit := pure ()

end ZiskFv.AirsClean.BinaryExtension
