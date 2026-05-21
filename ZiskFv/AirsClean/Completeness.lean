import ZiskFv.AirsClean.BinaryAdd.Constraints
import ZiskFv.AirsClean.MemAlignByte.Constraints
import ZiskFv.AirsClean.MemAlignReadByte.Constraints
import ZiskFv.AirsClean.ArithMul.Constraints

/-!
# Clean Component completeness axioms (non-security-critical trust class)

Clean's `GeneralFormalCircuit` makes `completeness` a mandatory field.
zisk-fv is a **soundness-only** verification — it does not claim, and the
pre-Clean code never established, completeness (that an honest prover can
satisfy the constraints). Per plan decision D-COMPLETE, each AIR's Component
`completeness` field is filled by a declared axiom, and all such axioms are
collected here in this one allowlisted file.

These axioms are **completeness-direction**: a falsehood in one cannot make
a wrong execution verify — the verification's *soundness* does not depend on
them. They form a distinct, declared trust class, kept here so the trust
ledger shows them plainly and separately from the soundness-critical axioms.

## Trust note

Axioms here: `binaryAdd_circuit_completeness`, `memAlignByte_circuit_completeness`,
`memAlignReadByte_circuit_completeness`, `arithMul_circuit_completeness`,
`arithDiv_circuit_completeness` (one more per AIR as the epic proceeds).
Trust class: "Clean-Component completeness (non-security-critical)" — see
`docs/fv/trusted-base.md`.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks

/-- **BinaryAdd Component completeness** (plan decision D-COMPLETE).
    Declared, not proved — zisk-fv is soundness-only. Completeness-direction:
    the verification's soundness does not depend on this axiom. -/
axiom binaryAdd_circuit_completeness :
    GeneralFormalCircuit.Completeness FGL binaryAddElaborated
      (fun _ _ _ => True) (fun _ _ _ => True)

end ZiskFv.AirsClean.BinaryAdd

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks

/-- **MemAlignByte Component completeness** (plan decision D-COMPLETE).
    Declared, not proved — zisk-fv is soundness-only. Completeness-direction:
    the verification's soundness does not depend on this axiom. -/
axiom memAlignByte_circuit_completeness :
    GeneralFormalCircuit.Completeness FGL memAlignByteElaborated
      (fun _ _ _ => True) (fun _ _ _ => True)

end ZiskFv.AirsClean.MemAlignByte

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks

/-- **MemAlignReadByte Component completeness** (plan decision D-COMPLETE).
    Declared, not proved — zisk-fv is soundness-only. Completeness-direction:
    the verification's soundness does not depend on this axiom. -/
axiom memAlignReadByte_circuit_completeness :
    GeneralFormalCircuit.Completeness FGL memAlignReadByteElaborated
      (fun _ _ _ => True) (fun _ _ _ => True)

end ZiskFv.AirsClean.MemAlignReadByte

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks

/-- **ArithMul Component completeness** (plan decision D-COMPLETE).
    Declared, not proved — zisk-fv is soundness-only. Completeness-direction:
    the verification's soundness does not depend on this axiom. -/
axiom arithMul_circuit_completeness :
    GeneralFormalCircuit.Completeness FGL arithMulElaborated
      (fun _ _ _ => True) (fun _ _ _ => True)

end ZiskFv.AirsClean.ArithMul
