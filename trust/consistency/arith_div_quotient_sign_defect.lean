import ZiskFv.Regression.SignedDivOrdinaryCounterexample

/-!
# Signed-DIV quotient-sign defect repro — axiom-closure probe

`trust/defects.md` cites `ZiskFv.Regression.SignedDivOrdinaryCounterexample` as
the local evidence for `ZISK-DEFECT-ARITH-DIV-QUOTIENT-SIGN-SOUNDNESS` (the
`DIV(1, -1) = +1` forgery reproduced end-to-end in codygunton/zisk#12). This
probe gives that citation the same machine-checked standing the sibling
MemAlign narrow-load repro already has in
`trust/consistency/memalign_narrow_load_lane_defect.lean`: the named theorems
must exist, elaborate, and close over kernel axioms only.

`componentFullSpec` is the load-bearing one. It discharges
`componentComplete.Spec = FullSpec ∧ SharedDivBlockSpec`, i.e. the forged row is
accepted by the COMPLETED Arith component that the live ensemble validates — so
the defect survives #279's Div-block completion rather than being ruled out by
it, which is what makes the `arithDivQuotientSignSoundness` exclusion load-
bearing rather than over-broad.
-/

#print axioms ZiskFv.Regression.SignedDivOrdinaryCounterexample.sharedDivBlockSpec
#print axioms ZiskFv.Regression.SignedDivOrdinaryCounterexample.componentFullSpec
#print axioms ZiskFv.Regression.SignedDivOrdinaryCounterexample.componentConstraints
#print axioms ZiskFv.Regression.SignedDivOrdinaryCounterexample.outsideDivRemForge
#print axioms ZiskFv.Regression.SignedDivOrdinaryCounterexample.providerMessage
#print axioms ZiskFv.Regression.SignedDivOrdinaryCounterexample.physicalQuotient_ne_sail
