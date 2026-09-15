# Remove `InputsAgreeCore` from `root_soundness` (#360)

Issue: https://github.com/eth-act/zisk-fv/issues/360

## Goal

Remove the per-step `InputsAgreeCore` premise from `root_soundness`.
Retain only explicit boot, platform, trust, and defect premises.

## Existing subissues

- [x] #330: register simulation.
- [x] #76: reduce the load memory premise.
- [ ] #172: connect Sail decode to the committed raw program.
- [ ] #184: classify every remaining premise and its proof source.
- [ ] #353: exercise the generated Sail trace beyond index zero.

#343 remains nested under #330.
#115, #119, and #141 retain their existing parent relationships.

## Program phases

- [ ] Complete #184 and replace estimates with measured field classes.
- [ ] Construct pure inputs and prove decode agreement.
- [ ] Derive ALU and arithmetic provider witnesses.
- [ ] Complete memory provider composition and memory simulation.
- [ ] Prove the required Sail state invariants and execution conditions.
- [ ] Collapse the 63 operation bundles into derived facts.
- [ ] Remove `InputsAgreeCore` from the root theorem.
- [ ] Pass all build, trust, and repository gates.

## Scope rule

Do not reopen or expand #330.
Do not replace `InputsAgreeCore` with an equivalent aggregate premise.
