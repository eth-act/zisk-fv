Active plan: docs/ai/plan/PLAN_ENDGAME_P4_CLOSEOUT.md (§5 PR2, rework-off-#97).

Branch `p4-closeout-construction` off `origin/endgame-p4-pr2` (#97 @ 6c414ffa).

Focus: EXECUTE PR2 — strip the P4 relabel, keep the salvage + via_binaryadd
route, add the first honest sound construction (`construction_sub_sound`, 17 +
execRow residual binders). End in a CLEAN do-not-merge PR superseding #94/#97.

Done:
- Stripped AcceptedTrace.lean to the salvage (AcceptedTrace + ProgramBinding
  skeleton + Layer-A provider-match wrappers). Removed ArmTag, 37 *RowBinding
  structs, per-op ProgramBinding projections, all construction_<op> defs +
  aeneasBridgeTrust theorems, the 28 exists_construction_*_from_balance wrappers.
- Stripped the 4 addViaBinaryAdd*OfExtractedShape decls (AeneasBridgeTrust.lean).
- Stripped the print-construction-binders subcommand (TrustGate/Main.lean), the
  blind check-construction-theorem-binders.sh + its baseline + its wiring in
  check-all-semantic.sh / regenerate.sh / README.md.
- KEPT the via_binaryadd salvage route (OpEnvelope arms, Dispatch, EquivCore/Add,
  BinaryAdd circuit, route ledger).
- Added ConstructionSub.lean (sound construction_sub_sound).

Next: lake build green -> check-all.sh / check-all-semantic.sh -> commit -> push
-> PR.

Blocking: (none yet; awaiting build result).
