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

DONE: lake build green (8681 jobs); check-all.sh 18/18; check-all-semantic.sh
12/12; 0 PROJECT axioms (construction_sub_sound closure empty); 17 + execRow
honest binders; net diff vs main has 0 relabel decls. Committed 9b55bcdb, pushed,
opened do-not-merge PR #99 (eth-act/zisk-fv, base main) superseding #94/#97.

DONE (recursive gate, Option X): re-added the DEEP construction-binder gate.
TypeWalk.lean renderTheoremBindersDeep + renderDeep (descend only into ZiskFv.*
project structures; library structures are leaves; visited-set cycle guard).
Main.lean print-construction-binders-deep targeting construction_sub_sound.
check-construction-theorem-binders.sh re-added (points at -deep), re-wired into
check-all-semantic.sh (5/12) + regenerate.sh + README. Deep baseline = 17 flat
h_ residual lines + execRow; ZERO RowBinding/MainRowProvenance substrings; setup
binders (trace/binding) descend into honest trace structure only. nix run .#test
green. Committed 0e25550d, pushed to update PR #99.

DONE (PR3 — second sound family, AND, logic route): added
ConstructionAnd.lean (`construction_and_sound`), the mechanical mirror of
`construction_sub_sound` for the logic family. Op-bus match via the salvaged
logic Layer-A wrapper `exists_staticBinary_provider_row_matches_logic_from_binding`
(op pin via `Or.inl h_main_op`); OP_AND (=14, <16) byte-chain path
(`logic_row_mode_pins_of_emit_op_lt_16_of_static_spec` + `BinaryTable.OP_AND`);
data effect concluded via `equiv_AND` (`execute_RTYPE_and_pure`, bottoms in
`binary_and_chunks_eq_bv_and_of_wf`). Same 17 + execRow residual budget, flat
top-level binders, no `*RowBinding`/`MainRowProvenance` leaf. Generalized the
recursive gate: `soundConstructionTheorems` list + labelled-block deep render
in TrustGate/Main.lean (adding a family = append to the list + regen). Deep
baseline grew 34→71 lines = +2 headers + 1 blank + 34 honest AND binders; SUB
block byte-identical. lake build green (8682 jobs); check-all.sh 18/18;
check-all-semantic.sh 12/12 (deep check now covers both); 0 PROJECT
(ZiskFv.*) axioms (construction_and_sound closure empty of ZiskFv.* names);
nix run .#test green.

Next (follow-up increments, NOT this PR): the remaining ALU/sweep families;
close stale #94/#97 on merge (Cody's call).

Blocking: none.
