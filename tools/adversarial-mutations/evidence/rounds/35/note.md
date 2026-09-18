`is_precompiled` selects "this row dispatches to a precompile". Deleting its
booleanity lets a prover set it to any field element, so the gate between the
ordinary RV64IM path and the precompile path stops being a boolean choice.
