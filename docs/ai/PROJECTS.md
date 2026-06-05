# Memory Axiom

Retire `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load` by replacing it with explicit trace-indexed memory agreement for selected Mem provider rows. The active implementation first introduces byte-address row matching and a Sail memory agreement predicate, then threads that evidence through load witnesses and regenerates trust ledgers. The remaining risk is proving or supplying whole-trace agreement from accepted Mem trace constraints rather than reintroducing a source axiom.
