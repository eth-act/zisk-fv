Active plan: docs/ai/plan/PLAN_CI_RUNTIME.md.

Current focus: speed up `proofs` CI after run 27457939944 reached ~2.5h.
Diagnosis: top-level setup/cache/populate is not the bottleneck; `nix run
.#test` spent 2h22m56s, mostly Aeneas production extraction (~1h34m) plus
`lake build` (~41m). Historical runs show Aeneas is a stable fixed cost and
Lake grew after the Clean completeness waves.

Blocking: none. Memory is not currently the limiter for the successful run
(~9.1GiB max kernel used on 16GiB L runner, `LEAN_NUM_THREADS=4`).

Approach: keep local `nix run .#test` as the full all-in-one gate, but let CI
skip the Aeneas subcheck in the Lake job while a parallel Aeneas job runs the
same full production extraction check and caches its temporary Lake artifacts.

Next step: push/open PR for `ci/proofs-parallel-aeneas`, then compare the first
split `proofs` run wall time against run 27457939944.
