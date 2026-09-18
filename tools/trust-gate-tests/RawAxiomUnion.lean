import TrustGate.AxiomClosure
import ZiskFv

/-! Regression checks for the extraction gate's shared-closure fast path.
The negative cases inspect existing environment declarations; they introduce
no axioms, admitted proofs, or new compiled-certificate tactics. -/

open Lean
open TrustGate.AxiomClosure

run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let cases : Array (Array Name × Bool) := #[
    (#[`Nat.add_comm, `List.append_assoc], true),
    (#[`Classical.choice, `propext, `Quot.sound, `Nat.add_comm, `Classical.choice], true),
    (#[`sorryAx], false),
    (#[`Nat.add_comm, `sorryAx, `sorryAx], false),
    (#[`Lean.ofReduceBool], false),
    (#[`Lean.trustCompiler], false)]
  for (roots, expected) in cases do
    for root in roots do
      unless (env.find? root).isSome do
        throwError "raw-closure fixture is absent: {root}"
    let union := rawAxiomUnion env roots
    let individual := roots.flatMap (rawAxiomDepsForTheorem env)
    let individual := individual.toList.eraseDups.toArray.qsort
      (fun a b => a.toString < b.toString)
    unless union == individual do
      throwError "shared traversal differs from independent closures for {roots}"
    unless union.all allowed.contains == expected do
      throwError "wrong raw-closure acceptance for {roots}: {union}"
