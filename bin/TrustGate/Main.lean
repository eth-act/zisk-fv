/-
TrustGate.Main — entry point for the V2 trust gate Lake executable.

Subcommands:
  regenerate-deps              Print per-theorem axiom-dep baseline to stdout.
  check-deps PATH              Compare regenerated baseline against PATH.
  check-no-output-eq-v2 PATH   Type-walk; fail on forbidden Names from PATH.
  all                          Run check-deps + check-no-output-eq-v2 against
                               trust/baseline-equiv-axiom-deps.txt and
                               trust/forbidden-types.txt.

Run AFTER `lake build` (consumes oleans).
-/
/-
NOTE: We deliberately do NOT `import ZiskFv` at compile time. Doing so
would force Lake to native-compile every Sail/* module's C export
(~30+ min on cold cache, since the auto-generated Sail Lean code
produces multi-MB C files compiled at -O3). The exe loads ZiskFv
purely at runtime via `withImportModules`; Lake sets `LEAN_PATH` so
the olean is found.
-/
import Lean
import TrustGate.CanonicalTheorems
import TrustGate.AxiomClosure
import TrustGate.TypeWalk

open Lean

namespace TrustGate

/-- Run a `MetaM` action against a frozen environment. -/
def runMeta {α} (env : Environment) (x : Meta.MetaM α) : IO α := do
  let coreCtx : Core.Context := { fileName := "<trust-gate>", fileMap := default }
  let coreState : Core.State := { env := env }
  let (a, _, _) ← x.toIO coreCtx coreState
  return a

/-- Render the per-theorem axiom-dep baseline as a single string. -/
def renderDepsBaseline (env : Environment) : String := Id.run do
  let canonical := CanonicalTheorems.findCanonical env
  let mut lines : Array String := #[]
  for n in canonical do
    let deps := AxiomClosure.axiomDepsForTheorem env n
    let depsStr := String.intercalate ", " (deps.map (·.toString)).toList
    lines := lines.push s!"{n}: {depsStr}"
  String.intercalate "\n" lines.toList ++ "\n"

/-- Parse `trust/forbidden-types.txt` (one fully-qualified Name per line;
`#` comments and blank lines ignored). -/
def loadForbiddenTypes (path : System.FilePath) : IO NameSet := do
  let content ← IO.FS.readFile path
  let mut s : NameSet := {}
  for raw in content.splitOn "\n" do
    let line := raw.trim
    if line.isEmpty || line.startsWith "#" then continue
    s := s.insert line.toName
  return s

/-- Naive line-by-line diff. Returns nonzero when contents differ. -/
def diffStrings (regenerated committed : String) : IO UInt32 := do
  if regenerated == committed then
    IO.println "trust-gate (V2): per-theorem axiom-dep baseline matches."
    return 0
  IO.eprintln "trust-gate (V2): per-theorem axiom-dep baseline DIFFERS."
  IO.eprintln "  Run `lake exe trust-gate regenerate-deps > trust/baseline-equiv-axiom-deps.txt`"
  IO.eprintln "  and review the diff before committing."
  let r := regenerated.splitOn "\n"
  let c := committed.splitOn "\n"
  let mut shown := 0
  let total := max r.length c.length
  for i in [0:total] do
    if shown >= 80 then break
    let rl := r[i]?.getD ""
    let cl := c[i]?.getD ""
    if rl != cl then
      if !cl.isEmpty then IO.eprintln s!"-{cl}"
      if !rl.isEmpty then IO.eprintln s!"+{rl}"
      shown := shown + 1
  return 1

/-- Execute the type-walk against `forbidden`; returns 0 on clean run. -/
def runTypeWalk (env : Environment) (forbidden : NameSet) : IO UInt32 := do
  let canonical := CanonicalTheorems.findCanonical env
  let mut totalViols : Nat := 0
  for n in canonical do
    let viols ← runMeta env (TypeWalk.checkTheorem forbidden n)
    for v in viols do
      totalViols := totalViols + 1
      let hits := String.intercalate ", " (v.hits.map (·.toString)).toList
      IO.eprintln s!"  {n} binder #{v.binderIdx} :: forbidden Name(s): {hits}"
      IO.eprintln s!"    type: {v.binderType}"
  if totalViols == 0 then
    IO.println s!"trust-gate (V2): no forbidden types in {canonical.size} canonical equiv_<OP> theorem(s)."
    return 0
  IO.eprintln s!"trust-gate (V2): {totalViols} forbidden-type hit(s) — FAIL."
  return 1

def usage : IO Unit := do
  IO.println "Usage: trust-gate <subcommand>"
  IO.println "  regenerate-deps                regen baseline → stdout"
  IO.println "  check-deps PATH                compare against PATH"
  IO.println "  check-no-output-eq-v2 PATH     type-walk against forbidden-Names PATH"
  IO.println "  all                            check-deps + check-no-output-eq-v2 against trust/* defaults"

def dispatch (env : Environment) (args : List String) : IO UInt32 := do
  match args with
  | ["regenerate-deps"] =>
    IO.print (renderDepsBaseline env)
    return 0
  | ["check-deps", path] =>
    let baseline ← IO.FS.readFile path
    diffStrings (renderDepsBaseline env) baseline
  | ["check-no-output-eq-v2", path] =>
    let forbidden ← loadForbiddenTypes path
    runTypeWalk env forbidden
  | ["all"] =>
    let baseline ← IO.FS.readFile "trust/baseline-equiv-axiom-deps.txt"
    let r1 ← diffStrings (renderDepsBaseline env) baseline
    let forbidden ← loadForbiddenTypes "trust/forbidden-types.txt"
    let r2 ← runTypeWalk env forbidden
    return (if r1 == 0 && r2 == 0 then 0 else 1)
  | _ =>
    usage
    return 1

end TrustGate

unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.withImportModules #[{ module := `ZiskFv }] {}
      (fun env => TrustGate.dispatch env args)
