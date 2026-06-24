/-
TrustGate.Main — entry point for the V2 trust gate Lake executable.

Subcommands:
  regenerate-deps              Print per-theorem axiom-dep baseline to stdout.
  check-deps PATH              Compare regenerated baseline against PATH.
  check-no-output-eq-v2 PATH   Type-walk; fail on forbidden Names from PATH.
  print-global-binders         Print global theorem binder baseline rows.
  all                          Run check-deps + check-no-output-eq-v2 against
                               trust/generated/baseline-equiv-axiom-deps.txt and
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
import TrustGate.ConstantClosure

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
    let line := if depsStr.isEmpty then s!"{n}:" else s!"{n}: {depsStr}"
    lines := lines.push line
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
  IO.eprintln "  Run `lake exe trust-gate regenerate-deps > trust/generated/baseline-equiv-axiom-deps.txt`"
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

/-- Collapse pretty-printer whitespace so generated baselines keep one row per
binder even when the type is too wide for the default formatter. (Re-exported
from `TrustGate.TypeWalk`, where the deep renderer also uses it.) -/
def normalizeWhitespace (s : String) : String :=
  TypeWalk.normalizeWhitespace s

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

/-- Parse an entry-points file (one fully-qualified Name per line;
`#` comments and blank lines ignored). -/
def loadEntryPoints (path : System.FilePath) : IO (List Name) := do
  let content ← IO.FS.readFile path
  let mut out : Array Name := #[]
  for raw in content.splitOn "\n" do
    let line := raw.trim
    if line.isEmpty || line.startsWith "#" then continue
    out := out.push line.toName
  return out.toList

/-- Report missing entry-point Names (so a typo in the config fails
loudly instead of silently shrinking the reachable set). -/
def warnMissingEntries (env : Environment) (entries : List Name) : IO Unit := do
  let missing := entries.filter (fun n => (env.find? n).isNone)
  if !missing.isEmpty then
    IO.eprintln s!"WARNING: {missing.length} entry-point name(s) not found in environment:"
    for n in missing do
      IO.eprintln s!"  - {n}"

/-- Subcommand: print every `ZiskFv.*` constant reachable from the
entry-points file, sorted. -/
def cmdPrintReachable (env : Environment) (path : String) : IO UInt32 := do
  let entries ← loadEntryPoints path
  warnMissingEntries env entries
  let reach := ConstantClosure.transitiveClosure env entries
  let proj := reach.toList.filter ConstantClosure.isAuditable
  let sorted := proj.toArray.qsort (fun a b => a.toString < b.toString)
  for n in sorted do
    IO.println n.toString
  return 0

/-- Parse a `trust/generated/baseline-axioms.txt` line. The file is whitespace-
separated columns: `<hash>  <file>:<line>  <kind>  <name>`. We only
need the last column (the unqualified axiom name). Lines starting
with `#` and blank lines are skipped. -/
def loadBaselineAxioms (path : System.FilePath) : IO (Array String) := do
  let content ← IO.FS.readFile path
  let mut out : Array String := #[]
  for raw in content.splitOn "\n" do
    let line := raw.trim
    if line.isEmpty || line.startsWith "#" then continue
    -- Take the last whitespace-separated token.
    let parts := line.splitToList (·.isWhitespace) |>.filter (!·.isEmpty)
    if let some last := parts.getLast? then
      out := out.push last
  return out

/-- Load one-axiom-name-per-line file (#-comments and blank lines ignored).
    Used by the V2 gate's tolerated non-closure allowlist: source trust
    declarations that the soundness proof intentionally does not reach but
    which still live in the source tree for a documented local/legacy or
    completeness-only surface. -/
def loadAxiomList (path : System.FilePath) : IO (Array String) := do
  if !(← System.FilePath.pathExists path) then return #[]
  let content ← IO.FS.readFile path
  let mut out : Array String := #[]
  for raw in content.splitOn "\n" do
    let line := raw.trim
    if line.isEmpty || line.startsWith "#" then continue
    out := out.push line
  return out

/-- Subcommand: check that the project-axiom closure of
`zisk_riscv_compliant_program_bus` exactly matches the unqualified
names in `trust/generated/baseline-axioms.txt`, modulo the tolerated
non-closure allowlist at `trust/tolerated-completeness-axioms.txt`. Catches the
kind of drift that the per-theorem `equiv_<OP>` axiom-dep baseline
cannot see — i.e., axioms that survive in the trust ledger but are
no longer reachable from the uber-theorem (dead trust) AND aren't
explicitly tolerated as documented non-global trust. -/
def cmdCheckClosureVsBaseline (env : Environment) (path : String)
    (theoremName : Name) : IO UInt32 := do
  if (env.find? theoremName).isNone then
    IO.eprintln s!"trust-gate: unknown const {theoremName}"
    return 1
  -- Project-axiom closure (qualified). Strip to last component to
  -- match the baseline format.
  let depsQualified := AxiomClosure.axiomDepsForTheorem env theoremName
  let closureLast : Array String :=
    depsQualified.map (fun n => n.componentsRev.head!.toString)
  let baselineLast ← loadBaselineAxioms path
  let tolerated ← loadAxiomList "trust/tolerated-completeness-axioms.txt"
  let toleratedSet : Std.HashSet String := tolerated.foldl (·.insert ·) {}
  let closureSet : Std.HashSet String := closureLast.foldl (·.insert ·) {}
  let baselineSet : Std.HashSet String := baselineLast.foldl (·.insert ·) {}
  let mut missingFromBaseline : Array String := #[]
  let mut missingFromClosure : Array String := #[]
  for n in closureLast do
    if !baselineSet.contains n then
      missingFromBaseline := missingFromBaseline.push n
  for n in baselineLast do
    if !closureSet.contains n && !toleratedSet.contains n then
      missingFromClosure := missingFromClosure.push n
  let missingFromBaselineSorted := missingFromBaseline.qsort (· < ·)
  let missingFromClosureSorted := missingFromClosure.qsort (· < ·)
  if missingFromBaselineSorted.isEmpty && missingFromClosureSorted.isEmpty then
    IO.println s!"trust-gate (V2): uber-theorem axiom closure matches generated/baseline-axioms.txt modulo tolerated non-closure axioms ({closureLast.size} names)."
    return 0
  IO.eprintln "trust-gate (V2): uber-theorem axiom closure DIVERGES from generated/baseline-axioms.txt."
  IO.eprintln s!"  Theorem:   {theoremName}"
  IO.eprintln s!"  Baseline:  {path}"
  IO.eprintln s!"  Closure:   {closureLast.size} names"
  IO.eprintln s!"  Baseline:  {baselineLast.size} names"
  IO.eprintln ""
  if !missingFromBaselineSorted.isEmpty then
    IO.eprintln s!"  In closure but NOT in baseline ({missingFromBaselineSorted.size}) — baseline is missing audited axioms:"
    for n in missingFromBaselineSorted do
      IO.eprintln s!"    + {n}"
  if !missingFromClosureSorted.isEmpty then
    IO.eprintln s!"  In baseline but NOT in closure ({missingFromClosureSorted.size}) — dead axioms in ledger:"
    for n in missingFromClosureSorted do
      IO.eprintln s!"    - {n}"
  IO.eprintln ""
  IO.eprintln "  After confirming the diff is intentional, regenerate the baseline:"
  IO.eprintln "    trust/scripts/regenerate.sh"
  IO.eprintln "  and review (CODEOWNER required for ledger changes)."
  return 1

/-- Subcommand: render the global theorem's elaborated binder list. This is a
baseline-only audit surface; it does not apply policy or forbidden-name checks. -/
def cmdPrintGlobalBinders (env : Environment) (theoremName : Name) : IO UInt32 := do
  if (env.find? theoremName).isNone then
    IO.eprintln s!"trust-gate: unknown const {theoremName}"
    return 1
  let rows ← runMeta env (TypeWalk.renderTheoremBinders theoremName)
  for r in rows do
    IO.println s!"{r.binderIdx} :: {r.binderName} :: {normalizeWhitespace r.binderType}"
  return 0

/-- The strengthened trace-level export theorem (#61, channel-balance form).
Audited by the strong-export closure + binder gates exactly as
`zisk_riscv_compliant_program_bus` is audited by `check-closure-vs-baseline` /
`check-global-theorem-binders`. -/
def strongExportTheorem : Name :=
  `ZiskFv.Compliance.root_soundness

/-- Subcommand: check that the `ZiskFv.*` project-axiom closure of the strong
trace-level export theorem exactly matches the fully-qualified Names committed in
`trust/generated/baseline-strong-export-closure.txt`. This mirrors
`check-closure-vs-baseline` for the new public theorem: any silent change to its
project-trust footprint (additions OR removals) fails the gate. The expectation
is an EMPTY closure (0 `ZiskFv.*` axioms), identical to the old global theorem. -/
def cmdCheckStrongExportClosure (env : Environment) (path : String) : IO UInt32 := do
  if (env.find? strongExportTheorem).isNone then
    IO.eprintln s!"trust-gate: unknown const {strongExportTheorem}"
    return 1
  -- Live closure (fully-qualified ZiskFv.* axiom Names, sorted).
  let live := AxiomClosure.axiomDepsForTheorem env strongExportTheorem
  let liveStrs := live.map (·.toString)
  -- Committed baseline: one fully-qualified Name per non-comment line.
  let content ← IO.FS.readFile path
  let mut baseline : Array String := #[]
  for raw in content.splitOn "\n" do
    let line := raw.trim
    if line.isEmpty || line.startsWith "#" then continue
    baseline := baseline.push line
  let baselineSorted := baseline.qsort (· < ·)
  if liveStrs == baselineSorted then
    IO.println s!"trust-gate (V2): strong-export axiom closure matches baseline ({liveStrs.size} ZiskFv.* axiom(s))."
    return 0
  IO.eprintln "trust-gate (V2): strong-export axiom closure DIVERGES from baseline."
  IO.eprintln s!"  Theorem:  {strongExportTheorem}"
  IO.eprintln s!"  Baseline: {path}"
  IO.eprintln s!"  Live:     {liveStrs.size} ZiskFv.* axiom(s); Baseline: {baselineSorted.size}"
  let liveSet : Std.HashSet String := liveStrs.foldl (·.insert ·) {}
  let baseSet : Std.HashSet String := baselineSorted.foldl (·.insert ·) {}
  for n in liveStrs do
    if !baseSet.contains n then IO.eprintln s!"    + {n}  (in closure, NOT in baseline)"
  for n in baselineSorted do
    if !liveSet.contains n then IO.eprintln s!"    - {n}  (in baseline, NOT in closure)"
  IO.eprintln ""
  IO.eprintln "  After confirming the diff is intentional, regenerate the baseline:"
  IO.eprintln "    trust/scripts/regenerate.sh"
  return 1

/-- Subcommand: check the strong export theorem's binder list against its committed
baseline AND walk every binder type for forbidden Names. This mirrors
`check-global-theorem-binders` + the canonical `check-no-output-eq-v2` walk, but
targets the new public theorem so its `rowData` / `h_known_bugs` premise surface is
a visible, drift-protected audit surface. The first arg is the binder baseline; the
second is the forbidden-Names file (reused from the canonical gate). -/
def cmdCheckStrongExportBinders (env : Environment) (baselinePath : String)
    (forbiddenPath : String) : IO UInt32 := do
  if (env.find? strongExportTheorem).isNone then
    IO.eprintln s!"trust-gate: unknown const {strongExportTheorem}"
    return 1
  -- 1. Binder baseline drift.
  let rows ← runMeta env (TypeWalk.renderTheoremBinders strongExportTheorem)
  let regen := String.intercalate "\n"
    (rows.map (fun r => s!"{r.binderIdx} :: {r.binderName} :: {normalizeWhitespace r.binderType}")).toList
    ++ "\n"
  let committed ← IO.FS.readFile baselinePath
  let mut rc : UInt32 := 0
  if regen == committed then
    IO.println "trust-gate (V2): strong-export binder baseline matches."
  else
    IO.eprintln "trust-gate (V2): strong-export binder baseline DIFFERS."
    IO.eprintln s!"  Run: lake exe trust-gate print-strong-export-binders > {baselinePath}"
    IO.eprintln "  and review the diff before committing."
    let r := regen.splitOn "\n"
    let c := committed.splitOn "\n"
    let total := max r.length c.length
    for i in [0:total] do
      let rl := r[i]?.getD ""
      let cl := c[i]?.getD ""
      if rl != cl then
        if !cl.isEmpty then IO.eprintln s!"-{cl}"
        if !rl.isEmpty then IO.eprintln s!"+{rl}"
    rc := 1
  -- 2. Forbidden-type walk over the strong export theorem's binders.
  let forbidden ← loadForbiddenTypes forbiddenPath
  let viols ← runMeta env (TypeWalk.checkTheorem forbidden strongExportTheorem)
  if viols.isEmpty then
    IO.println s!"trust-gate (V2): no forbidden types in {strongExportTheorem} binders."
  else
    for v in viols do
      let hits := String.intercalate ", " (v.hits.map (·.toString)).toList
      IO.eprintln s!"  {strongExportTheorem} binder #{v.binderIdx} :: forbidden Name(s): {hits}"
      IO.eprintln s!"    type: {v.binderType}"
    rc := 1
  return rc

/-- Subcommand: enumerate every auditable `ZiskFv.*` const, subtract
the reachable set, print the unreachable ones grouped by module. -/
def cmdFindUnused (env : Environment) (path : String) : IO UInt32 := do
  let entries ← loadEntryPoints path
  warnMissingEntries env entries
  let reach := ConstantClosure.transitiveClosure env entries
  let all := ConstantClosure.allAuditableProjectConsts env
  -- Group unreachable by module.
  let mut byModule : Std.HashMap String (Array Name) := {}
  let mut unreachableCount := 0
  for n in all do
    if !reach.contains n then
      unreachableCount := unreachableCount + 1
      let m := ConstantClosure.moduleOf env n
      byModule := byModule.insert m ((byModule.getD m #[]).push n)
  let modules := byModule.toList.toArray.qsort (fun a b => a.1 < b.1)
  IO.println s!"# unreachable `ZiskFv.*` constants: {unreachableCount}"
  IO.println s!"# total auditable `ZiskFv.*` constants: {all.size}"
  IO.println s!"# entry points: {entries.length}"
  IO.println ""
  for (m, names) in modules do
    IO.println s!"## {m} ({names.size})"
    let sorted := names.qsort (fun a b => a.toString < b.toString)
    for n in sorted do
      let kindStr :=
        match env.find? n with
        | some (.thmInfo _)   => "theorem"
        | some (.defnInfo _)  => "def    "
        | some (.axiomInfo _) => "axiom  "
        | some (.opaqueInfo _) => "opaque "
        | some (.ctorInfo _)  => "ctor   "
        | some (.inductInfo _) => "induct "
        | some (.recInfo _)   => "rec    "
        | some (.quotInfo _)  => "quot   "
        | _                   => "???    "
      IO.println s!"  {kindStr}  {n.toString}"
    IO.println ""
  return 0

/-- Subcommand: emit the proof-tree edge list as TSV. Each row is
`parent\tchild\tparentKind\tchildKind` where kind ∈ {P,A,E}
(project / axiom / external). Suitable for a static-page graph
visualizer. -/
def cmdPrintTreeEdges (env : Environment) (rootStr : String) : IO UInt32 := do
  let root := rootStr.toName
  if (env.find? root).isNone then
    IO.eprintln s!"trust-gate: unknown const {rootStr}"
    return 1
  let edges := ConstantClosure.collectEdges env root
  IO.println "parent\tchild\tparent_kind\tchild_kind"
  for (p, c, pk, ck) in edges do
    IO.println s!"{p}\t{c}\t{pk.toTag}\t{ck.toTag}"
  return 0

def usage : IO Unit := do
  IO.println "Usage: trust-gate <subcommand>"
  IO.println "  regenerate-deps                regen axiom-dep baseline → stdout"
  IO.println "  check-deps PATH                compare against PATH"
  IO.println "  check-no-output-eq-v2 PATH     type-walk against forbidden-Names PATH"
  IO.println "  all                            check-deps + check-no-output-eq-v2 against trust/* defaults"
  IO.println "  print-axiom-closure NAME       print transitive ZiskFv-namespace axioms reachable from NAME"
  IO.println "  print-reachable PATH           print every ZiskFv.* const reachable from entry-points in PATH"
  IO.println "  find-unused PATH               enumerate ZiskFv.* consts not reachable from PATH entry points"
  IO.println "  check-closure-vs-baseline PATH check zisk_riscv_compliant_program_bus axiom closure == generated/baseline-axioms.txt"
  IO.println "  print-global-binders           print zisk_riscv_compliant_program_bus binder baseline rows"
  IO.println "  print-strong-export-closure    print strong export theorem ZiskFv.* axiom closure"
  IO.println "  print-strong-export-binders    print strong export theorem binder baseline rows"
  IO.println "  check-strong-export-closure PATH  check strong export theorem ZiskFv.* axiom closure == PATH"
  IO.println "  check-strong-export-binders BASELINE FORBIDDEN  check strong export binder baseline + forbidden-type walk"
  IO.println "  print-tree-edges NAME          emit TSV edge list (parent→child) for proof-tree visualizer"

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
  | ["print-axiom-closure", nameStr] =>
    let n := nameStr.toName
    if (env.find? n).isNone then
      IO.eprintln s!"unknown const: {nameStr}"
      return 1
    let deps := AxiomClosure.axiomDepsForTheorem env n
    for d in deps do IO.println d.toString
    return 0
  | ["print-reachable", path] => cmdPrintReachable env path
  | ["find-unused", path]     => cmdFindUnused env path
  | ["print-tree-edges", name] => cmdPrintTreeEdges env name
  | ["check-closure-vs-baseline", path] =>
    cmdCheckClosureVsBaseline env path
      `ZiskFv.Compliance.zisk_riscv_compliant_program_bus
  | ["print-global-binders"] =>
    cmdPrintGlobalBinders env
      `ZiskFv.Compliance.zisk_riscv_compliant_program_bus
  | ["print-strong-export-closure"] =>
    -- Print the strong export theorem's ZiskFv.* axiom closure (the audit body
    -- of trust/generated/baseline-strong-export-closure.txt).
    let deps := AxiomClosure.axiomDepsForTheorem env strongExportTheorem
    for d in deps do IO.println d.toString
    return 0
  | ["print-strong-export-binders"] =>
    cmdPrintGlobalBinders env strongExportTheorem
  | ["check-strong-export-closure", path] =>
    cmdCheckStrongExportClosure env path
  | ["check-strong-export-binders", baselinePath, forbiddenPath] =>
    cmdCheckStrongExportBinders env baselinePath forbiddenPath
  | ["all"] =>
    let baseline ← IO.FS.readFile "trust/generated/baseline-equiv-axiom-deps.txt"
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
